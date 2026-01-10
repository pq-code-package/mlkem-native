/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>

/* Expose declaration of allocator (normally internal) */
#define MLK_BUILD_INTERNAL
#include "../../mlkem/mlkem_native.h"
#include "../../mlkem/src/common.h"
#include "../notrandombytes/notrandombytes.h"

/*
 * Level-dependent allocation limit macros.
 * These expand to the right MLK_TOTAL_ALLOC_{512,768,1024}_* constant
 * based on MLK_CONFIG_API_PARAMETER_SET.
 */
#define MLK_TOTAL_ALLOC_KEYPAIR__(LVL) MLK_TOTAL_ALLOC_##LVL##_KEYPAIR
#define MLK_TOTAL_ALLOC_KEYPAIR_(LVL) MLK_TOTAL_ALLOC_KEYPAIR__(LVL)
#define MLK_TOTAL_ALLOC_KEYPAIR \
  MLK_TOTAL_ALLOC_KEYPAIR_(MLK_CONFIG_API_PARAMETER_SET)

#define MLK_TOTAL_ALLOC_ENCAPS__(LVL) MLK_TOTAL_ALLOC_##LVL##_ENCAPS
#define MLK_TOTAL_ALLOC_ENCAPS_(LVL) MLK_TOTAL_ALLOC_ENCAPS__(LVL)
#define MLK_TOTAL_ALLOC_ENCAPS \
  MLK_TOTAL_ALLOC_ENCAPS_(MLK_CONFIG_API_PARAMETER_SET)

#define MLK_TOTAL_ALLOC_DECAPS__(LVL) MLK_TOTAL_ALLOC_##LVL##_DECAPS
#define MLK_TOTAL_ALLOC_DECAPS_(LVL) MLK_TOTAL_ALLOC_DECAPS__(LVL)
#define MLK_TOTAL_ALLOC_DECAPS \
  MLK_TOTAL_ALLOC_DECAPS_(MLK_CONFIG_API_PARAMETER_SET)

#define MLK_TOTAL_ALLOC__(LVL) MLK_TOTAL_ALLOC_##LVL
#define MLK_TOTAL_ALLOC_(LVL) MLK_TOTAL_ALLOC__(LVL)
#define MLK_TOTAL_ALLOC MLK_TOTAL_ALLOC_(MLK_CONFIG_API_PARAMETER_SET)

/*
 * This test checks that
 * - we handle allocator failures correctly, propagating MLK_ERR_OUT_OF_MEMORY
 *   and cleaning up all memory, and
 * - we leak no memory, and
 * - we always de-allocate in the reverse order of allocation, thereby
 *   allowing the use of a bump allocator.
 *
 * This is done through a custom bump allocator and tracking of in-flight
 * allocations.
 */

/*
 * Allocation tracker
 *
 * Simple stack of in-flight allocations that's used to test that there are
 * no leaks and that we free in reverse order than we allocate. (The absence
 * of leaks is also checked through the address sanitizer)
 */

typedef struct
{
  void *addr;
  size_t size;
  const char *file;
  int line;
  const char *var;
  const char *type;
} alloc_info_t;

#define MLK_MAX_IN_FLIGHT_ALLOCS 100
static alloc_info_t alloc_stack[MLK_MAX_IN_FLIGHT_ALLOCS];
static int alloc_stack_top = 0;

static void alloc_tracker_push(void *addr, size_t size, const char *file,
                               int line, const char *var, const char *type)
{
  if (alloc_stack_top >= MLK_MAX_IN_FLIGHT_ALLOCS)
  {
    fprintf(stderr, "ERROR: Allocation stack overflow\n");
    exit(1);
  }
  alloc_stack[alloc_stack_top].addr = addr;
  alloc_stack[alloc_stack_top].size = size;
  alloc_stack[alloc_stack_top].file = file;
  alloc_stack[alloc_stack_top].line = line;
  alloc_stack[alloc_stack_top].var = var;
  alloc_stack[alloc_stack_top].type = type;
  alloc_stack_top++;
}

static void alloc_tracker_pop(void *addr, size_t size, const char *file,
                              int line, const char *var)
{
  alloc_info_t *top;
  if (alloc_stack_top == 0)
  {
    fprintf(
        stderr,
        "ERROR: Attempting to free %s at %s:%d but allocation stack is empty\n",
        var, file, line);
    exit(1);
  }

  top = &alloc_stack[alloc_stack_top - 1];
  if (top->addr != addr || top->size != size)
  {
    fprintf(stderr,
            "ERROR: Free order violation at %s:%d\n"
            "  Attempting to free: %s (addr=%p, sz %d)\n"
            "  Expected to free:   %s (addr=%p, sz %d) allocated at %s:%d\n",
            file, line, var, addr, (int)size, top->var, top->addr,
            (int)top->size, top->file, top->line);
    exit(1);
  }

  alloc_stack_top--;
}

/*
 * Bump allocator
 *
 * A simple stack-like allocator. We can use it since freeing happens in
 * reverse order to allocation.
 */

#define MLK_BUMP_ALLOC_SIZE (24 * 1024)  /* 24KB buffer */
static uint8_t *bump_buffer = NULL;      /* Base address */
static size_t bump_offset = 0;           /* Watermark */
static size_t bump_high_mark = 0;        /* High watermark */
static size_t global_bump_high_mark = 0; /* High watermark over all tests */
static size_t global_bump_high_mark_keypair =
    0;                                          /* High watermark for keypair */
static size_t global_bump_high_mark_encaps = 0; /* High watermark for encaps */
static size_t global_bump_high_mark_decaps = 0; /* High watermark for decaps */

static void *bump_alloc(size_t sz)
{
  /* Align to 32 bytes */
  size_t aligned_sz = (sz + 31) & ~((size_t)31);
  void *p;

  if (sz > MLK_BUMP_ALLOC_SIZE ||
      aligned_sz > MLK_BUMP_ALLOC_SIZE - bump_offset)
  {
    return NULL;
  }

  p = bump_buffer + bump_offset;
  bump_offset += aligned_sz;

  if (bump_offset > bump_high_mark)
  {
    bump_high_mark = bump_offset;
  }

  return p;
}

static int bump_free(void *p)
{
  if (p == NULL)
  {
    return 0;
  }

  /* Check that p is within the bump buffer */
  if (p < (void *)bump_buffer || p >= (void *)(bump_buffer + bump_offset))
  {
    return -1;
  }

  /* Reset bump offset to the freed address */
  bump_offset = (size_t)((uint8_t *)p - bump_buffer);
  return 0;
}

int alloc_counter = 0;
int fail_on_counter = -1;
int print_debug_info = 0;

static void reset_all(void)
{
  randombytes_reset();
  alloc_counter = 0;
  alloc_stack_top = 0;
  bump_offset = 0;
  fail_on_counter = -1;
}

void *custom_alloc(size_t sz, const char *file, int line, const char *var,
                   const char *type)
{
  void *p = NULL;
  if (alloc_counter++ == fail_on_counter)
  {
    return NULL;
  }

  p = bump_alloc(sz);
  if (p == NULL)
  {
    fprintf(stderr,
            "ERROR: Bump allocator (%d bytes) ran out of memory. "
            "%s *%s (%d bytes) at %s:%d\n",
            (int)MLK_BUMP_ALLOC_SIZE, type, var, (int)sz, file, line);
    exit(1);
  }

  alloc_tracker_push(p, sz, file, line, var, type);

  if (print_debug_info == 1)
  {
    fprintf(stderr, "Alloc #%d: %s %s (%d bytes) at %s:%d\n", alloc_counter + 1,
            type, var, (int)sz, file, line);
  }

  return p;
}

void custom_free(void *p, size_t sz, const char *file, int line,
                 const char *var, const char *type)
{
  (void)sz;
  (void)type;

  if (p != NULL)
  {
    alloc_tracker_pop(p, sz, file, line, var);
  }

  if (bump_free(p) != 0)
  {
    fprintf(stderr, "ERROR: Free failed: %s %s (%d bytes) at %s:%d\n", type,
            var, (int)sz, file, line);
    exit(1);
  }
}

#define TEST_ALLOC_FAILURE(test_name, call, alloc_limit, global_high_mark_ptr) \
  do                                                                           \
  {                                                                            \
    int num_allocs, i, rc;                                                     \
    /* First pass: count allocations */                                        \
    bump_high_mark = 0;                                                        \
    reset_all();                                                               \
    rc = call;                                                                 \
    if (rc != 0)                                                               \
    {                                                                          \
      fprintf(stderr, "ERROR: %s failed with %d in counting pass\n",           \
              test_name, rc);                                                  \
      return 1;                                                                \
    }                                                                          \
    if (alloc_stack_top != 0)                                                  \
    {                                                                          \
      fprintf(stderr, "ERROR: %s leaked %d allocation(s) in counting pass\n",  \
              test_name, alloc_stack_top);                                     \
      return 1;                                                                \
    }                                                                          \
    num_allocs = alloc_counter;                                                \
    /* Second pass: test each allocation failure */                            \
    for (i = 0; i < num_allocs; i++)                                           \
    {                                                                          \
      reset_all();                                                             \
      fail_on_counter = i;                                                     \
      rc = call;                                                               \
      if (rc != MLK_ERR_OUT_OF_MEMORY)                                         \
      {                                                                        \
        int rc2;                                                               \
        /* Re-run dry-run and print debug info */                              \
        print_debug_info = 1;                                                  \
        reset_all();                                                           \
        rc2 = call;                                                            \
        (void)rc2;                                                             \
        if (rc == 0)                                                           \
        {                                                                      \
          fprintf(stderr,                                                      \
                  "ERROR: %s unexpectedly succeeded when allocation %d/%d "    \
                  "was instrumented to fail\n",                                \
                  test_name, i + 1, num_allocs);                               \
        }                                                                      \
        else                                                                   \
        {                                                                      \
          fprintf(stderr,                                                      \
                  "ERROR: %s failed with wrong error code %d "                 \
                  "(expected %d) when allocation %d/%d was instrumented "      \
                  "to fail\n",                                                 \
                  test_name, rc, MLK_ERR_OUT_OF_MEMORY, i + 1, num_allocs);    \
        }                                                                      \
        return 1;                                                              \
      }                                                                        \
      if (alloc_stack_top != 0)                                                \
      {                                                                        \
        fprintf(stderr,                                                        \
                "ERROR: %s leaked %d allocation(s) when allocation %d/%d "     \
                "was instrumented to fail\n",                                  \
                test_name, alloc_stack_top, i + 1, num_allocs);                \
        return 1;                                                              \
      }                                                                        \
      if (bump_offset != 0)                                                    \
      {                                                                        \
        fprintf(stderr,                                                        \
                "ERROR: %s leaked %d bytes when allocation %d/%d "             \
                "was instrumented to fail\n",                                  \
                test_name, (int)bump_offset, i + 1, num_allocs);               \
        return 1;                                                              \
      }                                                                        \
    }                                                                          \
    if (bump_high_mark > (alloc_limit))                                        \
    {                                                                          \
      fprintf(stderr, "ERROR: max allocation %u in %s exceeded limit %d\n",    \
              (unsigned)bump_high_mark, test_name, (int)(alloc_limit));        \
      return 1;                                                                \
    }                                                                          \
    printf(                                                                    \
        "Allocation test for %s PASSED.\n"                                     \
        "  Max dynamic allocation: %d bytes\n",                                \
        test_name, (int)bump_high_mark);                                       \
    if (bump_high_mark > global_bump_high_mark)                                \
    {                                                                          \
      global_bump_high_mark = bump_high_mark;                                  \
    }                                                                          \
    if (bump_high_mark > *(global_high_mark_ptr))                              \
    {                                                                          \
      *(global_high_mark_ptr) = bump_high_mark;                                \
    }                                                                          \
  } while (0)

static int test_keygen_alloc_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];

  TEST_ALLOC_FAILURE("crypto_kem_keypair", crypto_kem_keypair(pk, sk),
                     MLK_TOTAL_ALLOC_KEYPAIR, &global_bump_high_mark_keypair);
  return 0;
}

static int test_enc_alloc_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key[CRYPTO_BYTES];

  /* Generate valid keypair first */
  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr, "ERROR: crypto_kem_keypair failed in enc test setup\n");
    return 1;
  }

  TEST_ALLOC_FAILURE("crypto_kem_enc", crypto_kem_enc(ct, key, pk),
                     MLK_TOTAL_ALLOC_ENCAPS, &global_bump_high_mark_encaps);
  return 0;
}

static int test_dec_alloc_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_enc[CRYPTO_BYTES];
  uint8_t key_dec[CRYPTO_BYTES];

  /* Generate valid keypair and ciphertext first */
  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr, "ERROR: crypto_kem_keypair failed in dec test setup\n");
    return 1;
  }

  if (crypto_kem_enc(ct, key_enc, pk) != 0)
  {
    fprintf(stderr, "ERROR: crypto_kem_enc failed in dec test setup\n");
    return 1;
  }

  TEST_ALLOC_FAILURE("crypto_kem_dec", crypto_kem_dec(key_dec, ct, sk),
                     MLK_TOTAL_ALLOC_DECAPS, &global_bump_high_mark_decaps);
  return 0;
}

static int test_check_pk_alloc_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];

  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr,
            "ERROR: crypto_kem_keypair failed in check_pk test setup\n");
    return 1;
  }

  TEST_ALLOC_FAILURE("crypto_kem_check_pk", crypto_kem_check_pk(pk),
                     MLK_TOTAL_ALLOC_KEYPAIR, &global_bump_high_mark_keypair);
  return 0;
}

static int test_check_sk_alloc_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];

  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr,
            "ERROR: crypto_kem_keypair failed in check_sk test setup\n");
    return 1;
  }

  TEST_ALLOC_FAILURE("crypto_kem_check_sk", crypto_kem_check_sk(sk),
                     MLK_TOTAL_ALLOC_KEYPAIR, &global_bump_high_mark_keypair);
  return 0;
}

/*
 * Helper macro to check allocation high watermark matches expected limit.
 */
#define CHECK_ALLOC_MATCH(high_mark, expected)                               \
  do                                                                         \
  {                                                                          \
    if ((expected) != (high_mark))                                           \
    {                                                                        \
      fprintf(stderr, "ERROR: %s = %u does not match %s = %d\n", #high_mark, \
              (unsigned)(high_mark), #expected, (int)(expected));            \
      return 1;                                                              \
    }                                                                        \
  } while (0)

int main(void)
{
  MLK_ALIGN uint8_t bump_buffer_storage[MLK_BUMP_ALLOC_SIZE];
  bump_buffer = bump_buffer_storage;

  if (test_keygen_alloc_failure() != 0)
  {
    return 1;
  }

  if (test_enc_alloc_failure() != 0)
  {
    return 1;
  }

  if (test_dec_alloc_failure() != 0)
  {
    return 1;
  }

  if (test_check_pk_alloc_failure() != 0)
  {
    return 1;
  }

  if (test_check_sk_alloc_failure() != 0)
  {
    return 1;
  }

  /* Check per-operation high watermarks match the declared limits */
  CHECK_ALLOC_MATCH(global_bump_high_mark_keypair, MLK_TOTAL_ALLOC_KEYPAIR);
  CHECK_ALLOC_MATCH(global_bump_high_mark_encaps, MLK_TOTAL_ALLOC_ENCAPS);
  CHECK_ALLOC_MATCH(global_bump_high_mark_decaps, MLK_TOTAL_ALLOC_DECAPS);
  CHECK_ALLOC_MATCH(global_bump_high_mark, MLK_TOTAL_ALLOC);

  /*
   * For parameter set 1024, also check that the high watermarks match
   * the MLK_MAX_TOTAL_ALLOC_* constants (which are defined as the 1024 values).
   */
#if MLK_CONFIG_API_PARAMETER_SET == 1024
  CHECK_ALLOC_MATCH(global_bump_high_mark_keypair, MLK_MAX_TOTAL_ALLOC_KEYPAIR);
  CHECK_ALLOC_MATCH(global_bump_high_mark_encaps, MLK_MAX_TOTAL_ALLOC_ENCAPS);
  CHECK_ALLOC_MATCH(global_bump_high_mark_decaps, MLK_MAX_TOTAL_ALLOC_DECAPS);
  CHECK_ALLOC_MATCH(global_bump_high_mark, MLK_MAX_TOTAL_ALLOC);
#endif /* MLK_CONFIG_API_PARAMETER_SET == 1024 */

  return 0;
}
