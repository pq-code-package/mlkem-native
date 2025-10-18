/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include "notrandombytes/notrandombytes.h"

#include "../mlkem/src/compress.h"
#include "../mlkem/src/poly.h"
#include "../mlkem/src/poly_k.h"

#ifndef NUM_RANDOM_TESTS
#ifdef MLKEM_DEBUG
#define NUM_RANDOM_TESTS 1000
#else
#define NUM_RANDOM_TESTS 10000
#endif
#endif /* !NUM_RANDOM_TESTS */

/* Declarations for _c functions exposed by MLK_STATIC_TESTABLE= */

void mlk_poly_reduce_c(mlk_poly *r);
void mlk_poly_tomont_c(mlk_poly *r);
void mlk_poly_ntt_c(mlk_poly *r);
void mlk_poly_invntt_tomont_c(mlk_poly *r);
void mlk_poly_tobytes_c(uint8_t r[MLKEM_POLYBYTES], const mlk_poly *a);
void mlk_poly_frombytes_c(mlk_poly *r, const uint8_t a[MLKEM_POLYBYTES]);
void mlk_polyvec_basemul_acc_montgomery_cached_c(
    mlk_poly *r, const mlk_polyvec a, const mlk_polyvec b,
    const mlk_polyvec_mulcache b_cache);
void mlk_poly_mulcache_compute_c(mlk_poly_mulcache *x, const mlk_poly *a);

#define CHECK(x)                                              \
  do                                                          \
  {                                                           \
    int rc;                                                   \
    rc = (x);                                                 \
    if (!rc)                                                  \
    {                                                         \
      fprintf(stderr, "ERROR (%s,%d)\n", __FILE__, __LINE__); \
      return 1;                                               \
    }                                                         \
  } while (0)

#if defined(MLK_USE_NATIVE_POLY_REDUCE) ||                                  \
    defined(MLK_USE_NATIVE_POLY_TOMONT) || defined(MLK_USE_NATIVE_NTT) ||   \
    defined(MLK_USE_NATIVE_INTT) || defined(MLK_USE_NATIVE_POLY_TOBYTES) || \
    defined(MLK_USE_NATIVE_POLY_FROMBYTES) ||                               \
    defined(MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)

/* Backend unit test helper functions */
static void print_i16_array(const char *label, const int16_t *array, size_t len)
{
  size_t i;
  fprintf(stderr, "%s:\n", label);
  for (i = 0; i < len; i++)
  {
    if (i % 16 == 0)
    {
      fprintf(stderr, "  ");
    }
    fprintf(stderr, "%6d", array[i]);
    if (i % 16 == 15)
    {
      fprintf(stderr, "\n");
    }
    else
    {
      fprintf(stderr, " ");
    }
  }
  if (len % 16 != 0)
  {
    fprintf(stderr, "\n");
  }
}

static void generate_i16_array_zeros(int16_t *data, size_t len)
{
  memset(data, 0, len * sizeof(int16_t));
}

static void generate_i16_array_single(int16_t *data, size_t len, size_t pos,
                                      int16_t value)
{
  memset(data, 0, len * sizeof(int16_t));
  data[pos] = value;
}

static void generate_i16_array_constant(int16_t *data, size_t len,
                                        int16_t value)
{
  size_t i;
  for (i = 0; i < len; i++)
  {
    data[i] = value;
  }
}

/* This does not generate a uniformly random distribution, but it's
 * good enough for our test.
 *
 * The lower bound is inclusive, the upper bound exclusive, matching
 * the CBMC assertions in the code base. */
static void generate_i16_array_ranged(int16_t *data, size_t len, int min_incl,
                                      int max_excl)
{
  size_t i;

  randombytes((uint8_t *)data, len * sizeof(int16_t));
  for (i = 0; i < len; i++)
  {
    data[i] = (int16_t)((unsigned)min_incl +
                        ((unsigned)data[i] % (unsigned)(max_excl - min_incl)));
  }
}

#if defined(MLK_USE_NATIVE_POLY_TOBYTES)
static void print_u8_array(const char *label, const uint8_t *array, size_t len)
{
  size_t i;
  fprintf(stderr, "%s:\n", label);
  for (i = 0; i < len; i++)
  {
    if (i % 16 == 0)
    {
      fprintf(stderr, "  ");
    }
    fprintf(stderr, "%4d", array[i]);
    if (i % 16 == 15)
    {
      fprintf(stderr, "\n");
    }
    else
    {
      fprintf(stderr, " ");
    }
  }
  if (len % 16 != 0)
  {
    fprintf(stderr, "\n");
  }
}

static int compare_u8_arrays(const uint8_t *a, const uint8_t *b, unsigned len,
                             const char *test_name)
{
  unsigned i;
  for (i = 0; i < len; i++)
  {
    if (a[i] != b[i])
    {
      fprintf(stderr, "FAIL: %s\n", test_name);
      fprintf(stderr,
              "  First difference at index %u: native=%d, reference=%d\n", i,
              a[i], b[i]);
      print_u8_array("Native result", a, len);
      print_u8_array("Reference result", b, len);
      return 0;
    }
  }
  return 1;
}
#endif /* MLK_USE_NATIVE_POLY_TOBYTES */

static int compare_i16_arrays(const int16_t *a, const int16_t *b, unsigned len,
                              const char *test_name, const int16_t *input)
{
  unsigned i;
  for (i = 0; i < len; i++)
  {
    if (a[i] != b[i])
    {
      fprintf(stderr, "FAIL: %s\n", test_name);
      fprintf(stderr,
              "  First difference at index %u: native=%d, reference=%d\n", i,
              a[i], b[i]);
      if (input)
      {
        print_i16_array("Input", input, len);
      }
      print_i16_array("Native result", a, len);
      print_i16_array("Reference result", b, len);
      return 0;
    }
  }
  return 1;
}

#ifdef MLK_USE_NATIVE_POLY_REDUCE
static int test_poly_reduce_core(const int16_t *input, const char *test_name)
{
  mlk_poly test_poly, ref_poly;

  memcpy(test_poly.coeffs, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

  mlk_poly_reduce(&test_poly);
  mlk_poly_reduce_c(&ref_poly);

  CHECK(compare_i16_arrays(test_poly.coeffs, ref_poly.coeffs, MLKEM_N,
                           test_name, NULL));
  return 0;
}

static int test_native_poly_reduce(void)
{
  int16_t test_data[MLKEM_N];
  int pos, i;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_poly_reduce_core(test_data, "poly_reduce_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, (size_t)pos, 1);
    CHECK(test_poly_reduce_core(test_data, "poly_reduce_single") == 0);
  }

  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(test_data, MLKEM_N, INT16_MIN, INT16_MAX + 1);
    CHECK(test_poly_reduce_core(test_data, "poly_reduce_random") == 0);
  }

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_REDUCE */

#ifdef MLK_USE_NATIVE_POLY_TOMONT
static int test_poly_tomont_core(const int16_t *input, const char *test_name)
{
  mlk_poly test_poly, ref_poly;

  memcpy(test_poly.coeffs, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

  mlk_poly_tomont(&test_poly);
  mlk_poly_tomont_c(&ref_poly);

  /* Normalize */
  mlk_poly_reduce_c(&ref_poly);
  mlk_poly_reduce_c(&test_poly);

  CHECK(compare_i16_arrays(test_poly.coeffs, ref_poly.coeffs, MLKEM_N,
                           test_name, NULL));
  return 0;
}

static int test_native_poly_tomont(void)
{
  int16_t test_data[MLKEM_N];
  int pos, i;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_poly_tomont_core(test_data, "poly_tomont_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, (size_t)pos, 1);
    CHECK(test_poly_tomont_core(test_data, "poly_tomont_single") == 0);
  }

  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(test_data, MLKEM_N, -MLKEM_Q + 1, MLKEM_Q);
    CHECK(test_poly_tomont_core(test_data, "poly_tomont_random") == 0);
  }

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_TOMONT */

#ifdef MLK_USE_NATIVE_NTT
static int test_ntt_core(const int16_t *input, const char *test_name)
{
  mlk_poly test_poly, ref_poly;

  memcpy(test_poly.coeffs, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

  mlk_poly_ntt(&test_poly);
  mlk_poly_ntt_c(&ref_poly);

#ifdef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
  mlk_poly_permute_bitrev_to_custom(ref_poly.coeffs);
#endif

  /* Normalize */
  mlk_poly_reduce_c(&ref_poly);
  mlk_poly_reduce_c(&test_poly);

  CHECK(compare_i16_arrays(test_poly.coeffs, ref_poly.coeffs, MLKEM_N,
                           test_name, input));
  return 0;
}

static int test_native_ntt(void)
{
  int16_t test_data[MLKEM_N];
  int pos, i;

  /* Use a more complex test that will expose the bug */
  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(test_data, MLKEM_N, -MLKEM_Q + 1, MLKEM_Q);
    CHECK(test_ntt_core(test_data, "ntt_complex") == 0);
  }

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_ntt_core(test_data, "ntt_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, (size_t)pos, 1);
    CHECK(test_ntt_core(test_data, "ntt_single") == 0);
  }

  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(test_data, MLKEM_N, -MLKEM_Q + 1, MLKEM_Q);
    CHECK(test_ntt_core(test_data, "ntt_random") == 0);
  }

  return 0;
}
#endif /* MLK_USE_NATIVE_NTT */

#ifdef MLK_USE_NATIVE_INTT
static int test_intt_core(const int16_t *input, const char *test_name)
{
  mlk_poly test_poly, ref_poly;

  memcpy(test_poly.coeffs, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

#ifdef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
  mlk_poly_permute_bitrev_to_custom(test_poly.coeffs);
#endif

  mlk_poly_invntt_tomont(&test_poly);
  mlk_poly_invntt_tomont_c(&ref_poly);

  /* Normalize */
  mlk_poly_reduce_c(&ref_poly);
  mlk_poly_reduce_c(&test_poly);

  CHECK(compare_i16_arrays(test_poly.coeffs, ref_poly.coeffs, MLKEM_N,
                           test_name, input));
  return 0;
}

static int test_native_intt(void)
{
  int16_t test_data[MLKEM_N];
  int coeff, pos, i;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_intt_core(test_data, "intt_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, (size_t)pos, 1);
    CHECK(test_intt_core(test_data, "intt_single") == 0);
  }

  /* invNTT implementation are at risk of overflow when not
   * correctly reducing those coefficients which grow exponentially
   * fast in the number of layers. Most notably, the first and second
   * coefficients in the output of the invNTT are sums of 128 input
   * coefficients each, which can easily overflow.
   *
   * Test this by running the invNTT on constant input coefficients.
   * Note that since the invNTT often performs a reduction or normalization
   * at the beginning, it's unclear which exact choice of constant data
   * would trigger the largest coefficient growth, so we just try them all.
   *
   * Gradually increase absolute value to find smallest failure first.
   */
  for (coeff = 0; coeff <= INT16_MAX; coeff++)
  {
    generate_i16_array_constant(test_data, MLKEM_N, (int16_t)coeff);
    CHECK(test_intt_core(test_data, "intt_constant") == 0);

    generate_i16_array_constant(test_data, MLKEM_N, (int16_t)-coeff);
    CHECK(test_intt_core(test_data, "intt_constant") == 0);
  }

  /* This one is omitted by the previous loop */
  generate_i16_array_constant(test_data, MLKEM_N, INT16_MIN);
  CHECK(test_intt_core(test_data, "intt_constant") == 0);


  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(test_data, MLKEM_N, INT16_MIN, INT16_MAX + 1);
    CHECK(test_intt_core(test_data, "intt_random") == 0);
  }

  return 0;
}
#endif /* MLK_USE_NATIVE_INTT */

#ifdef MLK_USE_NATIVE_POLY_TOBYTES
static int test_poly_tobytes_core(const int16_t *input, const char *test_name)
{
  uint8_t test_result[MLKEM_POLYBYTES], ref_result[MLKEM_POLYBYTES];
  mlk_poly test_poly, ref_poly;

  memcpy(test_poly.coeffs, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

#ifdef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
  mlk_poly_permute_bitrev_to_custom(test_poly.coeffs);
#endif

  mlk_poly_tobytes(test_result, &test_poly);
  mlk_poly_tobytes_c(ref_result, &ref_poly);

  CHECK(compare_u8_arrays(test_result, ref_result, MLKEM_POLYBYTES, test_name));
  return 1;
}

static int test_native_poly_tobytes(void)
{
  int16_t test_data[MLKEM_N];
  int pos, i;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_poly_tobytes_core(test_data, "poly_tobytes_zeros") == 1);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, (size_t)pos, 1);
    CHECK(test_poly_tobytes_core(test_data, "poly_tobytes_single") == 1);
  }

  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(test_data, MLKEM_N, 0, MLKEM_Q);
    CHECK(test_poly_tobytes_core(test_data, "poly_tobytes_random") == 1);
  }

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_TOBYTES */

#ifdef MLK_USE_NATIVE_POLY_FROMBYTES
static int test_poly_frombytes_core(const uint8_t *input_bytes,
                                    const char *test_name)
{
  mlk_poly test_poly, ref_poly;

  mlk_poly_frombytes(&test_poly, input_bytes);
  mlk_poly_frombytes_c(&ref_poly, input_bytes);

#ifdef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
  mlk_poly_permute_bitrev_to_custom(ref_poly.coeffs);
#endif

  CHECK(compare_i16_arrays(test_poly.coeffs, ref_poly.coeffs, MLKEM_N,
                           test_name, NULL));
  return 0;
}

static int test_native_poly_frombytes(void)
{
  uint8_t test_bytes[MLKEM_POLYBYTES];
  int16_t temp_data[MLKEM_POLYBYTES / 2];
  int i;

  /* Test with zero bytes */
  memset(test_bytes, 0, MLKEM_POLYBYTES);
  CHECK(test_poly_frombytes_core(test_bytes, "poly_frombytes_zeros") == 0);

  /* Test with incremental bytes */
  generate_i16_array_zeros(temp_data, MLKEM_POLYBYTES / 2);
  generate_i16_array_ranged(temp_data, MLKEM_POLYBYTES / 2, INT16_MIN,
                            INT16_MAX + 1);
  memcpy(test_bytes, temp_data, MLKEM_POLYBYTES);
  CHECK(test_poly_frombytes_core(test_bytes, "poly_frombytes_incremental") ==
        0);

  /* Test with random bytes */
  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(temp_data, MLKEM_POLYBYTES / 2, INT16_MIN,
                              INT16_MAX + 1);
    memcpy(test_bytes, temp_data, MLKEM_POLYBYTES);
    CHECK(test_poly_frombytes_core(test_bytes, "poly_frombytes_random") == 0);
  }

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_FROMBYTES */

#ifdef MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
static int test_polyvec_basemul_core(const int16_t *a, const int16_t *b,
                                     const char *test_name)
{
  mlk_poly test_result, ref_result;
  mlk_polyvec test_a, test_b, ref_a, ref_b;
  mlk_polyvec_mulcache test_cache, ref_cache;
  int i;

  /* Copy test data to structures */
  for (i = 0; i < MLKEM_K; i++)
  {
    memcpy(test_a[i].coeffs, &a[i * MLKEM_N], MLKEM_N * sizeof(int16_t));
    memcpy(test_b[i].coeffs, &b[i * MLKEM_N], MLKEM_N * sizeof(int16_t));
    memcpy(ref_a[i].coeffs, &a[i * MLKEM_N], MLKEM_N * sizeof(int16_t));
    memcpy(ref_b[i].coeffs, &b[i * MLKEM_N], MLKEM_N * sizeof(int16_t));

#ifdef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
    mlk_poly_permute_bitrev_to_custom(test_a[i].coeffs);
    mlk_poly_permute_bitrev_to_custom(test_b[i].coeffs);
#endif

    mlk_poly_mulcache_compute_c(&ref_cache[i], &ref_b[i]);
    mlk_poly_mulcache_compute(&test_cache[i], &test_b[i]);
  }

  mlk_polyvec_basemul_acc_montgomery_cached(&test_result, test_a, test_b,
                                            test_cache);
  mlk_polyvec_basemul_acc_montgomery_cached_c(&ref_result, ref_a, ref_b,
                                              ref_cache);

#ifdef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
  mlk_poly_permute_bitrev_to_custom(ref_result.coeffs);
#endif

  /* Normalize */
  mlk_poly_reduce_c(&ref_result);
  mlk_poly_reduce_c(&test_result);

  CHECK(compare_i16_arrays(test_result.coeffs, ref_result.coeffs, MLKEM_N,
                           test_name, NULL));
  return 0;
}

static int test_native_polyvec_basemul(void)
{
  int16_t a[MLKEM_K * MLKEM_N];
  int16_t b[MLKEM_K * MLKEM_N];
  int i;

  /* Test with zeros */
  generate_i16_array_zeros(a, MLKEM_K * MLKEM_N);
  generate_i16_array_zeros(b, MLKEM_K * MLKEM_N);
  CHECK(test_polyvec_basemul_core(a, b, "polyvec_basemul_zeros") == 0);

  /* Test with random data */
  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    generate_i16_array_ranged(a, MLKEM_K * MLKEM_N, 0, MLKEM_UINT12_LIMIT);
    generate_i16_array_ranged(b, MLKEM_K * MLKEM_N, 0, MLKEM_UINT12_LIMIT);
    CHECK(test_polyvec_basemul_core(a, b, "polyvec_basemul_random") == 0);
  }

  return 0;
}
#endif /* MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

static int test_backend_units(void)
{
  /* Set fixed seed for reproducible tests */
  randombytes_reset();

#ifdef MLK_USE_NATIVE_POLY_REDUCE
  CHECK(test_native_poly_reduce() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLY_TOMONT
  CHECK(test_native_poly_tomont() == 0);
#endif

#ifdef MLK_USE_NATIVE_NTT
  CHECK(test_native_ntt() == 0);
#endif

#ifdef MLK_USE_NATIVE_INTT
  CHECK(test_native_intt() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLY_TOBYTES
  CHECK(test_native_poly_tobytes() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLY_FROMBYTES
  CHECK(test_native_poly_frombytes() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
  CHECK(test_native_polyvec_basemul() == 0);
#endif

  return 0;
}

#endif /* MLK_USE_NATIVE_POLY_REDUCE || MLK_USE_NATIVE_POLY_TOMONT ||     \
          MLK_USE_NATIVE_NTT || MLK_USE_NATIVE_INTT ||                    \
          MLK_USE_NATIVE_POLY_TOBYTES || MLK_USE_NATIVE_POLY_FROMBYTES || \
          MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */


/* This test invokes the polynomial (de)compression routines
 * with minimally sized buffers. When run with address sanitization,
 * this ensures that no buffer overflow is happening. This is of interest
 * because the compressed buffers sometimes have unaligned lengths and
 * are therefore at risk of being overflowed by vectorized code. */
static int test_poly_compress_no_overflow(void)
{
#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || (MLKEM_K == 2 || MLKEM_K == 3)
  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d4(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d4(&s, r);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d10(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d10(&s, r);
  }
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == 3 */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4
  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d5(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d5(&s, r);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d11(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d11(&s, r);
  }
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4 */

  return 0;
}

int main(void)
{
  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  /* Run backend unit tests */
#if defined(MLK_USE_NATIVE_POLY_REDUCE) ||                                  \
    defined(MLK_USE_NATIVE_POLY_TOMONT) || defined(MLK_USE_NATIVE_NTT) ||   \
    defined(MLK_USE_NATIVE_INTT) || defined(MLK_USE_NATIVE_POLY_TOBYTES) || \
    defined(MLK_USE_NATIVE_POLY_FROMBYTES) ||                               \
    defined(MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
  CHECK(test_backend_units() == 0);
#endif /* MLK_USE_NATIVE_POLY_REDUCE || MLK_USE_NATIVE_POLY_TOMONT ||     \
          MLK_USE_NATIVE_NTT || MLK_USE_NATIVE_INTT ||                    \
          MLK_USE_NATIVE_POLY_TOBYTES || MLK_USE_NATIVE_POLY_FROMBYTES || \
          MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

  /* Test poly compress no overflow */
  CHECK(test_poly_compress_no_overflow() == 0);

  return 0;
}
