/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>

/* Expose internal functions */
#define MLK_BUILD_INTERNAL
#include "../../mlkem/mlkem_native.h"
#include "../../mlkem/src/common.h"

/*
 * This test checks that we handle randombytes failures correctly by:
 * - Returning MLK_ERR_RNG_FAIL when randombytes fails
 *
 * This is done through a custom randombytes implementation that can be
 * configured to fail at specific invocation counts.
 */

/* Include notrandombytes, renaming its randombytes to notrandombytes */
#define randombytes notrandombytes
#include "../notrandombytes/notrandombytes.c"
#undef randombytes

/*
 * Randombytes invocation tracker
 */

int randombytes(uint8_t *buf, size_t len);
int randombytes_counter = 0;
int randombytes_fail_on_counter = -1;

static void reset_all(void)
{
  randombytes_counter = 0;
  randombytes_fail_on_counter = -1;
  randombytes_reset();
}

int randombytes(uint8_t *buf, size_t len)
{
  int current_invocation = randombytes_counter++;

  if (current_invocation == randombytes_fail_on_counter)
  {
    return -1;
  }

  return notrandombytes(buf, len);
}

#define TEST_RNG_FAILURE(test_name, call)                              \
  do                                                                   \
  {                                                                    \
    int num_randombytes_calls, i, rc;                                  \
    /* First pass: count randombytes invocations */                    \
    reset_all();                                                       \
    rc = call;                                                         \
    if (rc != 0)                                                       \
    {                                                                  \
      fprintf(stderr,                                                  \
              "ERROR: %s failed with return code %d "                  \
              "in dry-run\n",                                          \
              test_name, rc);                                          \
      return 1;                                                        \
    }                                                                  \
    num_randombytes_calls = randombytes_counter;                       \
    if (num_randombytes_calls == 0)                                    \
    {                                                                  \
      printf("Skipping %s (no randombytes() calls)\n", test_name);     \
      break;                                                           \
    }                                                                  \
    /* Second pass: test each randombytes failure */                   \
    for (i = 0; i < num_randombytes_calls; i++)                        \
    {                                                                  \
      reset_all();                                                     \
      randombytes_fail_on_counter = i;                                 \
      rc = call;                                                       \
      if (rc != MLK_ERR_RNG_FAIL)                                      \
      {                                                                \
        int rc2;                                                       \
        /* Re-run to ensure clean state */                             \
        reset_all();                                                   \
        rc2 = call;                                                    \
        (void)rc2;                                                     \
        if (rc == 0)                                                   \
        {                                                              \
          fprintf(stderr,                                              \
                  "ERROR: %s unexpectedly succeeded when randombytes " \
                  "%d/%d was instrumented to fail\n",                  \
                  test_name, i + 1, num_randombytes_calls);            \
        }                                                              \
        else                                                           \
        {                                                              \
          fprintf(stderr,                                              \
                  "ERROR: %s failed with wrong error code %d "         \
                  "(expected %d) when randombytes %d/%d was "          \
                  "instrumented to fail\n",                            \
                  test_name, rc, MLK_ERR_RNG_FAIL, i + 1,              \
                  num_randombytes_calls);                              \
        }                                                              \
        return 1;                                                      \
      }                                                                \
    }                                                                  \
    printf(                                                            \
        "RNG failure test for %s PASSED.\n"                            \
        "  Tested %d randombytes invocation point(s)\n",               \
        test_name, num_randombytes_calls);                             \
  } while (0)

static int all_zero(const uint8_t *buf, size_t len)
{
  size_t i;
  for (i = 0; i < len; i++)
  {
    if (buf[i] != 0)
    {
      return 0;
    }
  }

  return 1;
}

static int test_keygen_rng_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];

  TEST_RNG_FAILURE("crypto_kem_keypair", crypto_kem_keypair(pk, sk));

  memset(pk, 0xA5, sizeof(pk));
  memset(sk, 0x5A, sizeof(sk));
  reset_all();
  randombytes_fail_on_counter = 0;
  if (crypto_kem_keypair(pk, sk) != MLK_ERR_RNG_FAIL)
  {
    fprintf(stderr, "ERROR: crypto_kem_keypair did not fail on RNG failure\n");
    return 1;
  }
  if (!all_zero(pk, sizeof(pk)) || !all_zero(sk, sizeof(sk)))
  {
    fprintf(stderr,
            "ERROR: crypto_kem_keypair did not clear outputs on RNG "
            "failure\n");
    return 1;
  }

  return 0;
}

static int test_enc_rng_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t ss[CRYPTO_BYTES];

  /* Generate valid keypair first */
  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr, "ERROR: crypto_kem_keypair failed in enc test setup\n");
    return 1;
  }

  TEST_RNG_FAILURE("crypto_kem_enc", crypto_kem_enc(ct, ss, pk));

  memset(ct, 0xA5, sizeof(ct));
  memset(ss, 0x5A, sizeof(ss));
  reset_all();
  randombytes_fail_on_counter = 0;
  if (crypto_kem_enc(ct, ss, pk) != MLK_ERR_RNG_FAIL)
  {
    fprintf(stderr, "ERROR: crypto_kem_enc did not fail on RNG failure\n");
    return 1;
  }
  if (!all_zero(ct, sizeof(ct)) || !all_zero(ss, sizeof(ss)))
  {
    fprintf(stderr,
            "ERROR: crypto_kem_enc did not clear outputs on RNG failure\n");
    return 1;
  }

  return 0;
}

static int test_dec_rng_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t ss_enc[CRYPTO_BYTES];
  uint8_t ss_dec[CRYPTO_BYTES];

  /* Generate valid keypair and ciphertext first */
  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr, "ERROR: crypto_kem_keypair failed in dec test setup\n");
    return 1;
  }

  if (crypto_kem_enc(ct, ss_enc, pk) != 0)
  {
    fprintf(stderr, "ERROR: crypto_kem_enc failed in dec test setup\n");
    return 1;
  }

  TEST_RNG_FAILURE("crypto_kem_dec", crypto_kem_dec(ss_dec, ct, sk));
  return 0;
}

static int test_check_pk_rng_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];

  /* Generate valid keypair first */
  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr,
            "ERROR: crypto_kem_keypair failed in check_pk test setup\n");
    return 1;
  }

  TEST_RNG_FAILURE("crypto_kem_check_pk", crypto_kem_check_pk(pk));
  return 0;
}

static int test_check_sk_rng_failure(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];

  /* Generate valid keypair first */
  reset_all();
  if (crypto_kem_keypair(pk, sk) != 0)
  {
    fprintf(stderr,
            "ERROR: crypto_kem_keypair failed in check_sk test setup\n");
    return 1;
  }

  TEST_RNG_FAILURE("crypto_kem_check_sk", crypto_kem_check_sk(sk));
  return 0;
}

/* Prototype for a re-#define'd main, to satisfy -Wmissing-prototypes. */
#if defined(main)
int main(void);
#endif
int main(void)
{
  if (test_keygen_rng_failure() != 0)
  {
    return 1;
  }

  if (test_enc_rng_failure() != 0)
  {
    return 1;
  }

  if (test_dec_rng_failure() != 0)
  {
    return 1;
  }

  if (test_check_pk_rng_failure() != 0)
  {
    return 1;
  }

  if (test_check_sk_rng_failure() != 0)
  {
    return 1;
  }

  return 0;
}
