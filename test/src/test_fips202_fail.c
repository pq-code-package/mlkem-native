/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../../mlkem/mlkem_native.h"
#include "../test_vectors/expected_test_vectors.h"
#include "test_common.h"
#include "test_namespace.h"

/*
 * This test checks that we handle failures of a custom FIPS202
 * implementation correctly (see MLK_CONFIG_FIPS202_CAN_FAIL):
 * - The API function returns MLK_ERR_FIPS202_FAIL.
 * - Its output buffers are unmodified or zeroized.
 *
 * It is built with test/configs/test_fips202_fail_config.h, whose custom
 * FIPS202 headers (test/fips202_fail/) wrap mlkem-native's own FIPS202
 * implementation and call mlk_test_fips202_fail() before every FIPS202 call.
 */

static int fips202_counter = 0;
static int fips202_fail_on_counter = -1;

int mlk_test_fips202_fail(void);
int mlk_test_fips202_fail(void)
{
  return fips202_counter++ == fips202_fail_on_counter;
}

static void reset_all(void)
{
  fips202_counter = 0;
  fips202_fail_on_counter = -1;
}

#define OUTPUT_MARKER 0xA5

/* Returns 1 if buf is unmodified (all OUTPUT_MARKER) or zeroized. */
static int unmodified_or_zeroized(const uint8_t *buf, size_t len)
{
  size_t i;
  int unmodified = 1, zeroized = 1;
  for (i = 0; i < len; i++)
  {
    unmodified &= (buf[i] == OUTPUT_MARKER);
    zeroized &= (buf[i] == 0);
  }
  return unmodified || zeroized;
}

/*
 * Run `call` once to count its FIPS202 calls, then once per FIPS202 call,
 * making that call fail. Before each run, the output buffers out0 and out1
 * (of lengths len0 and len1; len1 may be 0) are set to OUTPUT_MARKER.
 */
#define TEST_FIPS202_FAILURE(test_name, call, out0, len0, out1, len1)          \
  do                                                                           \
  {                                                                            \
    int num_fips202_calls, i, rc;                                              \
    /* First pass: count FIPS202 invocations */                                \
    reset_all();                                                               \
    rc = call;                                                                 \
    if (rc != 0)                                                               \
    {                                                                          \
      fprintf(stderr,                                                          \
              "ERROR: %s failed with return code %d (%s) in dry-run\n",        \
              test_name, rc, mlk_err_name(rc));                                \
      return 1;                                                                \
    }                                                                          \
    num_fips202_calls = fips202_counter;                                       \
    /* Second pass: test each FIPS202 failure */                               \
    for (i = 0; i < num_fips202_calls; i++)                                    \
    {                                                                          \
      reset_all();                                                             \
      fips202_fail_on_counter = i;                                             \
      memset((out0), OUTPUT_MARKER, (len0));                                   \
      memset((out1), OUTPUT_MARKER, (len1));                                   \
      rc = call;                                                               \
      if (rc != MLK_ERR_FIPS202_FAIL)                                          \
      {                                                                        \
        fprintf(stderr,                                                        \
                "ERROR: %s returned %d (%s) instead of %d (%s) when FIPS202 "  \
                "call %d/%d was instrumented to fail\n",                       \
                test_name, rc, mlk_err_name(rc), MLK_ERR_FIPS202_FAIL,         \
                mlk_err_name(MLK_ERR_FIPS202_FAIL), i + 1, num_fips202_calls); \
        return 1;                                                              \
      }                                                                        \
      if (!unmodified_or_zeroized((out0), (len0)) ||                           \
          !unmodified_or_zeroized((out1), (len1)))                             \
      {                                                                        \
        fprintf(stderr,                                                        \
                "ERROR: %s left an output neither unmodified nor zeroized "    \
                "when FIPS202 call %d/%d was instrumented to fail\n",          \
                test_name, i + 1, num_fips202_calls);                          \
        return 1;                                                              \
      }                                                                        \
    }                                                                          \
    printf(                                                                    \
        "FIPS202 failure test for %s PASSED.\n"                                \
        "  Tested %d FIPS202 invocation point(s)\n",                           \
        test_name, num_fips202_calls);                                         \
  } while (0)

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
static int test_keypair_derand_fips202_failure(void)
{
  uint8_t pk[MLKEM_PK_BYTES];
  uint8_t sk[MLKEM_SK_BYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];

  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);

  TEST_FIPS202_FAILURE("keypair_derand", mlk_kem_keypair_derand(pk, sk, coins),
                       pk, sizeof(pk), sk, sizeof(sk));
  return 0;
}
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static int test_enc_derand_fips202_failure(void)
{
  uint8_t ct[MLKEM_CT_BYTES];
  uint8_t ss[MLKEM_BYTES];

  TEST_FIPS202_FAILURE(
      "enc_derand", mlk_kem_enc_derand(ct, ss, test_vector_pk, test_vector_m),
      ct, sizeof(ct), ss, sizeof(ss));
  return 0;
}
#endif /* !MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static int test_dec_fips202_failure(void)
{
  uint8_t ss[MLKEM_BYTES];

  TEST_FIPS202_FAILURE("dec", mlk_kem_dec(ss, test_vector_ct, test_vector_sk),
                       ss, sizeof(ss), ss, 0);
  return 0;
}

static int test_check_sk_fips202_failure(void)
{
  uint8_t unused[1];

  TEST_FIPS202_FAILURE("check_sk", mlk_kem_check_sk(test_vector_sk), unused, 0,
                       unused, 0);
  return 0;
}
#endif /* !MLK_CONFIG_NO_DECAPS_API */

/* Prototype for a re-#define'd main, to satisfy -Wmissing-prototypes. */
#if defined(main)
int main(void);
#endif
int main(void)
{
  int r = 0;

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
  r |= test_keypair_derand_fips202_failure();
#endif

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
  r |= test_enc_derand_fips202_failure();
#endif

#if !defined(MLK_CONFIG_NO_DECAPS_API)
  r |= test_dec_fips202_failure();
  r |= test_check_sk_fips202_failure();
#endif

  return r != 0;
}
