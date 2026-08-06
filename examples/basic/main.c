/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include <string.h>

/* Import public mlkem-native API */
#include "expected_test_vectors.h"
#include "mlkem_native/mlkem_native.h"
#include "test_only_rng/notrandombytes.h"

/* Convenience abbreviations for the key and ciphertext sizes.
 *
 * Ordinarily you know the parameter set you're working with, so you would
 * just use the level-specific constants directly, e.g. MLKEM512_PUBLICKEYBYTES,
 * MLKEM768_CIPHERTEXTBYTES, or MLKEM1024_SECRETKEYBYTES.
 *
 * These examples, however, are compiled for all three parameter sets (512, 768,
 * 1024), so we keep things generic by deriving the sizes from the configured
 * MLK_CONFIG_PARAMETER_SET. */
#define MLKEM_PK_BYTES MLKEM_PUBLICKEYBYTES(MLK_CONFIG_PARAMETER_SET)
#define MLKEM_SK_BYTES MLKEM_SECRETKEYBYTES(MLK_CONFIG_PARAMETER_SET)
#define MLKEM_CT_BYTES MLKEM_CIPHERTEXTBYTES(MLK_CONFIG_PARAMETER_SET)

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

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
static int example_keygen(void)
{
  uint8_t pk[MLKEM_PK_BYTES];
  uint8_t sk[MLKEM_SK_BYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("Generating keypair (randomized)... ");
  CHECK(mlkem_keypair(pk, sk) == 0);
  CHECK(memcmp(pk, test_vector_pk, MLKEM_PK_BYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk, MLKEM_SK_BYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("Generating keypair (deterministic)... ");
  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);
  CHECK(mlkem_keypair_derand(pk, sk, coins) == 0);
  CHECK(memcmp(pk, test_vector_pk, MLKEM_PK_BYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk, MLKEM_SK_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_KEYPAIR_API */
static int example_keygen(void)
{
  printf("Generating keypair... SKIPPED (keygen API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_KEYPAIR_API */

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static int example_encaps(void)
{
  uint8_t ct[MLKEM_CT_BYTES];
  uint8_t ss[MLKEM_BYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("Encaps (randomized)... ");
  CHECK(mlkem_enc(ct, ss, test_vector_pk) == 0);
  CHECK(memcmp(ct, test_vector_ct, MLKEM_CT_BYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss, MLKEM_BYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("Encaps (deterministic)... ");
  CHECK(mlkem_enc_derand(ct, ss, test_vector_pk, test_vector_m) == 0);
  CHECK(memcmp(ct, test_vector_ct, MLKEM_CT_BYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss, MLKEM_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_ENCAPS_API */
static int example_encaps(void)
{
  printf("Encaps... SKIPPED (encaps API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static int example_decaps(void)
{
  uint8_t ss[MLKEM_BYTES];

  printf("Decaps... ");
  CHECK(mlkem_dec(ss, test_vector_ct, test_vector_sk) == 0);
  CHECK(memcmp(ss, test_vector_ss, MLKEM_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_DECAPS_API */
static int example_decaps(void)
{
  printf("Decaps... SKIPPED (decaps API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_DECAPS_API */

int main(void)
{
  int r = 0;

  /* WARNING: Test-only
   * Normally, you would seed a PRNG _once_ with trustworthy entropy and not
   * reseed it afterwards. Here, we reseed before each API call to make each
   * test independent and reproducible even when some API is disabled. */
  randombytes_reset();
  r |= example_keygen();
  randombytes_reset();
  r |= example_encaps();
  r |= example_decaps();

  return r;
}
