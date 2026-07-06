/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include <string.h>

/* Import public mlkem-native API */
#include "expected_test_vectors.h"
#include "mlkem_native/mlkem_native.h"

/* No randombytes needed for deterministic API */

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
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];

  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);

  printf("Generating keypair (deterministic)... ");
  CHECK(crypto_kem_keypair_derand(pk, sk, coins) == 0);
  CHECK(memcmp(pk, test_vector_pk, CRYPTO_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk, CRYPTO_SECRETKEYBYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_KEYPAIR_API */
static int example_keygen(void)
{
  printf(
      "Generating keypair (deterministic)... SKIPPED (keygen API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_KEYPAIR_API */

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static int example_encaps(void)
{
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t ss[CRYPTO_BYTES];

  printf("Encaps (deterministic)... ");
  CHECK(crypto_kem_enc_derand(ct, ss, test_vector_pk, test_vector_m) == 0);
  CHECK(memcmp(ct, test_vector_ct, CRYPTO_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss, CRYPTO_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_ENCAPS_API */
static int example_encaps(void)
{
  printf("Encaps (deterministic)... SKIPPED (encaps API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static int example_decaps(void)
{
  uint8_t ss[CRYPTO_BYTES];

  printf("Decaps... ");
  CHECK(crypto_kem_dec(ss, test_vector_ct, test_vector_sk) == 0);
  CHECK(memcmp(ss, test_vector_ss, CRYPTO_BYTES) == 0);
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
  r |= example_keygen();
  r |= example_encaps();
  r |= example_decaps();
  return r;
}
