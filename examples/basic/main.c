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

#if !defined(MLK_CONFIG_NO_KEYPAIR_API) && \
    !defined(MLK_CONFIG_NO_RANDOMIZED_API)
static int example_keygen(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];

  printf("Generating keypair... ");
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  CHECK(memcmp(pk, test_vector_pk, CRYPTO_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk, CRYPTO_SECRETKEYBYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_KEYPAIR_API && !MLK_CONFIG_NO_RANDOMIZED_API */
static int example_keygen(void)
{
  printf("Generating keypair... SKIPPED (keygen API disabled)\n");
  return 0;
}
#endif /* !(!MLK_CONFIG_NO_KEYPAIR_API && !MLK_CONFIG_NO_RANDOMIZED_API) */

#if !defined(MLK_CONFIG_NO_ENCAPS_API) && !defined(MLK_CONFIG_NO_RANDOMIZED_API)
static int example_encaps(void)
{
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t ss[CRYPTO_BYTES];

  printf("Encaps... ");
  CHECK(crypto_kem_enc(ct, ss, test_vector_pk) == 0);
  CHECK(memcmp(ct, test_vector_ct, CRYPTO_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss, CRYPTO_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_ENCAPS_API && !MLK_CONFIG_NO_RANDOMIZED_API */
static int example_encaps(void)
{
  printf("Encaps... SKIPPED (encaps API disabled)\n");
  return 0;
}
#endif /* !(!MLK_CONFIG_NO_ENCAPS_API && !MLK_CONFIG_NO_RANDOMIZED_API) */

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
