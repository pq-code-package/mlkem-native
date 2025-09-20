/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include <string.h>

/* Import public mlkem-native API
 *
 * This requires specifying the parameter set and namespace prefix
 * used for the build.
 */
#define MLK_CONFIG_API_PARAMETER_SET MLK_CONFIG_PARAMETER_SET
#define MLK_CONFIG_API_NAMESPACE_PREFIX mlkem
#include "mlkem_native/mlkem/mlkem_native.h"

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

int main(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  uint8_t alice_en[2 * MLKEM_SYMBYTES] = {0};
  uint8_t bob_en[MLKEM_SYMBYTES] = {1};


  /* The PCT modifies the PRNG state, so the KAT tests don't work.
   * We run KAT tests only for disabled PCT.
   * Expected keys are generated using deterministic entropy:
   * keypair uses all-zero entropy {0}, enc uses all-one entropy {1} */
#if !defined(MLK_CONFIG_KEYGEN_PCT)
#if MLK_CONFIG_PARAMETER_SET == 512
  const uint8_t expected_key[] = {
      0x5f, 0x5f, 0x8c, 0xf5, 0x7c, 0x34, 0xd4, 0x68, 0x06, 0xa2, 0xe9,
      0xc9, 0x28, 0xba, 0x10, 0x5a, 0x46, 0xf2, 0x67, 0x1a, 0xc7, 0x81,
      0xdf, 0xf1, 0x4a, 0xbb, 0x27, 0xea, 0x46, 0x06, 0x46, 0x3c};
#elif MLK_CONFIG_PARAMETER_SET == 768
  const uint8_t expected_key[] = {
      0x85, 0x21, 0xab, 0xc8, 0x14, 0xc7, 0x67, 0x70, 0x4f, 0xa6, 0x25,
      0xd9, 0x35, 0x95, 0xd0, 0x03, 0x79, 0xa8, 0xb3, 0x70, 0x35, 0x2c,
      0xa4, 0xba, 0xb3, 0xa6, 0x82, 0x46, 0x63, 0x0d, 0xb0, 0x8b};
#elif MLK_CONFIG_PARAMETER_SET == 1024
  const uint8_t expected_key[] = {
      0x30, 0x4d, 0xbe, 0x54, 0xd6, 0x6f, 0x80, 0x66, 0xc6, 0xa8, 0x1c,
      0x6b, 0x36, 0xc4, 0x48, 0x9b, 0xf9, 0xe6, 0x05, 0x79, 0x83, 0x3c,
      0x4e, 0xdc, 0x8a, 0xc7, 0x92, 0xe5, 0x73, 0x0d, 0xdd, 0x85};
#endif /* MLK_CONFIG_PARAMETER_SET == 1024 */
#endif /* !MLK_CONFIG_KEYGEN_PCT */

  /* No randombytes_reset() needed for deterministic API */

  printf("Generating keypair ... ");

  /* Alice generates a public key using deterministic API with all-zero entropy
   */
  CHECK(crypto_kem_keypair_derand(pk, sk, alice_en) == 0);

  printf("DONE\n");
  printf("Encaps... ");

  /* Bob derives a secret key and creates a response using deterministic API
   * with all-one entropy */
  CHECK(crypto_kem_enc_derand(ct, key_b, pk, bob_en) == 0);

  printf("DONE\n");
  printf("Decaps... ");

  /* Alice uses Bobs response to get her shared key */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);

  printf("DONE\n");
  printf("Compare... ");

  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) == 0);

  printf("Shared secret: ");
  {
    size_t i;
    for (i = 0; i < sizeof(key_a); i++)
    {
      printf("%02x", key_a[i]);
    }
  }
  printf("\n");

  /* Check against hardcoded result to make sure that
   * we integrated custom FIPS202 correctly */
  CHECK(memcmp(key_a, expected_key, CRYPTO_BYTES) == 0);


  printf("OK\n");
  return 0;
}
