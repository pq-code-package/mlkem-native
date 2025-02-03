/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <string.h>

#include <mlkem_native.h>
#include "test_only_rng/notrandombytes.h"

int main(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];

#if MLKEM_K == 2
  const uint8_t expected_key[] = {
      0x77, 0x6c, 0x74, 0xdf, 0x30, 0x1f, 0x8d, 0x82, 0x52, 0x5e, 0x8e,
      0xbb, 0xb4, 0x00, 0x95, 0xcd, 0x2e, 0x92, 0xdf, 0x6d, 0xc9, 0x33,
      0xe7, 0x86, 0x62, 0x59, 0xf5, 0x31, 0xc7, 0x35, 0x0a, 0xd5};
#elif MLKEM_K == 3
  const uint8_t expected_key[] = {
      0xe9, 0x13, 0x77, 0x84, 0x0e, 0x6b, 0x66, 0x94, 0xea, 0xa9, 0xf0,
      0x1c, 0x97, 0xff, 0x68, 0x87, 0x4e, 0x8b, 0x0c, 0x52, 0x0b, 0x00,
      0xc2, 0xcd, 0xe3, 0x7c, 0x4f, 0xc2, 0x39, 0x62, 0x6e, 0x70};
#elif MLKEM_K == 4
  const uint8_t expected_key[] = {
      0x5d, 0x9e, 0x23, 0x5f, 0xcc, 0xb2, 0xb3, 0x49, 0x9a, 0x5f, 0x49,
      0x0a, 0x56, 0xe3, 0xf0, 0xd3, 0xfd, 0x9b, 0x58, 0xbd, 0xa2, 0x8b,
      0x69, 0x0f, 0x91, 0xb5, 0x7b, 0x88, 0xa5, 0xa8, 0x0b, 0x90};
#endif

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  printf("Generating keypair ... ");

  /* Alice generates a public key */
  crypto_kem_keypair(pk, sk);

  printf("DONE\n");
  printf("Encaps... ");

  /* Bob derives a secret key and creates a response */
  crypto_kem_enc(ct, key_b, pk);

  printf("DONE\n");
  printf("Decaps... ");

  /* Alice uses Bobs response to get her shared key */
  crypto_kem_dec(key_a, ct, sk);

  printf("DONE\n");
  printf("Compare... ");

  if (memcmp(key_a, key_b, CRYPTO_BYTES))
  {
    printf("ERROR: Mismatching keys\n");
    return 1;
  }

  printf("Shared secret: ");
  {
    size_t i;
    for (i = 0; i < sizeof(key_a); i++)
      printf("%02x", key_a[i]);
  }
  printf("\n");

  /* Check against hardcoded result to make sure that
   * we integrated custom FIPS202 correctly */
  if (memcmp(key_a, expected_key, CRYPTO_BYTES) != 0)
  {
    printf("ERROR: Unexpected result\n");
    return 1;
  }

  printf("OK\n");

  return 0;
}
