/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <string.h>

#include <mlkem_native.h>

const uint8_t expected_key[] = {0xe9, 0x13, 0x77, 0x84, 0x0e, 0x6b, 0x66, 0x94,
                                0xea, 0xa9, 0xf0, 0x1c, 0x97, 0xff, 0x68, 0x87,
                                0x4e, 0x8b, 0x0c, 0x52, 0x0b, 0x00, 0xc2, 0xcd,
                                0xe3, 0x7c, 0x4f, 0xc2, 0x39, 0x62, 0x6e, 0x70};

int main(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];

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

  /* Check against hardcoded result to make sure that
   * we integrated custom FIPS202 correctly */
  if (memcmp(key_a, expected_key, CRYPTO_BYTES) != 0)
  {
    printf("ERROR: Unexpected result\n");
    return 1;
  }

  printf("OK\n");

  printf("Shared secret: ");
  {
    int i;
    for (i = 0; i < sizeof(key_a); i++)
      printf("%02x", key_a[i]);
  }
  printf("\n");

  return 0;
}
