/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <string.h>

#include <mlkem_native.h>

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
    printf("ERROR\n");
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
