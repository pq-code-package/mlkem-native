/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../mlkem/fips202/fips202.h"
#include "../mlkem/mlkem_native.h"

#define NTESTS 1000

static void print_hex(const char *label, const uint8_t *data, size_t size)
{
  size_t i;
  printf("%s = ", label);
  for (i = 0; i < size; i++)
  {
    printf("%02x", data[i]);
  }
  printf("\n");
}

int main(void)
{
  unsigned int i;
  ALIGN uint8_t coins[3 * CRYPTO_SYMBYTES];
  ALIGN uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  ALIGN uint8_t sk[CRYPTO_SECRETKEYBYTES];
  ALIGN uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  ALIGN uint8_t ss1[CRYPTO_BYTES];
  ALIGN uint8_t ss2[CRYPTO_BYTES];

  const uint8_t seed[64] = {
      32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
      64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
      80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
  };
  shake256(coins, sizeof(coins), seed, sizeof(seed));

  for (i = 0; i < NTESTS; i++)
  {
    shake256(coins, sizeof(coins), coins, sizeof(coins));

    crypto_kem_keypair_derand(pk, sk, coins);
    print_hex("pk", pk, sizeof(pk));
    print_hex("sk", sk, sizeof(sk));

    crypto_kem_enc_derand(ct, ss1, pk, coins + 2 * MLKEM_SYMBYTES);
    print_hex("ct", ct, sizeof(ct));

    crypto_kem_dec(ss2, ct, sk);

    if (memcmp(ss1, ss2, sizeof(ss1)))
    {
      fprintf(stderr, "ERROR\n");
      return -1;
    }

    print_hex("ss", ss1, sizeof(ss1));
  }

  return 0;
}
