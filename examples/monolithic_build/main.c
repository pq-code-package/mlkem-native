/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mlkem_native.h"

static int test_keys_mlkem(void)
{
  uint8_t pk[MLKEM_PUBLICKEYBYTES(BUILD_INFO_LVL)];
  uint8_t sk[MLKEM_SECRETKEYBYTES(BUILD_INFO_LVL)];
  uint8_t ct[MLKEM_CIPHERTEXTBYTES(BUILD_INFO_LVL)];
  uint8_t key_a[MLKEM_BYTES];
  uint8_t key_b[MLKEM_BYTES];

  /* Alice generates a public key */
  mlkem_keypair(pk, sk);

  /* Bob derives a secret key and creates a response */
  mlkem_enc(ct, key_b, pk);

  /* Alice uses Bobs response to get her shared key */
  mlkem_dec(key_a, ct, sk);

  if (memcmp(key_a, key_b, MLKEM_BYTES))
  {
    printf("[MLKEM] ERROR keys\n");
    return 1;
  }

  printf("[MLKEM-%d] OK\n", BUILD_INFO_LVL);
  return 0;
}

int main(void)
{
  if (test_keys_mlkem() != 0)
  {
    return 1;
  }

  return 0;
}
