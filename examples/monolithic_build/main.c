/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mlkem_native.h"

static int test_keys_mlkem512(void)
{
  uint8_t pk[MLKEM512_PUBLICKEYBYTES];
  uint8_t sk[MLKEM512_SECRETKEYBYTES];
  uint8_t ct[MLKEM512_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM512_BYTES];
  uint8_t key_b[MLKEM512_BYTES];

  /* Alice generates a public key */
  mlkem512_keypair(pk, sk);

  /* Bob derives a secret key and creates a response */
  mlkem512_enc(ct, key_b, pk);

  /* Alice uses Bobs response to get her shared key */
  mlkem512_dec(key_a, ct, sk);

  if (memcmp(key_a, key_b, MLKEM512_BYTES))
  {
    printf("[MLKEM-512] ERROR keys\n");
    return 1;
  }

  printf("[MLKEM-512] OK\n");
  return 0;
}

int main(void)
{
  if (test_keys_mlkem512() != 0)
  {
    return 1;
  }

  return 0;
}
