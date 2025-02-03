/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mlkem_native_all.h"

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

static int test_keys_mlkem768(void)
{
  uint8_t pk[MLKEM768_PUBLICKEYBYTES];
  uint8_t sk[MLKEM768_SECRETKEYBYTES];
  uint8_t ct[MLKEM768_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM768_BYTES];
  uint8_t key_b[MLKEM768_BYTES];

  /* Alice generates a public key */
  mlkem768_keypair(pk, sk);

  /* Bob derives a secret key and creates a response */
  mlkem768_enc(ct, key_b, pk);

  /* Alice uses Bobs response to get her shared key */
  mlkem768_dec(key_a, ct, sk);

  if (memcmp(key_a, key_b, MLKEM768_BYTES))
  {
    printf("[MLKEM-768] ERROR keys\n");
    return 1;
  }

  printf("[MLKEM-768] OK\n");
  return 0;
}

static int test_keys_mlkem1024(void)
{
  uint8_t pk[MLKEM1024_PUBLICKEYBYTES];
  uint8_t sk[MLKEM1024_SECRETKEYBYTES];
  uint8_t ct[MLKEM1024_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM1024_BYTES];
  uint8_t key_b[MLKEM1024_BYTES];

  /* Alice generates a public key */
  mlkem1024_keypair(pk, sk);

  /* Bob derives a secret key and creates a response */
  mlkem1024_enc(ct, key_b, pk);

  /* Alice uses Bobs response to get her shared key */
  mlkem1024_dec(key_a, ct, sk);

  if (memcmp(key_a, key_b, MLKEM1024_BYTES))
  {
    printf("[MLKEM-1024] ERROR keys\n");
    return 1;
  }

  printf("[MLKEM-1024] OK\n");
  return 0;
}

int main(void)
{
  if (test_keys_mlkem512() != 0)
  {
    return 1;
  }

  if (test_keys_mlkem768() != 0)
  {
    return 1;
  }

  if (test_keys_mlkem1024() != 0)
  {
    return 1;
  }

  return 0;
}
