/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mlkem_native_all.h"
#include "test_only_rng/notrandombytes.h"

static int test_keys_mlkem512(void)
{
  const uint8_t expected_key[] = {
      0x77, 0x6c, 0x74, 0xdf, 0x30, 0x1f, 0x8d, 0x82, 0x52, 0x5e, 0x8e,
      0xbb, 0xb4, 0x00, 0x95, 0xcd, 0x2e, 0x92, 0xdf, 0x6d, 0xc9, 0x33,
      0xe7, 0x86, 0x62, 0x59, 0xf5, 0x31, 0xc7, 0x35, 0x0a, 0xd5};

  uint8_t pk[MLKEM512_PUBLICKEYBYTES];
  uint8_t sk[MLKEM512_SECRETKEYBYTES];
  uint8_t ct[MLKEM512_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM512_BYTES];
  uint8_t key_b[MLKEM512_BYTES];

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

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

  printf("Shared secret: ");
  {
    size_t i;
    for (i = 0; i < sizeof(key_a); i++)
      printf("%02x", key_a[i]);
  }
  printf("\n");

  if (memcmp(key_a, expected_key, sizeof(key_a)) != 0)
  {
    printf("ERROR: Unexpected result\n");
    return 1;
  }

  printf("[MLKEM-512] OK\n");
  return 0;
}

static int test_keys_mlkem768(void)
{
  const uint8_t expected_key[] = {
      0xe9, 0x13, 0x77, 0x84, 0x0e, 0x6b, 0x66, 0x94, 0xea, 0xa9, 0xf0,
      0x1c, 0x97, 0xff, 0x68, 0x87, 0x4e, 0x8b, 0x0c, 0x52, 0x0b, 0x00,
      0xc2, 0xcd, 0xe3, 0x7c, 0x4f, 0xc2, 0x39, 0x62, 0x6e, 0x70};

  uint8_t pk[MLKEM768_PUBLICKEYBYTES];
  uint8_t sk[MLKEM768_SECRETKEYBYTES];
  uint8_t ct[MLKEM768_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM768_BYTES];
  uint8_t key_b[MLKEM768_BYTES];

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

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

  printf("Shared secret: ");
  {
    size_t i;
    for (i = 0; i < sizeof(key_a); i++)
      printf("%02x", key_a[i]);
  }
  printf("\n");

  if (memcmp(key_a, expected_key, sizeof(key_a)) != 0)
  {
    printf("ERROR: Unexpected result\n");
    return 1;
  }

  printf("[MLKEM-768] OK\n");
  return 0;
}

static int test_keys_mlkem1024(void)
{
  const uint8_t expected_key[] = {
      0x5d, 0x9e, 0x23, 0x5f, 0xcc, 0xb2, 0xb3, 0x49, 0x9a, 0x5f, 0x49,
      0x0a, 0x56, 0xe3, 0xf0, 0xd3, 0xfd, 0x9b, 0x58, 0xbd, 0xa2, 0x8b,
      0x69, 0x0f, 0x91, 0xb5, 0x7b, 0x88, 0xa5, 0xa8, 0x0b, 0x90};

  uint8_t pk[MLKEM1024_PUBLICKEYBYTES];
  uint8_t sk[MLKEM1024_SECRETKEYBYTES];
  uint8_t ct[MLKEM1024_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM1024_BYTES];
  uint8_t key_b[MLKEM1024_BYTES];

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

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

  printf("Shared secret: ");
  {
    size_t i;
    for (i = 0; i < sizeof(key_a); i++)
      printf("%02x", key_a[i]);
  }
  printf("\n");

  if (memcmp(key_a, expected_key, sizeof(key_a)) != 0)
  {
    printf("ERROR: Unexpected result\n");
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
