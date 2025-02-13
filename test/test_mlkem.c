/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../mlkem/compress.h"
#include "../mlkem/mlkem_native.h"

#include "notrandombytes/notrandombytes.h"

#ifndef NTESTS
#define NTESTS 1000
#endif

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


static int test_keys(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];

  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Alice uses Bobs response to get her shared key */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);

  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, CRYPTO_BYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, CRYPTO_BYTES);

  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) == 0);
  return 0;
}

static int test_invalid_pk(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_b[CRYPTO_BYTES];
  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* set first public key coefficient to 4095 (0xFFF) */
  pk[0] = 0xFF;
  pk[1] |= 0x0F;
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) != 0);
  return 0;
}

static int test_invalid_sk_a(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Replace first part of secret key with random values */
  randombytes(sk, 10);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to wrong sk */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);
  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, CRYPTO_BYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, CRYPTO_BYTES);

  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) != 0);
  return 0;
}

static int test_invalid_sk_b(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Replace H(pk) with radom values; */
  randombytes(sk + CRYPTO_SECRETKEYBYTES - 64, 32);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to the input validation */
  CHECK(crypto_kem_dec(key_a, ct, sk) != 0);
  return 0;
}

static int test_invalid_ciphertext(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  uint8_t b;
  size_t pos;

  do
  {
    randombytes(&b, sizeof(uint8_t));
    MLK_CT_TESTING_DECLASSIFY(&b, sizeof(uint8_t));
  } while (!b);
  randombytes((uint8_t *)&pos, sizeof(size_t));

  MLK_CT_TESTING_DECLASSIFY(&pos, sizeof(size_t));

  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Change some byte in the ciphertext (i.e., encapsulated key) */
  ct[pos % CRYPTO_CIPHERTEXTBYTES] ^= b;
  /* Alice uses Bobs response to get her shared key */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);
  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, CRYPTO_BYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, CRYPTO_BYTES);
  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) != 0);
  return 0;
}

/* This test invokes the polynomial (de)compression routines
 * with minimally sized buffers. When run with address sanitization,
 * this ensures that no buffer overflow is happening. This is of interest
 * because the compressed buffers sometimes have unaligned lengths and
 * are therefore at risk of being overflowed by vectorized code. */
static int test_poly_compress_no_overflow(void)
{
#if defined(MLK_MULTILEVEL_BUILD_WITH_SHARED) || (MLKEM_K == 2 || MLKEM_K == 3)
  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4];
    poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    poly_compress_d4(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4];
    poly s;
    memset(r, 0, sizeof(r));
    poly_decompress_d4(&s, r);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10];
    poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    poly_compress_d10(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10];
    poly s;
    memset(r, 0, sizeof(r));
    poly_decompress_d10(&s, r);
  }
#endif /* defined(MLK_MULTILEVEL_BUILD_WITH_SHARED) || (MLKEM_K == 2 \
          || MLKEM_K == 3) */

#if defined(MLK_MULTILEVEL_BUILD_WITH_SHARED) || MLKEM_K == 4
  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5];
    poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    poly_compress_d5(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5];
    poly s;
    memset(r, 0, sizeof(r));
    poly_decompress_d5(&s, r);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11];
    poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    poly_compress_d11(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11];
    poly s;
    memset(r, 0, sizeof(r));
    poly_decompress_d11(&s, r);
  }
#endif /* MLK_MULTILEVEL_BUILD_WITH_SHARED || MLKEM_K == 4 */

  return 0;
}

int main(void)
{
  unsigned i;

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  for (i = 0; i < NTESTS; i++)
  {
    CHECK(test_keys() == 0);
    CHECK(test_invalid_pk() == 0);
    CHECK(test_invalid_sk_a() == 0);
    CHECK(test_invalid_sk_b() == 0);
    CHECK(test_invalid_ciphertext() == 0);
    CHECK(test_poly_compress_no_overflow() == 0);
  }

  printf("CRYPTO_SECRETKEYBYTES:  %d\n", CRYPTO_SECRETKEYBYTES);
  printf("CRYPTO_PUBLICKEYBYTES:  %d\n", CRYPTO_PUBLICKEYBYTES);
  printf("CRYPTO_CIPHERTEXTBYTES: %d\n", CRYPTO_CIPHERTEXTBYTES);

  return 0;
}
