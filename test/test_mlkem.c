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

#ifdef ENABLE_CT_TESTING
#include <valgrind/memcheck.h>
#endif

#ifndef NTESTS
#define NTESTS 1000
#endif

static int test_keys(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];

  /* Alice generates a public key */
  crypto_kem_keypair(pk, sk);

#ifdef ENABLE_CT_TESTING
  /* mark public key as public (=defined) */
  VALGRIND_MAKE_MEM_DEFINED(pk, CRYPTO_PUBLICKEYBYTES);
#endif

  /* Bob derives a secret key and creates a response */
  crypto_kem_enc(ct, key_b, pk);

  /* Alice uses Bobs response to get her shared key */
  crypto_kem_dec(key_a, ct, sk);

#ifdef ENABLE_CT_TESTING
  /* mark as defined, so we can compare */
  VALGRIND_MAKE_MEM_DEFINED(key_a, CRYPTO_BYTES);
  VALGRIND_MAKE_MEM_DEFINED(key_b, CRYPTO_BYTES);
#endif

  if (memcmp(key_a, key_b, CRYPTO_BYTES))
  {
    printf("ERROR keys\n");
    return 1;
  }

  return 0;
}

static int test_invalid_pk(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_b[CRYPTO_BYTES];
  int rc;
  /* Alice generates a public key */
  crypto_kem_keypair(pk, sk);

#ifdef ENABLE_CT_TESTING
  /* mark public key as public (=defined) */
  VALGRIND_MAKE_MEM_DEFINED(pk, CRYPTO_PUBLICKEYBYTES);
#endif

  /* Bob derives a secret key and creates a response */
  rc = crypto_kem_enc(ct, key_b, pk);

  if (rc)
  {
    printf("ERROR test_invalid_pk\n");
    return 1;
  }

  /* set first public key coefficient to 4095 (0xFFF) */
  pk[0] = 0xFF;
  pk[1] |= 0x0F;
  /* Bob derives a secret key and creates a response */
  rc = crypto_kem_enc(ct, key_b, pk);

  if (!rc)
  {
    printf("ERROR test_invalid_pk\n");
    return 1;
  }
  return 0;
}

static int test_invalid_sk_a(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  int rc;

  /* Alice generates a public key */
  crypto_kem_keypair(pk, sk);

#ifdef ENABLE_CT_TESTING
  /* mark public key as public (=defined) */
  VALGRIND_MAKE_MEM_DEFINED(pk, CRYPTO_PUBLICKEYBYTES);
#endif

  /* Bob derives a secret key and creates a response */
  crypto_kem_enc(ct, key_b, pk);

  /* Replace first part of secret key with random values */
  randombytes(sk, 10);

  /*
   * Alice uses Bobs response to get her shared key
   * This should fail due to wrong sk
   */
  rc = crypto_kem_dec(key_a, ct, sk);
  if (rc)
  {
    printf("ERROR test_invalid_sk_a\n");
    return 1;
  }

#ifdef ENABLE_CT_TESTING
  /* mark as defined, so we can compare */
  VALGRIND_MAKE_MEM_DEFINED(key_a, CRYPTO_BYTES);
  VALGRIND_MAKE_MEM_DEFINED(key_b, CRYPTO_BYTES);
#endif

  if (!memcmp(key_a, key_b, CRYPTO_BYTES))
  {
    printf("ERROR invalid sk\n");
    return 1;
  }

  return 0;
}

static int test_invalid_sk_b(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  int rc;

  /* Alice generates a public key */
  crypto_kem_keypair(pk, sk);

#ifdef ENABLE_CT_TESTING
  /* mark public key as public (=defined) */
  VALGRIND_MAKE_MEM_DEFINED(pk, CRYPTO_PUBLICKEYBYTES);
#endif

  /* Bob derives a secret key and creates a response */
  crypto_kem_enc(ct, key_b, pk);

  /* Replace H(pk) with radom values; */
  randombytes(sk + CRYPTO_SECRETKEYBYTES - 64, 32);

  /*
   * Alice uses Bobs response to get her shared key
   * This should fail due to the input validation
   */
  rc = crypto_kem_dec(key_a, ct, sk);
  if (!rc)
  {
    printf("ERROR test_invalid_sk_b\n");
    return 1;
  }

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

#ifdef ENABLE_CT_TESTING
    VALGRIND_MAKE_MEM_DEFINED(&b, sizeof(uint8_t));
#endif
  } while (!b);
  randombytes((uint8_t *)&pos, sizeof(size_t));


#ifdef ENABLE_CT_TESTING
  VALGRIND_MAKE_MEM_DEFINED(&pos, sizeof(size_t));
#endif

  /* Alice generates a public key */
  crypto_kem_keypair(pk, sk);

#ifdef ENABLE_CT_TESTING
  /* mark public key as public (=defined) */
  VALGRIND_MAKE_MEM_DEFINED(pk, CRYPTO_PUBLICKEYBYTES);
#endif

  /* Bob derives a secret key and creates a response */
  crypto_kem_enc(ct, key_b, pk);

  /* Change some byte in the ciphertext (i.e., encapsulated key) */
  ct[pos % CRYPTO_CIPHERTEXTBYTES] ^= b;

  /* Alice uses Bobs response to get her shared key */
  crypto_kem_dec(key_a, ct, sk);

#ifdef ENABLE_CT_TESTING
  /* mark as defined, so we can compare */
  VALGRIND_MAKE_MEM_DEFINED(key_a, CRYPTO_BYTES);
  VALGRIND_MAKE_MEM_DEFINED(key_b, CRYPTO_BYTES);
#endif

  if (!memcmp(key_a, key_b, CRYPTO_BYTES))
  {
    printf("ERROR invalid ciphertext\n");
    return 1;
  }

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
  int r;

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  for (i = 0; i < NTESTS; i++)
  {
    r = test_keys();
    r |= test_invalid_pk();
    r |= test_invalid_sk_a();
    r |= test_invalid_sk_b();
    r |= test_invalid_ciphertext();
    r |= test_poly_compress_no_overflow();
    if (r)
    {
      return 1;
    }
  }

  printf("CRYPTO_SECRETKEYBYTES:  %d\n", CRYPTO_SECRETKEYBYTES);
  printf("CRYPTO_PUBLICKEYBYTES:  %d\n", CRYPTO_PUBLICKEYBYTES);
  printf("CRYPTO_CIPHERTEXTBYTES: %d\n", CRYPTO_CIPHERTEXTBYTES);

  return 0;
}
