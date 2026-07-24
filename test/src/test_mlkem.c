/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../../mlkem/src/compress.h"

#include "../../mlkem/mlkem_native.h"
#include "../notrandombytes/notrandombytes.h"
#include "../test_vectors/expected_test_vectors.h"

#ifndef NTESTS_FUNC
#define NTESTS_FUNC 1000
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


#if !defined(MLK_CONFIG_NO_KEYPAIR_API) && \
    !defined(MLK_CONFIG_NO_ENCAPS_API) && !defined(MLK_CONFIG_NO_DECAPS_API)
/* Force out-of-line so the ~6.4KB of stack buffers below stay in short-lived
 * frames and don't stack up in main() -- crucial on memory-constrained
 * targets such as AVR. */
static MLK_NOINLINE int test_keys_core(uint8_t pk[CRYPTO_PUBLICKEYBYTES],
                                       uint8_t sk[CRYPTO_SECRETKEYBYTES],
                                       uint8_t ct[CRYPTO_CIPHERTEXTBYTES],
                                       uint8_t key_a[CRYPTO_BYTES],
                                       uint8_t key_b[CRYPTO_BYTES])
{
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

static MLK_NOINLINE int test_keys(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  return test_keys_core(pk, sk, ct, key_a, key_b);
}

static MLK_NOINLINE int test_keys_unaligned(void)
{
  MLK_ALIGN uint8_t pk[CRYPTO_PUBLICKEYBYTES + 1];
  MLK_ALIGN uint8_t sk[CRYPTO_SECRETKEYBYTES + 1];
  MLK_ALIGN uint8_t ct[CRYPTO_CIPHERTEXTBYTES + 1];
  MLK_ALIGN uint8_t key_a[CRYPTO_BYTES + 1];
  MLK_ALIGN uint8_t key_b[CRYPTO_BYTES + 1];
  return test_keys_core(pk + 1, sk + 1, ct + 1, key_a + 1, key_b + 1);
}

static MLK_NOINLINE int test_invalid_pk(void)
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

static MLK_NOINLINE int test_invalid_sk_a(void)
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
  CHECK(randombytes(sk, 10) == 0);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to wrong sk */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);
  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, CRYPTO_BYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, CRYPTO_BYTES);

  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) != 0);
  return 0;
}

static MLK_NOINLINE int test_invalid_sk_b(void)
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
  CHECK(randombytes(sk + CRYPTO_SECRETKEYBYTES - 64, 32) == 0);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to the input validation */
  CHECK(crypto_kem_dec(key_a, ct, sk) != 0);
  return 0;
}

static MLK_NOINLINE int test_invalid_ciphertext(void)
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
    CHECK(randombytes(&b, sizeof(uint8_t)) == 0);
  } while (!b);
  CHECK(randombytes((uint8_t *)&pos, sizeof(size_t)) == 0);

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
#endif /* !MLK_CONFIG_NO_KEYPAIR_API && !MLK_CONFIG_NO_ENCAPS_API && \
          !MLK_CONFIG_NO_DECAPS_API */

/*
 * Test each API operation independently against pre-computed test vectors.
 * Compatible with reduced-API configurations. Each API's test is a
 * MLK_NOINLINE function so that its large key buffers stay in short-lived
 * frames -- this reduces peak stack usage on memory-constrained targets
 * such as AVR.
 */
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
static MLK_NOINLINE int test_kem_expected_keygen(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];
  uint8_t test_vector_sk_copy[CRYPTO_SECRETKEYBYTES];

  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);

  CHECK(crypto_kem_keypair_derand(pk, sk, coins) == 0);

  /* Declassify the generated sk and a copy of test_vector_sk so we can
   * memcmp them; the underlying test_vector_sk stays SECRET so it can
   * still be used as a CT-sensitive input in the decaps block. */
  MLK_CT_TESTING_DECLASSIFY(sk, CRYPTO_SECRETKEYBYTES);
  memcpy(test_vector_sk_copy, test_vector_sk, CRYPTO_SECRETKEYBYTES);
  MLK_CT_TESTING_DECLASSIFY(test_vector_sk_copy, CRYPTO_SECRETKEYBYTES);

  CHECK(memcmp(pk, test_vector_pk, CRYPTO_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk_copy, CRYPTO_SECRETKEYBYTES) == 0);
  return 0;
}
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static MLK_NOINLINE int test_kem_expected_encaps(void)
{
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t ss[CRYPTO_BYTES];

  CHECK(crypto_kem_enc_derand(ct, ss, test_vector_pk, test_vector_m) == 0);

  MLK_CT_TESTING_DECLASSIFY(ct, CRYPTO_CIPHERTEXTBYTES);
  MLK_CT_TESTING_DECLASSIFY(ss, CRYPTO_BYTES);

  CHECK(memcmp(ct, test_vector_ct, CRYPTO_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss, CRYPTO_BYTES) == 0);
  return 0;
}
#endif /* !MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static MLK_NOINLINE int test_kem_expected_decaps(void)
{
  uint8_t ss[CRYPTO_BYTES];

  CHECK(crypto_kem_dec(ss, test_vector_ct, test_vector_sk) == 0);

  MLK_CT_TESTING_DECLASSIFY(ss, CRYPTO_BYTES);
  CHECK(memcmp(ss, test_vector_ss, CRYPTO_BYTES) == 0);
  return 0;
}
#endif /* !MLK_CONFIG_NO_DECAPS_API */

static int test_kem_expected(void)
{
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
  if (test_kem_expected_keygen() != 0)
  {
    return 1;
  }
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */
#if !defined(MLK_CONFIG_NO_ENCAPS_API)
  if (test_kem_expected_encaps() != 0)
  {
    return 1;
  }
#endif /* !MLK_CONFIG_NO_ENCAPS_API */
#if !defined(MLK_CONFIG_NO_DECAPS_API)
  if (test_kem_expected_decaps() != 0)
  {
    return 1;
  }
#endif /* !MLK_CONFIG_NO_DECAPS_API */
  return 0;
}

/* Prototype for a re-#define'd main, to satisfy -Wmissing-prototypes. */
#if defined(main)
int main(void);
#endif
int main(void)
{
  unsigned i;
  int r;

  /* Fixed test-vector smoke test: exercises whichever of keygen/encaps/decaps
   * are enabled against pre-computed vectors. Mark public test vectors
   * DECLASSIFIED and the secret key test vector SECRET so valgrind CT
   * testing sees the same taint model as production usage. */
  MLK_CT_TESTING_DECLASSIFY(test_vector_pk, CRYPTO_PUBLICKEYBYTES);
  MLK_CT_TESTING_DECLASSIFY(test_vector_ct, CRYPTO_CIPHERTEXTBYTES);
  MLK_CT_TESTING_SECRET(test_vector_sk, CRYPTO_SECRETKEYBYTES);

  if (test_kem_expected() != 0)
  {
    return 1;
  }

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  for (i = 0; i < NTESTS_FUNC; i++)
  {
    r = 0;
#if !defined(MLK_CONFIG_NO_KEYPAIR_API) && \
    !defined(MLK_CONFIG_NO_ENCAPS_API) && !defined(MLK_CONFIG_NO_DECAPS_API)
    r |= test_keys();
    r |= test_keys_unaligned();
    r |= test_invalid_pk();
    r |= test_invalid_sk_a();
    r |= test_invalid_sk_b();
    r |= test_invalid_ciphertext();
#endif /* !MLK_CONFIG_NO_KEYPAIR_API && !MLK_CONFIG_NO_ENCAPS_API && \
          !MLK_CONFIG_NO_DECAPS_API */
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
