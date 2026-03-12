/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../../mlkem/src/compress.h"
#include "../../mlkem/src/kem.h"
#include "../../mlkem/src/symmetric.h"

#include "../notrandombytes/notrandombytes.h"

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


static int test_keys_core(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                          uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                          uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                          uint8_t key_a[MLKEM_SSBYTES],
                          uint8_t key_b[MLKEM_SSBYTES])
{
  /* Alice generates a public key */
  CHECK(mlk_kem_keypair(pk, sk, 0) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(mlk_kem_enc(ct, key_b, pk, 0) == 0);
  /* Alice uses Bobs response to get her shared key */
  CHECK(mlk_kem_dec(key_a, ct, sk, 0) == 0);

  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, MLKEM_SSBYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, MLKEM_SSBYTES);

  CHECK(memcmp(key_a, key_b, MLKEM_SSBYTES) == 0);
  return 0;
}

static int test_keys(void)
{
  uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES];
  uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES];
  uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM_SSBYTES];
  uint8_t key_b[MLKEM_SSBYTES];
  return test_keys_core(pk, sk, ct, key_a, key_b);
}

static int test_keys_unaligned(void)
{
  MLK_ALIGN uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES + 1];
  MLK_ALIGN uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES + 1];
  MLK_ALIGN uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES + 1];
  MLK_ALIGN uint8_t key_a[MLKEM_SSBYTES + 1];
  MLK_ALIGN uint8_t key_b[MLKEM_SSBYTES + 1];
  return test_keys_core(pk + 1, sk + 1, ct + 1, key_a + 1, key_b + 1);
}

static int test_invalid_pk(void)
{
  uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES];
  uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES];
  uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES];
  uint8_t key_b[MLKEM_SSBYTES];
  /* Alice generates a public key */
  CHECK(mlk_kem_keypair(pk, sk, 0) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(mlk_kem_enc(ct, key_b, pk, 0) == 0);
  /* set first public key coefficient to 4095 (0xFFF) */
  pk[0] = 0xFF;
  pk[1] |= 0x0F;
  /* Bob derives a secret key and creates a response */
  CHECK(mlk_kem_enc(ct, key_b, pk, 0) != 0);
  return 0;
}

static int test_invalid_sk_a(void)
{
  uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES];
  uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES];
  uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM_SSBYTES];
  uint8_t key_b[MLKEM_SSBYTES];
  /* Alice generates a public key */
  CHECK(mlk_kem_keypair(pk, sk, 0) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(mlk_kem_enc(ct, key_b, pk, 0) == 0);
  /* Replace first part of secret key with random values */
  CHECK(randombytes(sk, 10) == 0);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to wrong sk */
  CHECK(mlk_kem_dec(key_a, ct, sk, 0) == 0);
  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, MLKEM_SSBYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, MLKEM_SSBYTES);

  CHECK(memcmp(key_a, key_b, MLKEM_SSBYTES) != 0);
  return 0;
}

static int test_invalid_sk_b(void)
{
  uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES];
  uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES];
  uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM_SSBYTES];
  uint8_t key_b[MLKEM_SSBYTES];
  /* Alice generates a public key */
  CHECK(mlk_kem_keypair(pk, sk, 0) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(mlk_kem_enc(ct, key_b, pk, 0) == 0);
  /* Replace H(pk) with radom values; */
  CHECK(randombytes(sk + MLKEM_INDCCA_SECRETKEYBYTES - 64, 32) == 0);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to the input validation */
  CHECK(mlk_kem_dec(key_a, ct, sk, 0) != 0);
  return 0;
}

static int test_invalid_ciphertext(void)
{
  uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES];
  uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES];
  uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM_SSBYTES];
  uint8_t key_b[MLKEM_SSBYTES];
  uint8_t b;
  size_t pos;

  do
  {
    CHECK(randombytes(&b, sizeof(uint8_t)) == 0);
  } while (!b);
  CHECK(randombytes((uint8_t *)&pos, sizeof(size_t)) == 0);

  /* Alice generates a public key */
  CHECK(mlk_kem_keypair(pk, sk, 0) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(mlk_kem_enc(ct, key_b, pk, 0) == 0);
  /* Change some byte in the ciphertext (i.e., encapsulated key) */
  ct[pos % MLKEM_INDCCA_CIPHERTEXTBYTES] ^= b;
  /* Alice uses Bobs response to get her shared key */
  CHECK(mlk_kem_dec(key_a, ct, sk, 0) == 0);
  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, MLKEM_SSBYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, MLKEM_SSBYTES);
  CHECK(memcmp(key_a, key_b, MLKEM_SSBYTES) != 0);
  return 0;
}

static int test_incremental_enc(void)
{
  uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES];
  uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES];
  uint8_t ct_ref[MLKEM_INDCCA_CIPHERTEXTBYTES];
  uint8_t ss_ref[MLKEM_SSBYTES];
  uint8_t keygen_coins[2 * MLKEM_SYMBYTES];
  uint8_t enc_coins[MLKEM_SYMBYTES];

  /* Incremental outputs */
  uint8_t ct_u[MLKEM_POLYVECCOMPRESSEDBYTES_DU];
  uint8_t ct_v[MLKEM_POLYCOMPRESSEDBYTES_DV];
  uint8_t ss[MLKEM_SSBYTES];
  uint8_t sp_serial[MLKEM_POLYVEC16_BYTES];
  uint8_t epp_serial[MLKEM_EPP_BYTES];

  uint8_t hpk[MLKEM_SYMBYTES];
  const uint8_t *ek_vector;
  const uint8_t *ek_seed;

  /* Generate deterministic coins */
  CHECK(randombytes(keygen_coins, 2 * MLKEM_SYMBYTES) == 0);
  CHECK(randombytes(enc_coins, MLKEM_SYMBYTES) == 0);

  /* Standard keygen + encaps (reference) */
  CHECK(mlk_kem_keypair_derand(pk, sk, keygen_coins, 0) == 0);
  CHECK(mlk_kem_enc_derand(ct_ref, ss_ref, pk, enc_coins, 0) == 0);

  /* Split pk: pk = ek_vector || ek_seed */
  ek_vector = pk;
  ek_seed = pk + MLKEM_POLYVECBYTES;

  /* Compute H(pk) for incremental API */
  mlk_hash_h(hpk, pk, MLKEM_INDCCA_PUBLICKEYBYTES);

  /* Incremental encapsulation via KEM-level API */
  CHECK(mlk_kem_enc_derand_u(ct_u, ss, sp_serial, epp_serial, ek_seed, hpk,
                             enc_coins, 0) == 0);
  CHECK(mlk_kem_enc_v(ct_v, sp_serial, epp_serial, enc_coins, ek_vector, 0) ==
        0);

  /* Verify ct_u || ct_v matches reference ciphertext */
  MLK_CT_TESTING_DECLASSIFY(ct_u, MLKEM_POLYVECCOMPRESSEDBYTES_DU);
  MLK_CT_TESTING_DECLASSIFY(ct_v, MLKEM_POLYCOMPRESSEDBYTES_DV);
  MLK_CT_TESTING_DECLASSIFY(ct_ref, MLKEM_INDCCA_CIPHERTEXTBYTES);

  CHECK(memcmp(ct_u, ct_ref, MLKEM_POLYVECCOMPRESSEDBYTES_DU) == 0);
  CHECK(memcmp(ct_v, ct_ref + MLKEM_POLYVECCOMPRESSEDBYTES_DU,
               MLKEM_POLYCOMPRESSEDBYTES_DV) == 0);

  /* Verify shared secret matches */
  MLK_CT_TESTING_DECLASSIFY(ss, MLKEM_SSBYTES);
  MLK_CT_TESTING_DECLASSIFY(ss_ref, MLKEM_SSBYTES);
  CHECK(memcmp(ss, ss_ref, MLKEM_SSBYTES) == 0);

  /* Verify decaps works with reassembled ciphertext */
  {
    uint8_t ct_combined[MLKEM_INDCCA_CIPHERTEXTBYTES];
    uint8_t ss_dec[MLKEM_SSBYTES];
    memcpy(ct_combined, ct_u, MLKEM_POLYVECCOMPRESSEDBYTES_DU);
    memcpy(ct_combined + MLKEM_POLYVECCOMPRESSEDBYTES_DU, ct_v,
           MLKEM_POLYCOMPRESSEDBYTES_DV);
    CHECK(mlk_kem_dec(ss_dec, ct_combined, sk, 0) == 0);
    MLK_CT_TESTING_DECLASSIFY(ss_dec, MLKEM_SSBYTES);
    CHECK(memcmp(ss_dec, ss, MLKEM_SSBYTES) == 0);
  }

  return 0;
}

int main(void)
{
  unsigned i;

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  for (i = 0; i < NTESTS_FUNC; i++)
  {
    CHECK(test_keys() == 0);
    CHECK(test_keys_unaligned() == 0);
    CHECK(test_invalid_pk() == 0);
    CHECK(test_invalid_sk_a() == 0);
    CHECK(test_invalid_sk_b() == 0);
    CHECK(test_invalid_ciphertext() == 0);
    CHECK(test_incremental_enc() == 0);
  }

  printf("MLKEM_INDCCA_SECRETKEYBYTES:  %d\n", MLKEM_INDCCA_SECRETKEYBYTES);
  printf("MLKEM_INDCCA_PUBLICKEYBYTES:  %d\n", MLKEM_INDCCA_PUBLICKEYBYTES);
  printf("MLKEM_INDCCA_CIPHERTEXTBYTES: %d\n", MLKEM_INDCCA_CIPHERTEXTBYTES);

  return 0;
}
