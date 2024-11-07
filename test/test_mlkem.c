// SPDX-License-Identifier: Apache-2.0
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "kem.h"
#include "randombytes.h"

#define NTESTS 1000

static int test_keys(void) {
  mlkem_public_key pk;
  mlkem_secret_key sk;
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];

  // Alice generates a public key
  crypto_kem_keypair(&pk, &sk);

  // Bob derives a secret key and creates a response
  crypto_kem_enc(ct, key_b, &pk);

  // Alice uses Bobs response to get her shared key
  crypto_kem_dec(key_a, ct, &sk);

  if (memcmp(key_a, key_b, CRYPTO_BYTES)) {
    printf("ERROR keys\n");
    return 1;
  }

  return 0;
}


static int test_keys_serialized(void) {
  mlkem_public_key pk;
  mlkem_secret_key sk;
  uint8_t pks[CRYPTO_PUBLICKEYBYTES];
  uint8_t sks[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];

  // Alice generates a public key
  crypto_kem_keypair(&pk, &sk);

  // serialize keys
  crypto_kem_serialize_pk(pks, &pk);
  crypto_kem_serialize_sk(sks, &sk);

  // zero out keys to be sure serialization works properly
  memset(&pk, 0, sizeof(mlkem_public_key));
  memset(&sk, 0, sizeof(mlkem_secret_key));

  // deserialize keys
  crypto_kem_deserialize_pk(&pk, pks);
  crypto_kem_deserialize_sk(&sk, sks);

  // Bob derives a secret key and creates a response
  crypto_kem_enc(ct, key_b, &pk);

  // Alice uses Bobs response to get her shared key
  crypto_kem_dec(key_a, ct, &sk);

  if (memcmp(key_a, key_b, CRYPTO_BYTES)) {
    printf("ERROR keys (serialized)\n");
    return 1;
  }

  return 0;
}

static int test_invalid_pk(void) {
  uint8_t pks[CRYPTO_PUBLICKEYBYTES];
  mlkem_public_key pk;
  mlkem_secret_key sk;
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_b[CRYPTO_BYTES];
  int rc;
  // Alice generates a public key
  crypto_kem_keypair(&pk, &sk);


  crypto_kem_serialize_pk(pks, &pk);
  memset(&pk, 0, sizeof(mlkem_public_key));
  crypto_kem_deserialize_pk(&pk, pks);

  // Bob derives a secret key and creates a response
  rc = crypto_kem_enc(ct, key_b, &pk);

  if (rc) {
    printf("ERROR test_invalid_pk\n");
    return 1;
  }

  // set first public key coefficient to 4095 (0xFFF)
  pks[0] = 0xFF;
  pks[1] |= 0x0F;

  memset(&pk, 0, sizeof(mlkem_public_key));
  rc = crypto_kem_deserialize_pk(&pk, pks);

  if (!rc) {
    printf("ERROR test_invalid_pk\n");
    return 1;
  }
  return 0;
}

static int test_invalid_sk_a(void) {
  mlkem_public_key pk;
  mlkem_secret_key sk;
  uint8_t sks[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  int rc;

  // Alice generates a public key
  crypto_kem_keypair(&pk, &sk);

  // Bob derives a secret key and creates a response
  crypto_kem_enc(ct, key_b, &pk);


  crypto_kem_serialize_sk(sks, &sk);
  memset(&sk, 0, sizeof(mlkem_secret_key));
  // Replace first part of secret key with random values
  randombytes(sks, 10);
  crypto_kem_deserialize_sk(&sk, sks);

  // Alice uses Bobs response to get her shared key
  // This should fail due to wrong sk
  rc = crypto_kem_dec(key_a, ct, &sk);
  if (rc) {
    printf("ERROR test_invalid_sk_a\n");
    return 1;
  }

  if (!memcmp(key_a, key_b, CRYPTO_BYTES)) {
    printf("ERROR invalid sk\n");
    return 1;
  }

  return 0;
}


static int test_invalid_ciphertext(void) {
  mlkem_public_key pk;
  mlkem_secret_key sk;
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  uint8_t b;
  size_t pos;

  do {
    randombytes(&b, sizeof(uint8_t));
  } while (!b);
  randombytes((uint8_t *)&pos, sizeof(size_t));

  // Alice generates a public key
  crypto_kem_keypair(&pk, &sk);

  // Bob derives a secret key and creates a response
  crypto_kem_enc(ct, key_b, &pk);

  // Change some byte in the ciphertext (i.e., encapsulated key)
  ct[pos % CRYPTO_CIPHERTEXTBYTES] ^= b;

  // Alice uses Bobs response to get her shared key
  crypto_kem_dec(key_a, ct, &sk);

  if (!memcmp(key_a, key_b, CRYPTO_BYTES)) {
    printf("ERROR invalid ciphertext\n");
    return 1;
  }

  return 0;
}

int main(void) {
  unsigned int i;
  int r;

  for (i = 0; i < NTESTS; i++) {
    r = test_keys();
    r |= test_keys_serialized();
    r |= test_invalid_pk();
    r |= test_invalid_sk_a();
    r |= test_invalid_ciphertext();
    if (r) {
      return 1;
    }
  }

  printf("CRYPTO_SECRETKEYBYTES:  %d\n", CRYPTO_SECRETKEYBYTES);
  printf("CRYPTO_PUBLICKEYBYTES:  %d\n", CRYPTO_PUBLICKEYBYTES);
  printf("CRYPTO_CIPHERTEXTBYTES: %d\n", CRYPTO_CIPHERTEXTBYTES);

  return 0;
}
