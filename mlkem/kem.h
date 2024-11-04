/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef KEM_H
#define KEM_H

#include <stdint.h>
#include "cbmc.h"
#include "common.h"
#include "indcpa.h"

#if defined(MLKEM_NATIVE_CHECK_APIS)
/* Include to ensure consistency between internal kem.h
 * and external mlkem_native.h. */
#include "mlkem_native.h"

#if MLKEM_INDCCA_SECRETKEYBYTES != MLKEM_SECRETKEYBYTES(MLKEM_LVL)
#error Mismatch for SECRETKEYBYTES between kem.h and mlkem_native.h
#endif

#if MLKEM_INDCCA_PUBLICKEYBYTES != MLKEM_PUBLICKEYBYTES(MLKEM_LVL)
#error Mismatch for PUBLICKEYBYTES between kem.h and mlkem_native.h
#endif

#if MLKEM_INDCCA_CIPHERTEXTBYTES != MLKEM_CIPHERTEXTBYTES(MLKEM_LVL)
#error Mismatch for CIPHERTEXTBYTES between kem.h and mlkem_native.h
#endif

#else
#define crypto_kem_keypair_derand MLKEM_NAMESPACE_K(keypair_derand)
#define crypto_kem_keypair MLKEM_NAMESPACE_K(keypair)
#define crypto_kem_enc_derand MLKEM_NAMESPACE_K(enc_derand)
#define crypto_kem_enc MLKEM_NAMESPACE_K(enc)
#define crypto_kem_dec MLKEM_NAMESPACE_K(dec)
#endif

typedef struct
{
  mlkem_indcpa_secret_key indcpa_sk;
  mlkem_indcpa_public_key indcpa_pk;
  uint8_t seed[MLKEM_SYMBYTES];
  uint8_t z[MLKEM_SYMBYTES];
  uint8_t hpk[MLKEM_SYMBYTES];
} mlkem_secret_key;

typedef struct
{
  mlkem_indcpa_public_key indcpa_pk;
  uint8_t hpk[MLKEM_SYMBYTES];
} mlkem_public_key;

#define crypto_kem_serialize_sk MLKEM_NAMESPACE(serialize_sk)
int crypto_kem_serialize_sk(uint8_t sks[MLKEM_INDCCA_SECRETKEYBYTES],
                            const mlkem_secret_key *sk);

#define crypto_kem_deserialize_sk MLKEM_NAMESPACE(deserialize_sk)
int crypto_kem_deserialize_sk(mlkem_secret_key *sk,
                              const uint8_t sks[MLKEM_INDCCA_SECRETKEYBYTES]);

#define crypto_kem_serialize_pk MLKEM_NAMESPACE(serialize_pk)
int crypto_kem_serialize_pk(uint8_t pks[MLKEM_INDCCA_PUBLICKEYBYTES],
                            const mlkem_public_key *pk);

#define crypto_kem_deserialize_pk MLKEM_NAMESPACE(deserialize_pk)
int crypto_kem_deserialize_pk(mlkem_public_key *pk,
                              const uint8_t pks[MLKEM_INDCCA_PUBLICKEYBYTES]);

/*************************************************
 * Name:        crypto_kem_keypair_derand
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t *pk: pointer to output public key
 *                (an already allocated array of MLKEM_INDCCA_PUBLICKEYBYTES
 *                 bytes)
 *              - uint8_t *sk: pointer to output private key
 *                (an already allocated array of MLKEM_INDCCA_SECRETKEYBYTES
 *                 bytes)
 *              - uint8_t *coins: pointer to input randomness
 *                (an already allocated array filled with 2*MLKEM_SYMBYTES
 *                 random bytes)
 **
 * Returns 0 (success)
 **************************************************/
int crypto_kem_keypair_derand(mlkem_public_key *pk, mlkem_secret_key *sk,
                              const uint8_t *coins)
__contract__(
  requires(memory_no_alias(pk, MLKEM_INDCCA_PUBLICKEYBYTES))
  requires(memory_no_alias(sk, MLKEM_INDCCA_SECRETKEYBYTES))
  requires(memory_no_alias(coins, 2 * MLKEM_SYMBYTES))
  assigns(object_whole(pk))
  assigns(object_whole(sk))
);

/*************************************************
 * Name:        crypto_kem_keypair
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t *pk: pointer to output public key
 *                (an already allocated array of MLKEM_INDCCA_PUBLICKEYBYTES
 *                 bytes)
 *              - uint8_t *sk: pointer to output private key
 *                (an already allocated array of MLKEM_INDCCA_SECRETKEYBYTES
 *                 bytes)
 *
 * Returns 0 (success)
 **************************************************/
int crypto_kem_keypair(mlkem_public_key *pk, mlkem_secret_key *sk)
__contract__(
  requires(memory_no_alias(pk, MLKEM_INDCCA_PUBLICKEYBYTES))
  requires(memory_no_alias(sk, MLKEM_INDCCA_SECRETKEYBYTES))
  assigns(object_whole(pk))
  assigns(object_whole(sk))
);

/*************************************************
 * Name:        crypto_kem_enc_derand
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text
 *                (an already allocated array of MLKEM_INDCCA_CIPHERTEXTBYTES
 *                 bytes)
 *              - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_INDCCA_PUBLICKEYBYTES
 *                 bytes)
 *              - const uint8_t *coins: pointer to input randomness
 *                (an already allocated array filled with MLKEM_SYMBYTES random
 *                 bytes)
 **
 * Returns 0 on success, and -1 if the public key modulus check (see Section 7.2
 * of FIPS203) fails.
 **************************************************/
int crypto_kem_enc_derand(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                          uint8_t ss[MLKEM_SSBYTES], const mlkem_public_key *pk,
                          const uint8_t coins[MLKEM_SYMBYTES])
__contract__(
  requires(memory_no_alias(ct, MLKEM_INDCCA_CIPHERTEXTBYTES))
  requires(memory_no_alias(ss, MLKEM_SSBYTES))
  requires(memory_no_alias(pk, MLKEM_INDCCA_PUBLICKEYBYTES))
  requires(memory_no_alias(coins, MLKEM_SYMBYTES))
  assigns(object_whole(ct))
  assigns(object_whole(ss))
);

/*************************************************
 * Name:        crypto_kem_enc
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text
 *                (an already allocated array of MLKEM_INDCCA_CIPHERTEXTBYTES
 *bytes)
 *              - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_INDCCA_PUBLICKEYBYTES
 *bytes)
 *
 * Returns 0 on success, and -1 if the public key modulus check (see Section 7.2
 * of FIPS203) fails.
 **************************************************/
int crypto_kem_enc(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                   uint8_t ss[MLKEM_SSBYTES], const mlkem_public_key *pk)
__contract__(
  requires(memory_no_alias(ct, MLKEM_INDCCA_CIPHERTEXTBYTES))
  requires(memory_no_alias(ss, MLKEM_SSBYTES))
  requires(memory_no_alias(pk, MLKEM_INDCCA_PUBLICKEYBYTES))
  assigns(object_whole(ct))
  assigns(object_whole(ss))
);

/*************************************************
 * Name:        crypto_kem_dec
 *
 * Description: Generates shared secret for given
 *              cipher text and private key
 *
 * Arguments:   - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *ct: pointer to input cipher text
 *                (an already allocated array of MLKEM_INDCCA_CIPHERTEXTBYTES
 *bytes)
 *              - const uint8_t *sk: pointer to input private key
 *                (an already allocated array of MLKEM_INDCCA_SECRETKEYBYTES
 *bytes)
 *
 * Returns 0 on success, and -1 if the secret key hash check (see Section 7.3 of
 * FIPS203) fails.
 *
 * On failure, ss will contain a pseudo-random value.
 **************************************************/
int crypto_kem_dec(uint8_t ss[MLKEM_SSBYTES],
                   const uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                   const mlkem_secret_key *sk)
__contract__(
  requires(memory_no_alias(ss, MLKEM_SSBYTES))
  requires(memory_no_alias(ct, MLKEM_INDCCA_CIPHERTEXTBYTES))
  requires(memory_no_alias(sk, MLKEM_INDCCA_SECRETKEYBYTES))
  assigns(object_whole(ss))
);

#endif
