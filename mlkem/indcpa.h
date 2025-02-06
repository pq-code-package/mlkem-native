/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLKEM_NATIVE_INDCPA_H
#define MLKEM_NATIVE_INDCPA_H

#include <stdint.h>
#include "cbmc.h"
#include "common.h"
#include "poly_k.h"

typedef struct
{
  polyvec skpv;
} mlkem_indcpa_secret_key;

typedef struct
{
  polyvec at[MLKEM_K]; /* transposed matrix */
  polyvec pkpv;
  uint8_t seed[MLKEM_SYMBYTES];
} mlkem_indcpa_public_key;


#define indcpa_serialize_pk MLKEM_NAMESPACE_K(indcpa_serialize_pk)
/*************************************************
 * Name:        indcpa_serialize_pk
 *
 * Description: Serialize the public key as concatenation of the
 *              serialized vector of polynomials pk
 *              and the public seed used to generate the matrix A.
 *
 * Arguments:   uint8_t *pks: pointer to the output serialized public key
 *              polyvec *pk: pointer to the input public-key.
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void indcpa_serialize_pk(uint8_t pks[MLKEM_INDCPA_PUBLICKEYBYTES],
                         const mlkem_indcpa_public_key *pk);

#define indcpa_deserialize_pk MLKEM_NAMESPACE_K(indcpa_deserialize_pk)
/*************************************************
 * Name:        indcpa_deserialize_pk
 *
 * Description: De-serialize public key from a byte array;
 *              approximate inverse of indcpa_serialize_pk
 *
 * Arguments:   - mlkem_indcpa_public_key *pk: pointer to output public-key
 *              - uint8_t *seed: pointer to output seed to generate matrix A
 *              - const uint8_t *pks: pointer to input serialized public
 *                  key.
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void indcpa_deserialize_pk(mlkem_indcpa_public_key *pk,
                           const uint8_t pks[MLKEM_INDCPA_PUBLICKEYBYTES]);

#define indcpa_serialize_sk MLKEM_NAMESPACE_K(indcpa_serialize_sk)
/*************************************************
 * Name:        indcpa_serialize_sk
 *
 * Description: Serialize the secret key
 *
 * Arguments:   - uint8_t *sks: pointer to output serialized secret key
 *              - polyvec *sk: pointer to input secret key
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void indcpa_serialize_sk(uint8_t sks[MLKEM_INDCPA_SECRETKEYBYTES],
                         const mlkem_indcpa_secret_key *sk);

#define indcpa_deserialize_sk MLKEM_NAMESPACE_K(indcpa_deserialize_sk)
/*************************************************
 * Name:        indcpa_deserialize_sk
 *
 * Description: De-serialize the secret key; inverse of indcpa_serialize_sk
 *
 * Arguments:   - mlkem_indcpa_secret_key *sk: pointer to output secret key
 *              - const uint8_t *sks: pointer to input serialized secret key
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void indcpa_deserialize_sk(mlkem_indcpa_secret_key *sk,
                           const uint8_t sks[MLKEM_INDCPA_SECRETKEYBYTES]);

#define gen_matrix MLKEM_NAMESPACE_K(gen_matrix)
/*************************************************
 * Name:        gen_matrix
 *
 * Description: Deterministically generate matrix A (or the transpose of A)
 *              from a seed. Entries of the matrix are polynomials that look
 *              uniformly random. Performs rejection sampling on output of
 *              a XOF
 *
 * Arguments:   - polyvec *a: pointer to ouptput matrix A
 *              - const uint8_t *seed: pointer to input seed
 *              - int transposed: boolean deciding whether A or A^T is generated
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES], int transposed)
__contract__(
  requires(memory_no_alias(a, sizeof(polyvec) * MLKEM_K))
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  requires(transposed == 0 || transposed == 1)
  assigns(object_whole(a))
  ensures(forall(x, 0, MLKEM_K, forall(y, 0, MLKEM_K,
  array_bound(a[x].vec[y].coeffs, 0, MLKEM_N, 0, MLKEM_Q))));
);

#define indcpa_keypair_derand MLKEM_NAMESPACE_K(indcpa_keypair_derand)
/*************************************************
 * Name:        indcpa_keypair_derand
 *
 * Description: Generates public and private key for the CPA-secure
 *              public-key encryption scheme underlying ML-KEM
 *
 * Arguments:   - mlkem_indcpa_public_key *pk: pointer to output public key
 *              - mlkem_indcpa_secret_key *sk: pointer to output private key
 *              - const uint8_t *coins: pointer to input randomness
 *                             (of length MLKEM_SYMBYTES bytes)
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void indcpa_keypair_derand(mlkem_indcpa_public_key *pk,
                           mlkem_indcpa_secret_key *sk,
                           const uint8_t coins[MLKEM_SYMBYTES])
__contract__(
  requires(memory_no_alias(pk, sizeof(mlkem_indcpa_public_key)))
  requires(memory_no_alias(sk, sizeof(mlkem_indcpa_secret_key)))
  requires(memory_no_alias(coins, MLKEM_SYMBYTES))
  assigns(object_whole(pk))
  assigns(object_whole(sk))
);

#define indcpa_enc MLKEM_NAMESPACE_K(indcpa_enc)
/*************************************************
 * Name:        indcpa_enc
 *
 * Description: Encryption function of the CPA-secure
 *              public-key encryption scheme underlying Kyber.
 *
 * Arguments:   - uint8_t *c: pointer to output ciphertext
 *                            (of length MLKEM_INDCPA_BYTES bytes)
 *              - const uint8_t *m: pointer to input message
 *                                  (of length MLKEM_INDCPA_MSGBYTES bytes)
 *              - const mlkem_indcpa_public_key *pk: pointer to input public key
 *              - const uint8_t *coins: pointer to input random coins used as
 *seed (of length MLKEM_SYMBYTES) to deterministically generate all randomness
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const mlkem_indcpa_public_key *pk,
                const uint8_t coins[MLKEM_SYMBYTES])
__contract__(
  requires(memory_no_alias(c, MLKEM_INDCPA_BYTES))
  requires(memory_no_alias(m, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(pk, sizeof(mlkem_indcpa_public_key)))
  requires(memory_no_alias(coins, MLKEM_SYMBYTES))
  assigns(object_whole(c))
);

#define indcpa_dec MLKEM_NAMESPACE_K(indcpa_dec)
/*************************************************
 * Name:        indcpa_dec
 *
 * Description: Decryption function of the CPA-secure
 *              public-key encryption scheme underlying Kyber.
 *
 * Arguments:   - uint8_t *m: pointer to output decrypted message
 *                            (of length MLKEM_INDCPA_MSGBYTES)
 *              - const uint8_t *c: pointer to input ciphertext
 *                                  (of length MLKEM_INDCPA_BYTES)
 *              - const mlkem_indcpa_secret_key *sk: pointer to input secret key
 *
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t c[MLKEM_INDCPA_BYTES],
                const mlkem_indcpa_secret_key *sk)
__contract__(
  requires(memory_no_alias(c, MLKEM_INDCPA_BYTES))
  requires(memory_no_alias(m, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(sk, sizeof(mlkem_indcpa_secret_key)))
  assigns(object_whole(m))
);

#endif /* MLKEM_NATIVE_INDCPA_H */
