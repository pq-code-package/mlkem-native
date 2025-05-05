/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS203]
 *   FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/203/final
 */

#ifndef MLK_INDCPA_H
#define MLK_INDCPA_H

#include <stdint.h>
#include "cbmc.h"
#include "common.h"
#include "poly_k.h"

#define mlk_indcpa_secret_key MLK_NAMESPACE_K(mlk_indcpa_secret_key)
typedef struct
{
  mlk_polyvec skpv;
  mlk_polyvec_mulcache skpv_cache;
} MLK_ALIGN mlk_indcpa_secret_key;

#define mlk_indcpa_public_key MLK_NAMESPACE_K(mlk_indcpa_public_key)
typedef struct
{
  mlk_polymat at; /* transposed matrix */
  mlk_polyvec pkpv;
  MLK_ALIGN uint8_t marshalled[MLKEM_INDCCA_PUBLICKEYBYTES];
  int transposed;
} MLK_ALIGN mlk_indcpa_public_key;

#define mlk_indcpa_marshal_pk MLK_NAMESPACE_K(indcpa_marshal_pk)
MLK_INTERNAL_API
void mlk_indcpa_marshal_pk(uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                           const mlk_indcpa_public_key *pks)
__contract__(
  requires(memory_no_alias(pk,  MLKEM_INDCPA_PUBLICKEYBYTES))
  requires(memory_no_alias(pks, sizeof(mlk_indcpa_public_key)))
  requires(forall(k0, 0, MLKEM_K,
    array_bound(pks->pkpv[k0].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
  assigns(object_whole(pk))
);

#define mlk_indcpa_parse_pk MLK_NAMESPACE_K(indcpa_parse_pk)
MLK_INTERNAL_API
void mlk_indcpa_parse_pk(mlk_indcpa_public_key *pks,
                         const uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES])
__contract__(
  requires(memory_no_alias(pks, sizeof(mlk_indcpa_public_key)))
  requires(memory_no_alias(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
  assigns(memory_slice(pks, sizeof(mlk_indcpa_public_key)))
  ensures(forall(k1, 0, MLKEM_K,
    array_bound(pks->pkpv[k1].coeffs, 0, MLKEM_N, 0, MLKEM_UINT12_LIMIT)))
  ensures(forall(x, 0, MLKEM_K * MLKEM_K,
    array_bound(pks->at[x].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
);

#define mlk_indcpa_marshal_sk MLK_NAMESPACE_K(indcpa_marshal_sk)
MLK_INTERNAL_API
void mlk_indcpa_marshal_sk(uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                           const mlk_indcpa_secret_key *sks)
__contract__(
  requires(memory_no_alias(sk,  MLKEM_INDCPA_SECRETKEYBYTES))
  requires(memory_no_alias(sks, sizeof(mlk_indcpa_secret_key)))
  requires(forall(k0, 0, MLKEM_K,
    array_bound(sks->skpv[k0].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
  assigns(object_whole(sk))
);

#define mlk_indcpa_parse_sk MLK_NAMESPACE_K(indcpa_parse_sk)
MLK_INTERNAL_API
void mlk_indcpa_parse_sk(mlk_indcpa_secret_key *sks,
                         const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES])
__contract__(
  requires(memory_no_alias(sks, sizeof(mlk_indcpa_secret_key)))
  requires(memory_no_alias(sk, MLKEM_INDCPA_SECRETKEYBYTES))
  assigns(memory_slice(sks, sizeof(mlk_indcpa_secret_key)))
  ensures(forall(k0, 0, MLKEM_K,
    array_bound(sks->skpv[k0].coeffs, 0, MLKEM_N, 0, MLKEM_UINT12_LIMIT)))
);

#define mlk_gen_matrix MLK_NAMESPACE_K(gen_matrix)
/*************************************************
 * Name:        mlk_gen_matrix
 *
 * Description: Deterministically generate matrix A (or the transpose of A)
 *              from a seed. Entries of the matrix are polynomials that look
 *              uniformly random. Performs rejection sampling on output of
 *              a XOF
 *
 * Arguments:   - mlk_polymat a: pointer to output matrix A
 *              - const uint8_t *seed: pointer to input seed
 *              - int transposed: boolean deciding whether A or A^T is generated
 *
 * Specification: Implements [@FIPS203, Algorithm 13 (K-PKE.KeyGen), L3-7]
 *                and [@FIPS203, Algorithm 14 (K-PKE.Encrypt), L4-8].
 *                The `transposed` parameter only affects internal presentation.
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_gen_matrix(mlk_polymat a, const uint8_t seed[MLKEM_SYMBYTES],
                    int transposed)
__contract__(
  requires(memory_no_alias(a, sizeof(mlk_polymat)))
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  requires(transposed == 0 || transposed == 1)
  assigns(memory_slice(a, sizeof(mlk_poly) * MLKEM_K * MLKEM_K))
  ensures(forall(x, 0, MLKEM_K * MLKEM_K,
    array_bound(a[x].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
);

#define mlk_indcpa_keypair_derand MLK_NAMESPACE_K(indcpa_keypair_derand)
/*************************************************
 * Name:        mlk_indcpa_keypair_derand
 *
 * Description: Generates public and private key for the CPA-secure
 *              public-key encryption scheme underlying ML-KEM
 *
 * Arguments:   - uint8_t *pk: pointer to output public key
 *                             (of length MLKEM_INDCPA_PUBLICKEYBYTES bytes)
 *              - uint8_t *sk: pointer to output private key
 *                             (of length MLKEM_INDCPA_SECRETKEYBYTES bytes)
 *              - const uint8_t *coins: pointer to input randomness
 *                             (of length MLKEM_SYMBYTES bytes)
 *
 * Specification: Implements [@FIPS203, Algorithm 13 (K-PKE.KeyGen)].
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_indcpa_keypair_derand(mlk_indcpa_public_key *pk,
                               mlk_indcpa_secret_key *sk,
                               const uint8_t coins[MLKEM_SYMBYTES])
__contract__(
  requires(memory_no_alias(pk, sizeof(mlk_indcpa_public_key)))
  requires(memory_no_alias(sk, sizeof(mlk_indcpa_secret_key)))
  requires(memory_no_alias(coins, MLKEM_SYMBYTES))
  assigns(memory_slice(pk, sizeof(mlk_indcpa_public_key)))
  assigns(memory_slice(sk, sizeof(mlk_indcpa_secret_key)))
  ensures(forall(k0, 0, MLKEM_K,
    array_bound(pk->pkpv[k0].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
  ensures(forall(x, 0, MLKEM_K * MLKEM_K,
    array_bound(pk->at[x].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
  ensures(forall(k1, 0, MLKEM_K,
    array_bound(sk->skpv[k1].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
);

#define mlk_indcpa_enc MLK_NAMESPACE_K(indcpa_enc)
/*************************************************
 * Name:        mlk_indcpa_enc
 *
 * Description: Encryption function of the CPA-secure
 *              public-key encryption scheme underlying Kyber.
 *
 * Arguments:   - uint8_t *c: pointer to output ciphertext
 *                            (of length MLKEM_INDCPA_BYTES bytes)
 *              - const uint8_t *m: pointer to input message
 *                                  (of length MLKEM_INDCPA_MSGBYTES bytes)
 *              - const uint8_t *pk: pointer to input public key
 *                                   (of length MLKEM_INDCPA_PUBLICKEYBYTES)
 *              - const uint8_t *coins: pointer to input random coins used as
 *                 seed (of length MLKEM_SYMBYTES) to deterministically generate
 *                 all randomness
 *
 * Specification: Implements [@FIPS203, Algorithm 14 (K-PKE.Encrypt)].
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                    const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                    const mlk_indcpa_public_key *pk,
                    const uint8_t coins[MLKEM_SYMBYTES])
__contract__(
  requires(memory_no_alias(c, MLKEM_INDCPA_BYTES))
  requires(memory_no_alias(m, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(pk, sizeof(mlk_indcpa_public_key)))
  requires(forall(k0, 0, MLKEM_K,
    array_bound(pk->pkpv[k0].coeffs, 0, MLKEM_N, 0, MLKEM_UINT12_LIMIT)))
  requires(forall(x, 0, MLKEM_K * MLKEM_K,
      array_bound(pk->at[x].coeffs, 0, MLKEM_N, 0, MLKEM_Q)))
  requires(memory_no_alias(coins, MLKEM_SYMBYTES))
  assigns(object_whole(c))
);

#define mlk_indcpa_dec MLK_NAMESPACE_K(indcpa_dec)
/*************************************************
 * Name:        mlk_indcpa_dec
 *
 * Description: Decryption function of the CPA-secure
 *              public-key encryption scheme underlying Kyber.
 *
 * Arguments:   - uint8_t *m: pointer to output decrypted message
 *                            (of length MLKEM_INDCPA_MSGBYTES)
 *              - const uint8_t *c: pointer to input ciphertext
 *                                  (of length MLKEM_INDCPA_BYTES)
 *              - const uint8_t *sk: pointer to input secret key
 *                                   (of length MLKEM_INDCPA_SECRETKEYBYTES)
 *
 * Specification: Implements [@FIPS203, Algorithm 15 (K-PKE.Decrypt)].
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                    const uint8_t c[MLKEM_INDCPA_BYTES],
                    const mlk_indcpa_secret_key *sk)
__contract__(
  requires(memory_no_alias(c, MLKEM_INDCPA_BYTES))
  requires(memory_no_alias(m, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(sk, sizeof(mlk_indcpa_secret_key)))
  requires(forall(k0, 0, MLKEM_K,
    array_bound(sk->skpv[k0].coeffs, 0, MLKEM_N, 0, MLKEM_UINT12_LIMIT)))
  assigns(object_whole(m))
);

#endif /* !MLK_INDCPA_H */
