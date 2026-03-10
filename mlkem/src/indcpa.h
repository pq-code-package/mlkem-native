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

#include "cbmc.h"
#include "common.h"
#include "poly_k.h"

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
 * Specification: Implements @[FIPS203, Algorithm 13 (K-PKE.KeyGen), L3-7]
 *                and @[FIPS203, Algorithm 14 (K-PKE.Encrypt), L4-8].
 *                The `transposed` parameter only affects internal presentation.
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_gen_matrix(mlk_polymat *a, const uint8_t seed[MLKEM_SYMBYTES],
                    int transposed)
__contract__(
  requires(memory_no_alias(a, sizeof(mlk_polymat)))
  requires(memory_no_alias(seed, MLKEM_SYMBYTES))
  requires(transposed == 0 || transposed == 1)
  assigns(memory_slice(a, sizeof(mlk_polymat)))
  ensures(forall(x, 0, MLKEM_K, forall(y, 0, MLKEM_K,
  array_bound(a->vec[x].vec[y].coeffs, 0, MLKEM_N, 0, MLKEM_Q))))
);

#define mlk_indcpa_keypair_derand \
  MLK_NAMESPACE_K(indcpa_keypair_derand) MLK_CONTEXT_PARAMETERS_3
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
 * Specification: Implements @[FIPS203, Algorithm 13 (K-PKE.KeyGen)].
 *
 **************************************************/
MLK_INTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int mlk_indcpa_keypair_derand(uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                              uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                              const uint8_t coins[MLKEM_SYMBYTES],
                              MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
__contract__(
  requires(memory_no_alias(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
  requires(memory_no_alias(sk, MLKEM_INDCPA_SECRETKEYBYTES))
  requires(memory_no_alias(coins, MLKEM_SYMBYTES))
  assigns(memory_slice(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
  assigns(memory_slice(sk, MLKEM_INDCPA_SECRETKEYBYTES))
  ensures(return_value == 0 || return_value == MLK_ERR_FAIL ||
          return_value == MLK_ERR_OUT_OF_MEMORY ||
          return_value == MLK_ERR_RNG_FAIL)
);

#define mlk_indcpa_enc MLK_NAMESPACE_K(indcpa_enc) MLK_CONTEXT_PARAMETERS_4
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
 * Specification: Implements @[FIPS203, Algorithm 14 (K-PKE.Encrypt)].
 *
 **************************************************/
MLK_INTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int mlk_indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                   const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                   const uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                   const uint8_t coins[MLKEM_SYMBYTES],
                   MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
__contract__(
  requires(memory_no_alias(c, MLKEM_INDCPA_BYTES))
  requires(memory_no_alias(m, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
  requires(memory_no_alias(coins, MLKEM_SYMBYTES))
  assigns(memory_slice(c, MLKEM_INDCPA_BYTES))
  ensures(return_value == 0 || return_value == MLK_ERR_FAIL ||
          return_value == MLK_ERR_OUT_OF_MEMORY)
);

#define mlk_indcpa_enc_u MLK_NAMESPACE_K(indcpa_enc_u) MLK_CONTEXT_PARAMETERS_3
/*************************************************
 * Name:        mlk_indcpa_enc_u
 *
 * Description: Computes the u-component of a K-PKE ciphertext
 *              (first phase of incremental K-PKE.Encrypt).
 *
 *              Produces ct_u = Compress_du(A^T * r + e1).
 *              This is the coins-only variant: no intermediate state
 *              is output.
 *
 * Arguments:   - uint8_t *ct_u: pointer to output ct_u
 *                               (of length MLKEM_POLYVECCOMPRESSEDBYTES_DU)
 *              - const uint8_t *seed: pointer to input public seed rho
 *                                     (of length MLKEM_SYMBYTES)
 *              - const uint8_t *coins: pointer to input random coins
 *                 (of length MLKEM_SYMBYTES) to deterministically generate
 *                 all randomness
 *
 * Specification: Partially implements
 *                @[FIPS203, Algorithm 14 (K-PKE.Encrypt), L1-19]
 *
 **************************************************/
MLK_INTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int mlk_indcpa_enc_u(uint8_t ct_u[MLKEM_POLYVECCOMPRESSEDBYTES_DU],
                     const uint8_t seed[MLKEM_SYMBYTES],
                     const uint8_t coins[MLKEM_SYMBYTES],
                     MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
/* TODO: Add CBMC contracts */;

#define mlk_indcpa_enc_v MLK_NAMESPACE_K(indcpa_enc_v) MLK_CONTEXT_PARAMETERS_4
/*************************************************
 * Name:        mlk_indcpa_enc_v
 *
 * Description: Computes the v-component of a K-PKE ciphertext
 *              (second phase of incremental K-PKE.Encrypt).
 *
 *              Re-derives the noise (r, e2) from coins and computes
 *              ct_v = Compress_dv(t^T * r + e2 + msg).
 *              This is the coins-only variant: all randomness is
 *              re-derived from coins rather than taken from
 *              intermediate state.
 *
 * Arguments:   - uint8_t *ct_v: pointer to output ct_v
 *                               (of length MLKEM_POLYCOMPRESSEDBYTES_DV)
 *              - const uint8_t *m: pointer to input message
 *                                  (of length MLKEM_INDCPA_MSGBYTES)
 *              - const uint8_t *ek_vector: pointer to input encoded public
 *                  key vector t_hat (of length MLKEM_POLYVECBYTES)
 *              - const uint8_t *coins: pointer to input random coins
 *                 (of length MLKEM_SYMBYTES) to deterministically generate
 *                 all randomness
 *
 * Specification: Partially implements
 *                @[FIPS203, Algorithm 14 (K-PKE.Encrypt), L2-3, L20-23]
 *
 **************************************************/
MLK_INTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int mlk_indcpa_enc_v(uint8_t ct_v[MLKEM_POLYCOMPRESSEDBYTES_DV],
                     const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                     const uint8_t ek_vector[MLKEM_POLYVECBYTES],
                     const uint8_t coins[MLKEM_SYMBYTES],
                     MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
/* TODO: Add CBMC contracts */;

#define mlk_indcpa_dec MLK_NAMESPACE_K(indcpa_dec) MLK_CONTEXT_PARAMETERS_3
/*************************************************
 * Name:        mlk_indcpa_dec
 *
 * Description: Decryption function of the CPA-secure
 *              public-key encryption scheme underlying ML-KEM.
 *
 * Arguments:   - uint8_t *m: pointer to output decrypted message
 *                            (of length MLKEM_INDCPA_MSGBYTES)
 *              - const uint8_t *c: pointer to input ciphertext
 *                                  (of length MLKEM_INDCPA_BYTES)
 *              - const uint8_t *sk: pointer to input secret key
 *                                   (of length MLKEM_INDCPA_SECRETKEYBYTES)
 *
 * Specification: Implements @[FIPS203, Algorithm 15 (K-PKE.Decrypt)].
 *
 **************************************************/
MLK_INTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int mlk_indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                   const uint8_t c[MLKEM_INDCPA_BYTES],
                   const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                   MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
__contract__(
  requires(memory_no_alias(c, MLKEM_INDCPA_BYTES))
  requires(memory_no_alias(m, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(sk, MLKEM_INDCPA_SECRETKEYBYTES))
  assigns(memory_slice(m, MLKEM_INDCPA_MSGBYTES))
  ensures(return_value == 0 || return_value == MLK_ERR_FAIL ||
          return_value == MLK_ERR_OUT_OF_MEMORY)
);

#endif /* !MLK_INDCPA_H */
