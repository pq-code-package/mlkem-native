/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "arith_backend.h"
#include "cbmc.h"
#include "debug.h"
#include "indcpa.h"
#include "poly.h"
#include "poly_k.h"
#include "randombytes.h"
#include "sampling.h"
#include "symmetric.h"

/* Level namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define mlk_unpack_pk MLK_ADD_LEVEL(mlk_unpack_pk)
#define mlk_unpack_sk MLK_ADD_LEVEL(mlk_unpack_sk)
#define mlk_pack_ciphertext MLK_ADD_LEVEL(mlk_pack_ciphertext)
#define mlk_unpack_ciphertext MLK_ADD_LEVEL(mlk_unpack_ciphertext)
#define mlk_matvec_mul MLK_ADD_LEVEL(mlk_matvec_mul)
#define transpose_matrix MLK_ADD_LEVEL(transpose_matrix)
/* End of level namespacing */

/*************************************************
 * Name:        mlk_indcpa_marshal_pk
 *
 * Description: Serialize the public key as concatenation of the
 *              serialized vector of polynomials pk
 *              and the public seed used to generate the matrix A.
 *
 * Arguments:   uint8_t *r: pointer to the output serialized public key
 *              mlk_polyvec *pk: pointer to the input public-key mlk_polyvec.
 *                Must have coefficients within [0,..,q-1].
 *              const uint8_t *seed: pointer to the input public seed
 *
 * Specification:
 * Implements [FIPS 203, Algorithm 13 (K-PKE.KeyGen), L19]
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_indcpa_marshal_pk(uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                           const mlk_indcpa_public_key *pks)
{
  mlk_assert_bound_2d(pks->pkpv.vec, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
  mlk_polyvec_tobytes(pk, &pks->pkpv);
  memcpy(pk + MLKEM_POLYVECBYTES, pks->seed, MLKEM_SYMBYTES);
}


/*************************************************
 * Name:        mlk_indcpa_parse_pk
 *
 * Description: De-serialize public key from a byte array;
 *              approximate inverse of mlk_pack_pk
 *
 * Arguments:   - mlk_polyvec *pk: pointer to output public-key polynomial
 *                vector Coefficients will be normalized to [0,..,q-1].
 *              - uint8_t *seed: pointer to output seed to generate matrix A
 *              - const uint8_t *packedpk: pointer to input serialized public
 *                  key.
 *
 * Specification:
 * Implements [FIPS 203, Algorithm 14 (K-PKE.Encrypt), L2-3]
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_indcpa_parse_pk(mlk_indcpa_public_key *pks,
                         const uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES])
{
  mlk_polyvec_frombytes(&pks->pkpv, pk);
  memcpy(pks->seed, pk + MLKEM_POLYVECBYTES, MLKEM_SYMBYTES);
  mlk_gen_matrix(pks->at, pk + MLKEM_POLYVECBYTES, 1);

  /* NOTE: If a modulus check was conducted on the PK, we know at this
   * point that the coefficients of `pk` are unsigned canonical. The
   * specifications and proofs, however, do _not_ assume this, and instead
   * work with the easily provable bound by MLKEM_UINT12_LIMIT. */
}

/*************************************************
 * Name:        mlk_indcpa_marshal_sk
 *
 * Description: Serialize the secret key
 *
 * Arguments:   - uint8_t *r: pointer to output serialized secret key
 *              - mlk_polyvec *sk: pointer to input vector of polynomials
 *                (secret key)
 *
 * Specification:
 * Implements [FIPS 203, Algorithm 13 (K-PKE.KeyGen), L20]
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_indcpa_marshal_sk(uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                           const mlk_indcpa_secret_key *sks)
{
  mlk_assert_bound_2d(&sks->skpv, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
  mlk_polyvec_tobytes(sk, &sks->skpv);
}

/*************************************************
 * Name:        mlk_indcpa_parse_sk
 *
 * Description: De-serialize the secret key; inverse of mlk_pack_sk
 *
 * Arguments:   - mlk_polyvec *sk: pointer to output vector of polynomials
 *                (secret key)
 *              - const uint8_t *packedsk: pointer to input serialized secret
 *                key
 *
 * Specification:
 * Implements [FIPS 203, Algorithm 15 (K-PKE.Decrypt), L5]
 *
 **************************************************/
MLK_INTERNAL_API
void mlk_indcpa_parse_sk(mlk_indcpa_secret_key *sks,
                         const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES])
{
  mlk_polyvec_frombytes(&sks->skpv, sk);
}

/*************************************************
 * Name:        mlk_pack_ciphertext
 *
 * Description: Serialize the ciphertext as concatenation of the
 *              compressed and serialized vector of polynomials b
 *              and the compressed and serialized polynomial v
 *
 * Arguments:   uint8_t *r: pointer to the output serialized ciphertext
 *              mlk_poly *pk: pointer to the input vector of polynomials b
 *              mlk_poly *v: pointer to the input polynomial v
 *
 * Specification:
 * Implements [FIPS 203, Algorithm 14 (K-PKE.Encrypt), L22-23]
 *
 **************************************************/
static void mlk_pack_ciphertext(uint8_t r[MLKEM_INDCPA_BYTES], mlk_polyvec *b,
                                mlk_poly *v)
{
  mlk_polyvec_compress_du(r, b);
  mlk_poly_compress_dv(r + MLKEM_POLYVECCOMPRESSEDBYTES_DU, v);
}

/*************************************************
 * Name:        mlk_unpack_ciphertext
 *
 * Description: De-serialize and decompress ciphertext from a byte array;
 *              approximate inverse of mlk_pack_ciphertext
 *
 * Arguments:   - mlk_polyvec *b: pointer to the output vector of polynomials b
 *              - mlk_poly *v: pointer to the output polynomial v
 *              - const uint8_t *c: pointer to the input serialized ciphertext
 *
 * Specification:
 * Implements [FIPS 203, Algorithm 15 (K-PKE.Decrypt), L1-4]
 *
 **************************************************/
static void mlk_unpack_ciphertext(mlk_polyvec *b, mlk_poly *v,
                                  const uint8_t c[MLKEM_INDCPA_BYTES])
{
  mlk_polyvec_decompress_du(b, c);
  mlk_poly_decompress_dv(v, c + MLKEM_POLYVECCOMPRESSEDBYTES_DU);
}

#if !defined(MLK_USE_NATIVE_NTT_CUSTOM_ORDER)
/* This namespacing is not done at the top to avoid a naming conflict
 * with native backends, which are currently not yet namespaced. */
#define mlk_poly_permute_bitrev_to_custom \
  MLK_ADD_LEVEL(mlk_poly_permute_bitrev_to_custom)

static MLK_INLINE void mlk_poly_permute_bitrev_to_custom(int16_t data[MLKEM_N])
__contract__(
  /* We don't specify that this should be a permutation, but only
   * that it does not change the bound established at the end of mlk_gen_matrix. */
  requires(memory_no_alias(data, sizeof(int16_t) * MLKEM_N))
  requires(array_bound(data, 0, MLKEM_N, 0, MLKEM_Q))
  assigns(memory_slice(data, sizeof(mlk_poly)))
  ensures(array_bound(data, 0, MLKEM_N, 0, MLKEM_Q))) { ((void)data); }
#endif /* MLK_USE_NATIVE_NTT_CUSTOM_ORDER */

static void mlk_transpose_matrix(mlk_polyvec a[MLKEM_K])
__contract__(
  requires(memory_no_alias(a, MLKEM_K*sizeof(mlk_polyvec)))
  requires(forall(k0, 0, MLKEM_K,
    forall(k1, 0, MLKEM_K,
      array_bound(a[k0].vec[k1].coeffs, 0, MLKEM_N, 0, MLKEM_Q))))
  assigns(memory_slice(a, sizeof(mlk_polyvec) * MLKEM_K))
  ensures(forall(k0, 0, MLKEM_K,
    forall(k1, 0, MLKEM_K,
      array_bound(a[k0].vec[k1].coeffs, 0, MLKEM_N, 0, MLKEM_Q))))
)
{
  unsigned int i, j, k;
  int16_t t;
  for (i = 0; i < MLKEM_K; i++)
  {
    for (j = i + 1; j < MLKEM_K; j++)
    {
      for (k = 0; k < MLKEM_N; k++)
      {
        t = a[i].vec[j].coeffs[k];
        a[i].vec[j].coeffs[k] = a[j].vec[i].coeffs[k];
        a[j].vec[i].coeffs[k] = t;
      }
    }
  }
}

/* Reference: `gen_matrix()` in the reference implementation.
 *            - We use a special subroutine to generate 4 polynomials
 *              at a time, to be able to leverage batched Keccak-f1600
 *              implementations. The reference implementation generates
 *              one matrix entry a time.
 *
 * Not static for benchmarking */
MLK_INTERNAL_API
void mlk_gen_matrix(mlk_polyvec *a, const uint8_t seed[MLKEM_SYMBYTES],
                    int transposed)
{
  unsigned i, j;
  /*
   * We generate four separate seed arrays rather than a single one to work
   * around limitations in CBMC function contracts dealing with disjoint slices
   * of the same parent object.
   */

  MLK_ALIGN uint8_t seed0[MLKEM_SYMBYTES + 2];
  MLK_ALIGN uint8_t seed1[MLKEM_SYMBYTES + 2];
  MLK_ALIGN uint8_t seed2[MLKEM_SYMBYTES + 2];
  MLK_ALIGN uint8_t seed3[MLKEM_SYMBYTES + 2];
  uint8_t *seedxy[4];
  seedxy[0] = seed0;
  seedxy[1] = seed1;
  seedxy[2] = seed2;
  seedxy[3] = seed3;

  for (j = 0; j < 4; j++)
  {
    memcpy(seedxy[j], seed, MLKEM_SYMBYTES);
  }

  /* Sample 4 matrix entries a time. */
  for (i = 0; i < (MLKEM_K * MLKEM_K / 4) * 4; i += 4)
  {
    uint8_t x, y;

    for (j = 0; j < 4; j++)
    {
      x = (i + j) / MLKEM_K;
      y = (i + j) % MLKEM_K;
      if (transposed)
      {
        seedxy[j][MLKEM_SYMBYTES + 0] = x;
        seedxy[j][MLKEM_SYMBYTES + 1] = y;
      }
      else
      {
        seedxy[j][MLKEM_SYMBYTES + 0] = y;
        seedxy[j][MLKEM_SYMBYTES + 1] = x;
      }
    }

    /*
     * This call writes across mlk_polyvec boundaries for K=2 and K=3.
     * This is intentional and safe.
     */
    mlk_poly_rej_uniform_x4(&a[0].vec[0] + i, seedxy);
  }

  /* For MLKEM_K == 3, sample the last entry individually. */
  if (i < MLKEM_K * MLKEM_K)
  {
    uint8_t x, y;
    x = i / MLKEM_K;
    y = i % MLKEM_K;

    if (transposed)
    {
      seed0[MLKEM_SYMBYTES + 0] = x;
      seed0[MLKEM_SYMBYTES + 1] = y;
    }
    else
    {
      seed0[MLKEM_SYMBYTES + 0] = y;
      seed0[MLKEM_SYMBYTES + 1] = x;
    }

    mlk_poly_rej_uniform(&a[0].vec[0] + i, seed0);
    i++;
  }

  mlk_assert(i == MLKEM_K * MLKEM_K);

  /*
   * The public matrix is generated in NTT domain. If the native backend
   * uses a custom order in NTT domain, permute A accordingly.
   */
  for (i = 0; i < MLKEM_K; i++)
  {
    for (j = 0; j < MLKEM_K; j++)
    {
      mlk_poly_permute_bitrev_to_custom(a[i].vec[j].coeffs);
    }
  }

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(seed0, sizeof(seed0));
  mlk_zeroize(seed1, sizeof(seed1));
  mlk_zeroize(seed2, sizeof(seed2));
  mlk_zeroize(seed3, sizeof(seed3));
}

/*************************************************
 * Name:        mlk_matvec_mul
 *
 * Description: Computes matrix-vector product in NTT domain,
 *              via Montgomery multiplication.
 *
 * Arguments:   - mlk_polyvec *out: Pointer to output polynomial vector
 *              - mlk_polyvec a[MLKEM_K]: Input matrix. Must be in NTT domain
 *                  and have coefficients of absolute value < 4096.
 *              - mlk_polyvec *v: Input polynomial vector. Must be in NTT
 *                  domain.
 *              - mlk_polyvec *vc: Mulcache for v, computed via
 *                  mlk_polyvec_mulcache_compute().
 *
 * Specification: Implements [FIPS 203, Section 2.4.7, Eq (2.12), (2.13)]
 *
 **************************************************/
static void mlk_matvec_mul(mlk_polyvec *out, const mlk_polyvec a[MLKEM_K],
                           const mlk_polyvec *v, const mlk_polyvec_mulcache *vc)
__contract__(
  requires(memory_no_alias(out, sizeof(mlk_polyvec)))
  requires(memory_no_alias(a, sizeof(mlk_polyvec) * MLKEM_K))
  requires(memory_no_alias(v, sizeof(mlk_polyvec)))
  requires(memory_no_alias(vc, sizeof(mlk_polyvec_mulcache)))
  requires(forall(k0, 0, MLKEM_K,
    forall(k1, 0, MLKEM_K,
      array_bound(a[k0].vec[k1].coeffs, 0, MLKEM_N, 0, MLKEM_UINT12_LIMIT))))
  assigns(memory_slice(out, sizeof(mlk_polyvec))))
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  __loop__(
    assigns(i, object_whole(out))
    invariant(i <= MLKEM_K))
  {
    mlk_polyvec_basemul_acc_montgomery_cached(&out->vec[i], &a[i], v, vc);
  }
}

/* Reference: `indcpa_keypair_derand()` in the reference implementation.
 *            - We use x4-batched versions of `poly_getnoise` to leverage
 *              batched x4-batched Keccak-f1600.
 *            - We use a different implementation of `gen_matrix()` which
 *              uses x4-batched Keccak-f1600 (see `mlk_gen_matrix()` above).
 *            - We use a mulcache to speed up matrix-vector multiplication.
 *            - We include buffer zeroization.
 */
MLK_INTERNAL_API
void mlk_indcpa_keypair_derand(mlk_indcpa_public_key *pk,
                               mlk_indcpa_secret_key *sk,
                               const uint8_t coins[MLKEM_SYMBYTES])
{
  MLK_ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  const uint8_t *publicseed = buf;
  const uint8_t *noiseseed = buf + MLKEM_SYMBYTES;
  mlk_polyvec e, t;
  mlk_polyvec_mulcache skpv_cache;

  MLK_ALIGN uint8_t coins_with_domain_separator[MLKEM_SYMBYTES + 1];
  /* Concatenate coins with MLKEM_K for domain separation of security levels */
  memcpy(coins_with_domain_separator, coins, MLKEM_SYMBYTES);
  coins_with_domain_separator[MLKEM_SYMBYTES] = MLKEM_K;

  mlk_hash_g(buf, coins_with_domain_separator, MLKEM_SYMBYTES + 1);

  /*
   * Declassify the public seed.
   * Required to use it in conditional-branches in rejection sampling.
   * This is needed because all output of randombytes is marked as secret
   * (=undefined)
   */
  MLK_CT_TESTING_DECLASSIFY(publicseed, MLKEM_SYMBYTES);

  mlk_gen_matrix(pk->at, publicseed, 0 /* no transpose */);

#if MLKEM_K == 2
  mlk_poly_getnoise_eta1_4x(sk->skpv.vec + 0, sk->skpv.vec + 1, e.vec + 0,
                            e.vec + 1, noiseseed, 0, 1, 2, 3);
#elif MLKEM_K == 3
  /*
   * Only the first three output buffers are needed.
   * The laster parameter is a dummy that's overwritten later.
   */
  mlk_poly_getnoise_eta1_4x(sk->skpv.vec + 0, sk->skpv.vec + 1,
                            sk->skpv.vec + 2, pk->pkpv.vec + 0 /* irrelevant */,
                            noiseseed, 0, 1, 2, 0xFF /* irrelevant */);
  /* Same here */
  mlk_poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2,
                            pk->pkpv.vec + 0 /* irrelevant */, noiseseed, 3, 4,
                            5, 0xFF /* irrelevant */);
#elif MLKEM_K == 4
  mlk_poly_getnoise_eta1_4x(sk->skpv.vec + 0, sk->skpv.vec + 1,
                            sk->skpv.vec + 2, sk->skpv.vec + 3, noiseseed, 0, 1,
                            2, 3);
  mlk_poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2, e.vec + 3,
                            noiseseed, 4, 5, 6, 7);
#endif

  mlk_polyvec_ntt(&sk->skpv);
  mlk_polyvec_ntt(&e);

  mlk_polyvec_mulcache_compute(&skpv_cache, &sk->skpv);
  /* TODO: Eliminate the temporary polyvec t -  this is currently needed because
    CBMC proofs break with mlk_matvec_mul(&pk->pkpv, pk->at, &sk->skpv,
    &skpv_cache); because two arguments are part of the same object */

  mlk_matvec_mul(&t, pk->at, &sk->skpv, &skpv_cache);
  memcpy(&pk->pkpv, &t, sizeof(mlk_polyvec));
  mlk_polyvec_tomont(&pk->pkpv);

  mlk_polyvec_add(&pk->pkpv, &e);
  mlk_polyvec_reduce(&pk->pkpv);
  mlk_polyvec_reduce(&sk->skpv);
  memcpy(pk->seed, publicseed, MLKEM_SYMBYTES);
  /**
   * TODO: We can eliminate this by moving the transpose into the matvec_mul
   * Then we can also eliminate the flag from the from the gen_matrix function
   */
  mlk_transpose_matrix(pk->at);


  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(buf, sizeof(buf));
  mlk_zeroize(coins_with_domain_separator, sizeof(coins_with_domain_separator));
  mlk_zeroize(&e, sizeof(e));
  mlk_zeroize(&skpv_cache, sizeof(skpv_cache));
}

/* Reference: `indcpa_enc()` in the reference implementation.
 *            - We use x4-batched versions of `poly_getnoise` to leverage
 *              batched x4-batched Keccak-f1600.
 *            - We use a different implementation of `gen_matrix()` which
 *              uses x4-batched Keccak-f1600 (see `mlk_gen_matrix()` above).
 *            - We use a mulcache to speed up matrix-vector multiplication.
 *            - We include buffer zeroization.
 */
MLK_INTERNAL_API
void mlk_indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                    const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                    const mlk_indcpa_public_key *pk,
                    const uint8_t coins[MLKEM_SYMBYTES])
{
  mlk_polyvec sp, ep, b;
  mlk_poly v, k, epp;
  mlk_polyvec_mulcache sp_cache;
  mlk_poly_frommsg(&k, m);

#if MLKEM_K == 2
  mlk_poly_getnoise_eta1122_4x(sp.vec + 0, sp.vec + 1, ep.vec + 0, ep.vec + 1,
                               coins, 0, 1, 2, 3);
  mlk_poly_getnoise_eta2(&epp, coins, 4);
#elif MLKEM_K == 3
  /*
   * In this call, only the first three output buffers are needed.
   * The last parameter is a dummy that's overwritten later.
   */
  mlk_poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, &b.vec[0],
                            coins, 0, 1, 2, 0xFF);
  /* The fourth output buffer in this call _is_ used. */
  mlk_poly_getnoise_eta2_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, &epp, coins, 3,
                            4, 5, 6);
#elif MLKEM_K == 4
  mlk_poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, sp.vec + 3,
                            coins, 0, 1, 2, 3);
  mlk_poly_getnoise_eta2_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, ep.vec + 3,
                            coins, 4, 5, 6, 7);
  mlk_poly_getnoise_eta2(&epp, coins, 8);
#endif

  mlk_polyvec_ntt(&sp);

  mlk_polyvec_mulcache_compute(&sp_cache, &sp);
  mlk_matvec_mul(&b, pk->at, &sp, &sp_cache);
  mlk_polyvec_basemul_acc_montgomery_cached(&v, &pk->pkpv, &sp, &sp_cache);

  mlk_polyvec_invntt_tomont(&b);
  mlk_poly_invntt_tomont(&v);

  mlk_polyvec_add(&b, &ep);
  mlk_poly_add(&v, &epp);
  mlk_poly_add(&v, &k);

  mlk_polyvec_reduce(&b);
  mlk_poly_reduce(&v);

  mlk_pack_ciphertext(c, &b, &v);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(&sp, sizeof(sp));
  mlk_zeroize(&sp_cache, sizeof(sp_cache));
  mlk_zeroize(&b, sizeof(b));
  mlk_zeroize(&v, sizeof(v));
  mlk_zeroize(&k, sizeof(k));
  mlk_zeroize(&ep, sizeof(ep));
  mlk_zeroize(&epp, sizeof(epp));
}

/* Reference: `indcpa_dec()` in the reference implementation.
 *            - We use a mulcache for the scalar product.
 *            - We include buffer zeroization. */
MLK_INTERNAL_API
void mlk_indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                    const uint8_t c[MLKEM_INDCPA_BYTES],
                    const mlk_indcpa_secret_key *sk)
{
  mlk_polyvec b;
  mlk_poly v, sb;
  mlk_polyvec_mulcache b_cache;

  mlk_unpack_ciphertext(&b, &v, c);

  mlk_polyvec_ntt(&b);
  mlk_polyvec_mulcache_compute(&b_cache, &b);
  mlk_polyvec_basemul_acc_montgomery_cached(&sb, &sk->skpv, &b, &b_cache);
  mlk_poly_invntt_tomont(&sb);

  mlk_poly_sub(&v, &sb);
  mlk_poly_reduce(&v);

  mlk_poly_tomsg(m, &v);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(&b, sizeof(b));
  mlk_zeroize(&b_cache, sizeof(b_cache));
  mlk_zeroize(&v, sizeof(v));
  mlk_zeroize(&sb, sizeof(sb));
}

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef mlk_unpack_pk
#undef mlk_unpack_sk
#undef mlk_pack_ciphertext
#undef mlk_unpack_ciphertext
#undef mlk_matvec_mul
#undef transpose_matrix
#undef mlk_poly_permute_bitrev_to_custom
