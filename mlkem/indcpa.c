/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "indcpa.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "fips202/fips202.h"
#include "fips202/fips202x4.h"
#include "indcpa.h"
#include "poly.h"
#include "poly_k.h"
#include "randombytes.h"
#include "sampling.h"
#include "symmetric.h"

#include "arith_backend.h"
#include "debug.h"

#include "cbmc.h"

#ifdef ENABLE_CT_TESTING
#include <valgrind/memcheck.h>
#endif

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define pack_ciphertext MLKEM_NAMESPACE_K(pack_ciphertext)
#define unpack_ciphertext MLKEM_NAMESPACE_K(unpack_ciphertext)
#define matvec_mul MLKEM_NAMESPACE_K(matvec_mul)
/* End of static namespacing */


MLKEM_NATIVE_INTERNAL_API
void indcpa_serialize_pk(uint8_t pks[MLKEM_INDCPA_PUBLICKEYBYTES],
                         const mlkem_indcpa_public_key *pk)
{
  debug_assert_bound_2d(pk->pkpv, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
  polyvec_tobytes(pks, &pk->pkpv);
  memcpy(pks + MLKEM_POLYVECBYTES, pk->seed, MLKEM_SYMBYTES);
}

MLKEM_NATIVE_INTERNAL_API
void indcpa_deserialize_pk(mlkem_indcpa_public_key *pk,
                           const uint8_t pks[MLKEM_INDCPA_PUBLICKEYBYTES])
{
  polyvec_frombytes(&pk->pkpv, pks);
  memcpy(pk->seed, pks + MLKEM_POLYVECBYTES, MLKEM_SYMBYTES);
  gen_matrix(pk->at, pk->seed, 1);


  /* NOTE: If a modulus check was conducted on the PK, we know at this
   * point that the coefficients of `pk` are unsigned canonical. The
   * specifications and proofs, however, do _not_ assume this, and instead
   * work with the easily provable bound by UINT12_LIMIT. */
}

MLKEM_NATIVE_INTERNAL_API
void indcpa_serialize_sk(uint8_t sks[MLKEM_INDCPA_SECRETKEYBYTES],
                         const mlkem_indcpa_secret_key *sk)
{
  debug_assert_bound_2d(&sk->skpv, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
  polyvec_tobytes(sks, &sk->skpv);
}

MLKEM_NATIVE_INTERNAL_API
void indcpa_deserialize_sk(mlkem_indcpa_secret_key *sk,
                           const uint8_t sks[MLKEM_INDCPA_SECRETKEYBYTES])
{
  polyvec_frombytes(&sk->skpv, sks);
}

/*************************************************
 * Name:        pack_ciphertext
 *
 * Description: Serialize the ciphertext as concatenation of the
 *              compressed and serialized vector of polynomials b
 *              and the compressed and serialized polynomial v
 *
 * Arguments:   uint8_t *r: pointer to the output serialized ciphertext
 *              poly *pk: pointer to the input vector of polynomials b
 *              poly *v: pointer to the input polynomial v
 **************************************************/
static void pack_ciphertext(uint8_t r[MLKEM_INDCPA_BYTES], polyvec *b, poly *v)
{
  polyvec_compress_du(r, b);
  poly_compress_dv(r + MLKEM_POLYVECCOMPRESSEDBYTES_DU, v);
}

/*************************************************
 * Name:        unpack_ciphertext
 *
 * Description: De-serialize and decompress ciphertext from a byte array;
 *              approximate inverse of pack_ciphertext
 *
 * Arguments:   - polyvec *b: pointer to the output vector of polynomials b
 *              - poly *v: pointer to the output polynomial v
 *              - const uint8_t *c: pointer to the input serialized ciphertext
 **************************************************/
static void unpack_ciphertext(polyvec *b, poly *v,
                              const uint8_t c[MLKEM_INDCPA_BYTES])
{
  polyvec_decompress_du(b, c);
  poly_decompress_dv(v, c + MLKEM_POLYVECCOMPRESSEDBYTES_DU);
}

#if !defined(MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER)
/* This namespacing is not done at the top to avoid a naming conflict
 * with native backends, which are currently not yet namespaced. */
#define poly_permute_bitrev_to_custom \
  MLKEM_NAMESPACE_K(poly_permute_bitrev_to_custom)

static INLINE void poly_permute_bitrev_to_custom(int16_t data[MLKEM_N])
__contract__(
  /* We don't specify that this should be a permutation, but only
   * that it does not change the bound established at the end of gen_matrix. */
  requires(memory_no_alias(data, sizeof(int16_t) * MLKEM_N))
  requires(array_bound(data, 0, MLKEM_N, 0, MLKEM_Q))
  assigns(memory_slice(data, sizeof(poly)))
  ensures(array_bound(data, 0, MLKEM_N, 0, MLKEM_Q))) { ((void)data); }
#endif /* MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER */

/* Not static for benchmarking */
MLKEM_NATIVE_INTERNAL_API
void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES], int transposed)
{
  unsigned i, j;
  /*
   * We generate four separate seed arrays rather than a single one to work
   * around limitations in CBMC function contracts dealing with disjoint slices
   * of the same parent object.
   */

  ALIGN uint8_t seed0[MLKEM_SYMBYTES + 2];
  ALIGN uint8_t seed1[MLKEM_SYMBYTES + 2];
  ALIGN uint8_t seed2[MLKEM_SYMBYTES + 2];
  ALIGN uint8_t seed3[MLKEM_SYMBYTES + 2];
  uint8_t *seedxy[4];
  seedxy[0] = seed0;
  seedxy[1] = seed1;
  seedxy[2] = seed2;
  seedxy[3] = seed3;

  for (j = 0; j < KECCAK_WAY; j++)
  {
    memcpy(seedxy[j], seed, MLKEM_SYMBYTES);
  }

  for (i = 0; i < (MLKEM_K * MLKEM_K / KECCAK_WAY) * KECCAK_WAY;
       i += KECCAK_WAY)
  {
    uint8_t x, y;

    for (j = 0; j < KECCAK_WAY; j++)
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
     * This call writes across polyvec boundaries for K=2 and K=3.
     * This is intentional and safe.
     */
    poly_rej_uniform_x4(&a[0].vec[0] + i, seedxy);
  }

  /* For left over polynomial, we use single keccak. */
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

    poly_rej_uniform(&a[0].vec[0] + i, seed0);
    i++;
  }

  debug_assert(i == MLKEM_K * MLKEM_K);

  /*
   * The public matrix is generated in NTT domain. If the native backend
   * uses a custom order in NTT domain, permute A accordingly.
   */
  for (i = 0; i < MLKEM_K; i++)
  {
    for (j = 0; j < MLKEM_K; j++)
    {
      poly_permute_bitrev_to_custom(a[i].vec[j].coeffs);
    }
  }
}


static void transpose_matrix(polyvec a[MLKEM_K])
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

/*************************************************
 * Name:        matvec_mul
 *
 * Description: Computes matrix-vector product in NTT domain,
 *              via Montgomery multiplication.
 *
 * Arguments:   - polyvec *out: Pointer to output polynomial vector
 *              - polyvec a[MLKEM_K]: Input matrix. Must be in NTT domain
 *                  and have coefficients of absolute value < 4096.
 *              - polyvec *v: Input polynomial vector. Must be in NTT domain.
 *              - polyvec *vc: Mulcache for v, computed via
 *                  polyvec_mulcache_compute().
 **************************************************/
static void matvec_mul(polyvec *out, const polyvec a[MLKEM_K], const polyvec *v,
                       const polyvec_mulcache *vc)
__contract__(
  requires(memory_no_alias(out, sizeof(polyvec)))
  requires(memory_no_alias(a, sizeof(polyvec) * MLKEM_K))
  requires(memory_no_alias(v, sizeof(polyvec)))
  requires(memory_no_alias(vc, sizeof(polyvec_mulcache)))
  requires(forall(k0, 0, MLKEM_K,
    forall(k1, 0, MLKEM_K,
      array_bound(a[k0].vec[k1].coeffs, 0, MLKEM_N, 0, UINT12_LIMIT))))
  assigns(object_whole(out)))
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  __loop__(
    assigns(i, object_whole(out))
    invariant(i <= MLKEM_K))
  {
    polyvec_basemul_acc_montgomery_cached(&out->vec[i], &a[i], v, vc);
  }
}

MLKEM_NATIVE_INTERNAL_API
void indcpa_keypair_derand(mlkem_indcpa_public_key *pk,
                           mlkem_indcpa_secret_key *sk,
                           const uint8_t coins[MLKEM_SYMBYTES])
{
  ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  const uint8_t *publicseed = buf;
  const uint8_t *noiseseed = buf + MLKEM_SYMBYTES;
  polyvec e;
  polyvec_mulcache skpv_cache;

  ALIGN uint8_t coins_with_domain_separator[MLKEM_SYMBYTES + 1];
  /* Concatenate coins with MLKEM_K for domain separation of security levels */
  memcpy(coins_with_domain_separator, coins, MLKEM_SYMBYTES);
  coins_with_domain_separator[MLKEM_SYMBYTES] = MLKEM_K;

  hash_g(buf, coins_with_domain_separator, MLKEM_SYMBYTES + 1);


#ifdef ENABLE_CT_TESTING
  /*
   * Declassify the public seed.
   * Required to use it in conditional-branches in rejection sampling.
   * This is needed because all output of randombytes is marked as secret
   * (=undefined)
   */
  VALGRIND_MAKE_MEM_DEFINED(publicseed, MLKEM_SYMBYTES);
#endif

  gen_matrix(pk->at, publicseed, 0 /* no transpose */);

#if MLKEM_K == 2
  poly_getnoise_eta1_4x(sk->skpv.vec + 0, sk->skpv.vec + 1, e.vec + 0,
                        e.vec + 1, noiseseed, 0, 1, 2, 3);
#elif MLKEM_K == 3
  /*
   * Only the first three output buffers are needed.
   * The laster parameter is a dummy that's overwritten later.
   */
  poly_getnoise_eta1_4x(sk->skpv.vec + 0, sk->skpv.vec + 1, sk->skpv.vec + 2,
                        pk->pkpv.vec + 0 /* irrelevant */, noiseseed, 0, 1, 2,
                        0xFF /* irrelevant */);
  /* Same here */
  poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2,
                        pk->pkpv.vec + 0 /* irrelevant */, noiseseed, 3, 4, 5,
                        0xFF /* irrelevant */);
#elif MLKEM_K == 4
  poly_getnoise_eta1_4x(sk->skpv.vec + 0, sk->skpv.vec + 1, sk->skpv.vec + 2,
                        sk->skpv.vec + 3, noiseseed, 0, 1, 2, 3);
  poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2, e.vec + 3, noiseseed,
                        4, 5, 6, 7);
#endif

  polyvec_ntt(&sk->skpv);
  polyvec_ntt(&e);
  polyvec_mulcache_compute(&skpv_cache, &sk->skpv);
  matvec_mul(&pk->pkpv, pk->at, &sk->skpv, &skpv_cache);
  polyvec_tomont(&pk->pkpv);

  polyvec_add(&pk->pkpv, &e);
  polyvec_reduce(&pk->pkpv);
  polyvec_reduce(&sk->skpv);

  memcpy(pk->seed, publicseed, MLKEM_SYMBYTES);
  // tranpose matrix as encapsulation requires the transpose
  transpose_matrix(pk->at);
}


MLKEM_NATIVE_INTERNAL_API
void indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const mlkem_indcpa_public_key *pk,
                const uint8_t coins[MLKEM_SYMBYTES])
{
  polyvec sp, ep, b;
  poly v, k, epp;
  polyvec_mulcache sp_cache;

  poly_frommsg(&k, m);


#ifdef ENABLE_CT_TESTING
  /*
   * Declassify the public seed.
   * Required to use it in conditional-branches in rejection sampling.
   * This is needed because in re-encryption the publicseed originated from sk
   * which is marked undefined.
   */
  VALGRIND_MAKE_MEM_DEFINED(seed, MLKEM_SYMBYTES);
#endif

#if MLKEM_K == 2
  poly_getnoise_eta1122_4x(sp.vec + 0, sp.vec + 1, ep.vec + 0, ep.vec + 1,
                           coins, 0, 1, 2, 3);
  poly_getnoise_eta2(&epp, coins, 4);
#elif MLKEM_K == 3
  /*
   * In this call, only the first three output buffers are needed.
   * The last parameter is a dummy that's overwritten later.
   */
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, &b.vec[0], coins, 0,
                        1, 2, 0xFF);
  /* The fourth output buffer in this call _is_ used. */
  poly_getnoise_eta2_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, &epp, coins, 3, 4,
                        5, 6);
#elif MLKEM_K == 4
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, sp.vec + 3, coins,
                        0, 1, 2, 3);
  poly_getnoise_eta2_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, ep.vec + 3, coins,
                        4, 5, 6, 7);
  poly_getnoise_eta2(&epp, coins, 8);
#endif

  polyvec_ntt(&sp);

  polyvec_mulcache_compute(&sp_cache, &sp);
  matvec_mul(&b, pk->at, &sp, &sp_cache);
  polyvec_basemul_acc_montgomery_cached(&v, &pk->pkpv, &sp, &sp_cache);

  polyvec_invntt_tomont(&b);
  poly_invntt_tomont(&v);

  polyvec_add(&b, &ep);
  poly_add(&v, &epp);
  poly_add(&v, &k);

  polyvec_reduce(&b);
  poly_reduce(&v);

  pack_ciphertext(c, &b, &v);
}

MLKEM_NATIVE_INTERNAL_API
void indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t c[MLKEM_INDCPA_BYTES],
                const mlkem_indcpa_secret_key *sk)
{
  polyvec b;
  poly v, sb;

  unpack_ciphertext(&b, &v, c);

  polyvec_ntt(&b);
  polyvec_basemul_acc_montgomery(&sb, &sk->skpv, &b);
  poly_invntt_tomont(&sb);

  poly_sub(&v, &sb);
  poly_reduce(&v);

  poly_tomsg(m, &v);
}
