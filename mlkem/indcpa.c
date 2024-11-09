// SPDX-License-Identifier: Apache-2.0
#include "indcpa.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "fips202.h"
#include "fips202x4.h"
#include "indcpa.h"
#include "ntt.h"
#include "params.h"
#include "poly.h"
#include "polyvec.h"
#include "randombytes.h"
#include "rej_uniform.h"
#include "symmetric.h"

#include "arith_native.h"
#include "debug/debug.h"

#include "cbmc.h"

/*************************************************
 * Name:        pack_pk
 *
 * Description: Serialize the public key as concatenation of the
 *              serialized vector of polynomials pk
 *              and the public seed used to generate the matrix A.
 *
 * Arguments:   uint8_t *r: pointer to the output serialized public key
 *              polyvec *pk: pointer to the input public-key polyvec.
 *                Must have coefficients within [0,..,q-1].
 *              const uint8_t *seed: pointer to the input public seed
 **************************************************/
STATIC_TESTABLE
void pack_pk(uint8_t r[MLKEM_INDCPA_PUBLICKEYBYTES], polyvec *pk,
             const uint8_t seed[MLKEM_SYMBYTES])  // clang-format off
REQUIRES(IS_FRESH(r, MLKEM_INDCPA_PUBLICKEYBYTES))
REQUIRES(IS_FRESH(pk, sizeof(polyvec)))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
REQUIRES(FORALL(int, k0, 0, MLKEM_K - 1,
  ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, pk->vec[k0].coeffs, 0, MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(r))  // clang-format on
{
  POLYVEC_BOUND(pk, MLKEM_Q);
  polyvec_tobytes(r, pk);
  memcpy(r + MLKEM_POLYVECBYTES, seed, MLKEM_SYMBYTES);
}

/*************************************************
 * Name:        unpack_pk
 *
 * Description: De-serialize public key from a byte array;
 *              approximate inverse of pack_pk
 *
 * Arguments:   - polyvec *pk: pointer to output public-key polynomial vector
 *                  Coefficients will be normalized to [0,..,q-1].
 *              - uint8_t *seed: pointer to output seed to generate matrix A
 *              - const uint8_t *packedpk: pointer to input serialized public
 *                  key.
 **************************************************/
STATIC_TESTABLE
void unpack_pk(
    polyvec *pk, uint8_t seed[MLKEM_SYMBYTES],
    const uint8_t packedpk[MLKEM_INDCPA_PUBLICKEYBYTES])  // clang-format off
REQUIRES(IS_FRESH(packedpk, MLKEM_INDCPA_PUBLICKEYBYTES))
REQUIRES(IS_FRESH(pk, sizeof(polyvec)))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
ENSURES(FORALL(int, k0, 0, MLKEM_K - 1,
  ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, pk->vec[k0].coeffs, 0, MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(pk))
ASSIGNS(OBJECT_WHOLE(seed))  // clang-format on
{
  polyvec_frombytes(pk, packedpk);
  memcpy(seed, packedpk + MLKEM_POLYVECBYTES, MLKEM_SYMBYTES);

  // TODO! pk must be subject to a "modulus check" at the top-level
  // crypto_kem_enc_derand(). Once that's done, the reduction is no
  // longer necessary here.
  polyvec_reduce(pk);
}

/*************************************************
 * Name:        pack_sk
 *
 * Description: Serialize the secret key
 *
 * Arguments:   - uint8_t *r: pointer to output serialized secret key
 *              - polyvec *sk: pointer to input vector of polynomials (secret
 *key)
 **************************************************/
STATIC_TESTABLE
void pack_sk(uint8_t r[MLKEM_INDCPA_SECRETKEYBYTES],
             polyvec *sk)  // clang-format off
REQUIRES(IS_FRESH(r, MLKEM_INDCPA_SECRETKEYBYTES))
REQUIRES(IS_FRESH(sk, sizeof(polyvec)))
REQUIRES(FORALL(int, k0, 0, MLKEM_K - 1,
  ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, sk->vec[k0].coeffs, 0, MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(r))
// clang-format on
{
  POLYVEC_BOUND(sk, MLKEM_Q);
  polyvec_tobytes(r, sk);
}

/*************************************************
 * Name:        unpack_sk
 *
 * Description: De-serialize the secret key; inverse of pack_sk
 *
 * Arguments:   - polyvec *sk: pointer to output vector of polynomials (secret
 *key)
 *              - const uint8_t *packedsk: pointer to input serialized secret
 *key
 **************************************************/
STATIC_TESTABLE
void unpack_sk(
    polyvec *sk,
    const uint8_t packedsk[MLKEM_INDCPA_SECRETKEYBYTES])  // clang-format off
REQUIRES(IS_FRESH(packedsk, MLKEM_INDCPA_SECRETKEYBYTES))
REQUIRES(IS_FRESH(sk, sizeof(polyvec)))
ENSURES(FORALL(int, k0, 0, MLKEM_K - 1,
  ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, sk->vec[k0].coeffs, 0, MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(sk))  // clang-format on
{
  polyvec_frombytes(sk, packedsk);
  polyvec_reduce(sk);
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
static void pack_ciphertext(uint8_t r[MLKEM_INDCPA_BYTES], polyvec *b,
                            poly *v) {
  polyvec_compress(r, b);
  poly_compress(r + MLKEM_POLYVECCOMPRESSEDBYTES, v);
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
                              const uint8_t c[MLKEM_INDCPA_BYTES]) {
  polyvec_decompress(b, c);
  poly_decompress(v, c + MLKEM_POLYVECCOMPRESSEDBYTES);
}

#define GEN_MATRIX_NBLOCKS \
  ((12 * MLKEM_N / 8 * (1 << 12) / MLKEM_Q + SHAKE128_RATE) / SHAKE128_RATE)

// Generate four A matrix entries from a seed, using rejection
// sampling on the output of a XOF.
// clang-format off
STATIC_TESTABLE
void gen_matrix_entry_x4(poly *vec, uint8_t *seed[4])
  REQUIRES(IS_FRESH(vec, sizeof(poly) * 4))
  REQUIRES(IS_FRESH(seed, sizeof(uint8_t*) * 4))
  REQUIRES(IS_FRESH(seed[0], MLKEM_SYMBYTES + 2))
  REQUIRES(IS_FRESH(seed[1], MLKEM_SYMBYTES + 2))
  REQUIRES(IS_FRESH(seed[2], MLKEM_SYMBYTES + 2))
  REQUIRES(IS_FRESH(seed[3], MLKEM_SYMBYTES + 2))
  ASSIGNS(OBJECT_UPTO(vec, sizeof(poly) * 4))
  ENSURES(ARRAY_IN_BOUNDS(int, k0, 0, MLKEM_N - 1, vec[0].coeffs, 0, (MLKEM_Q - 1)))
  ENSURES(ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, vec[1].coeffs, 0, (MLKEM_Q - 1)))
  ENSURES(ARRAY_IN_BOUNDS(int, k2, 0, MLKEM_N - 1, vec[2].coeffs, 0, (MLKEM_Q - 1)))
  ENSURES(ARRAY_IN_BOUNDS(int, k3, 0, MLKEM_N - 1, vec[3].coeffs, 0, (MLKEM_Q - 1)))
// clang-format on
{
  // Temporary buffers for XOF output before rejection sampling
  uint8_t buf0[GEN_MATRIX_NBLOCKS * SHAKE128_RATE];
  uint8_t buf1[GEN_MATRIX_NBLOCKS * SHAKE128_RATE];
  uint8_t buf2[GEN_MATRIX_NBLOCKS * SHAKE128_RATE];
  uint8_t buf3[GEN_MATRIX_NBLOCKS * SHAKE128_RATE];

  // Tracks the number of coefficients we have already sampled
  unsigned int ctr[KECCAK_WAY];
  keccakx4_state statex;
  unsigned int buflen;

  // seed is MLKEM_SYMBYTES + 2 bytes long, but padded to MLKEM_SYMBYTES + 16
  shake128x4_absorb(&statex, seed[0], seed[1], seed[2], seed[3],
                    MLKEM_SYMBYTES + 2);

  // Initially, squeeze heuristic number of GEN_MATRIX_NBLOCKS.
  // This should generate the matrix entries with high probability.
  shake128x4_squeezeblocks(buf0, buf1, buf2, buf3, GEN_MATRIX_NBLOCKS, &statex);
  buflen = GEN_MATRIX_NBLOCKS * SHAKE128_RATE;
  ctr[0] = rej_uniform(vec[0].coeffs, MLKEM_N, 0, buf0, buflen);
  ctr[1] = rej_uniform(vec[1].coeffs, MLKEM_N, 0, buf1, buflen);
  ctr[2] = rej_uniform(vec[2].coeffs, MLKEM_N, 0, buf2, buflen);
  ctr[3] = rej_uniform(vec[3].coeffs, MLKEM_N, 0, buf3, buflen);

  // So long as not all matrix entries have been generated, squeeze
  // one more block a time until we're done.
  buflen = SHAKE128_RATE;
  while (ctr[0] < MLKEM_N || ctr[1] < MLKEM_N || ctr[2] < MLKEM_N ||
         ctr[3] < MLKEM_N)  // clang-format off
    ASSIGNS(ctr, statex, OBJECT_UPTO(vec, sizeof(poly) * 4), OBJECT_WHOLE(buf0),
       OBJECT_WHOLE(buf1), OBJECT_WHOLE(buf2), OBJECT_WHOLE(buf3))
    INVARIANT(ctr[0] <= MLKEM_N && ctr[1] <= MLKEM_N)
    INVARIANT(ctr[2] <= MLKEM_N && ctr[3] <= MLKEM_N)
    INVARIANT(ctr[0] > 0 ==> ARRAY_IN_BOUNDS(int, k0, 0, ctr[0] - 1, vec[0].coeffs, 0, (MLKEM_Q - 1)))
    INVARIANT(ctr[1] > 0 ==> ARRAY_IN_BOUNDS(int, k1, 0, ctr[1] - 1, vec[1].coeffs, 0, (MLKEM_Q - 1)))
    INVARIANT(ctr[2] > 0 ==> ARRAY_IN_BOUNDS(int, k2, 0, ctr[2] - 1, vec[2].coeffs, 0, (MLKEM_Q - 1)))
    INVARIANT(ctr[3] > 0 ==> ARRAY_IN_BOUNDS(int, k3, 0, ctr[3] - 1, vec[3].coeffs, 0, (MLKEM_Q - 1)))
                            // clang-format on
    {
      shake128x4_squeezeblocks(buf0, buf1, buf2, buf3, 1, &statex);
      ctr[0] = rej_uniform(vec[0].coeffs, MLKEM_N, ctr[0], buf0, buflen);
      ctr[1] = rej_uniform(vec[1].coeffs, MLKEM_N, ctr[1], buf1, buflen);
      ctr[2] = rej_uniform(vec[2].coeffs, MLKEM_N, ctr[2], buf2, buflen);
      ctr[3] = rej_uniform(vec[3].coeffs, MLKEM_N, ctr[3], buf3, buflen);
    }

  shake128x4_ctx_release(&statex);
}

// Generate a single A matrix entry from a seed, using rejection
// sampling on the output of a XOF.
STATIC_TESTABLE
void gen_matrix_entry(poly *entry,
                      uint8_t seed[MLKEM_SYMBYTES + 2])  // clang-format off
  REQUIRES(IS_FRESH(entry, sizeof(poly)))
  REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES + 2))
  ASSIGNS(OBJECT_UPTO(entry, sizeof(poly)))
  ENSURES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, entry->coeffs, 0, (MLKEM_Q - 1)))
{  // clang-format on
  shake128ctx state;
  uint8_t buf[GEN_MATRIX_NBLOCKS * SHAKE128_RATE];
  unsigned int ctr, buflen;

  shake128_absorb(&state, seed, MLKEM_SYMBYTES + 2);

  // Initially, squeeze + sample heuristic number of GEN_MATRIX_NBLOCKS.
  // This should generate the matrix entry with high probability.
  shake128_squeezeblocks(buf, GEN_MATRIX_NBLOCKS, &state);
  buflen = GEN_MATRIX_NBLOCKS * SHAKE128_RATE;
  ctr = rej_uniform(entry->coeffs, MLKEM_N, 0, buf, buflen);

  // Squeeze + sampel one more block a time until we're done
  buflen = SHAKE128_RATE;
  while (ctr < MLKEM_N)  // clang-format off
    ASSIGNS(ctr, state, OBJECT_UPTO(entry, sizeof(poly)), OBJECT_WHOLE(buf))
    INVARIANT(0 <= ctr && ctr <= MLKEM_N)
    INVARIANT(ctr > 0 ==> ARRAY_IN_BOUNDS(int, k, 0, ctr - 1, entry->coeffs,
                                          0, (MLKEM_Q - 1)))  // clang-format on
    {
      shake128_squeezeblocks(buf, 1, &state);
      ctr = rej_uniform(entry->coeffs, MLKEM_N, ctr, buf, SHAKE128_RATE);
    }

  shake128_ctx_release(&state);
}

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
// Not static for benchmarking
void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES],
                int transposed) {
  int i;
  // We generate four separate seed arrays rather than a single one to work
  // around limitations in CBMC function contracts dealing with disjoint slices
  // of the same parent object.
  uint8_t seed0[MLKEM_SYMBYTES + 2] ALIGN;
  uint8_t seed1[MLKEM_SYMBYTES + 2] ALIGN;
  uint8_t seed2[MLKEM_SYMBYTES + 2] ALIGN;
  uint8_t seed3[MLKEM_SYMBYTES + 2] ALIGN;
  uint8_t *seedxy[] = {seed0, seed1, seed2, seed3};

  for (unsigned j = 0; j < KECCAK_WAY; j++) {
    memcpy(seedxy[j], seed, MLKEM_SYMBYTES);
  }

  // TODO: All loops in this function should be unrolled for decent
  // performance.
  //
  // Either add suitable pragmas, or split gen_matrix according to MLKEM_K
  // and unroll by hand.
  for (i = 0; i < (MLKEM_K * MLKEM_K / KECCAK_WAY) * KECCAK_WAY;
       i += KECCAK_WAY) {
    uint8_t x, y;

    for (unsigned int j = 0; j < KECCAK_WAY; j++) {
      x = (i + j) / MLKEM_K;
      y = (i + j) % MLKEM_K;
      if (transposed) {
        seedxy[j][MLKEM_SYMBYTES + 0] = x;
        seedxy[j][MLKEM_SYMBYTES + 1] = y;
      } else {
        seedxy[j][MLKEM_SYMBYTES + 0] = y;
        seedxy[j][MLKEM_SYMBYTES + 1] = x;
      }
    }

    // This call writes across polyvec boundaries for K=2 and K=3.
    // This is intentional and safe.
    gen_matrix_entry_x4(&a[0].vec[0] + i, seedxy);
  }

  // For left over polynomial, we use single keccak.
  if (i < MLKEM_K * MLKEM_K) {
    uint8_t x, y;
    x = i / MLKEM_K;
    y = i % MLKEM_K;

    if (transposed) {
      seed0[MLKEM_SYMBYTES + 0] = x;
      seed0[MLKEM_SYMBYTES + 1] = y;
    } else {
      seed0[MLKEM_SYMBYTES + 0] = y;
      seed0[MLKEM_SYMBYTES + 1] = x;
    }

    gen_matrix_entry(&a[0].vec[0] + i, seed0);
    i++;
  }

  ASSERT(i == MLKEM_K * MLKEM_K, "gen_matrix: failed to generate whole matrix");

#if defined(MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER)
  // The public matrix is generated in NTT domain. If the native backend
  // uses a custom order in NTT domain, permute A accordingly.
  for (i = 0; i < MLKEM_K; i++) {
    for (int j = 0; j < MLKEM_K; j++) {
      poly_permute_bitrev_to_custom(&a[i].vec[j]);
    }
  }
#endif /* MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER */
}

// clang-format off
STATIC_TESTABLE
void matvec_mul(polyvec *out, polyvec const *a, polyvec const *v,
    polyvec_mulcache const *vc)
  REQUIRES(IS_FRESH(out, sizeof(polyvec)))
  REQUIRES(IS_FRESH(a, sizeof(polyvec) * MLKEM_K))
  REQUIRES(IS_FRESH(v, sizeof(polyvec)))
  REQUIRES(IS_FRESH(vc, sizeof(polyvec_mulcache)))
  REQUIRES(FORALL(int, k0, 0, MLKEM_K - 1,
   FORALL(int, k1, 0, MLKEM_K - 1,
     ARRAY_IN_BOUNDS(int, k2, 0, MLKEM_N - 1,
       a[k0].vec[k1].coeffs, -(MLKEM_Q - 1), (MLKEM_Q - 1)))))
  ASSIGNS(OBJECT_WHOLE(out))
// clang-format on
{
  for (int i = 0; i < MLKEM_K; i++) {
    polyvec_basemul_acc_montgomery_cached(&out->vec[i], &a[i], v, vc);
  }
}

/*************************************************
 * Name:        indcpa_keypair_derand
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
 **************************************************/

STATIC_ASSERT(NTT_BOUND + MLKEM_Q < INT16_MAX, indcpa_enc_bound_0)

void indcpa_keypair_derand(uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                           uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                           const uint8_t coins[MLKEM_SYMBYTES]) {
  uint8_t buf[2 * MLKEM_SYMBYTES] ALIGN;
  const uint8_t *publicseed = buf;
  const uint8_t *noiseseed = buf + MLKEM_SYMBYTES;
  polyvec a[MLKEM_K], e, pkpv, skpv;
  polyvec_mulcache skpv_cache;

  // Add MLKEM_K for domain separation of security levels
  memcpy(buf, coins, MLKEM_SYMBYTES);
  buf[MLKEM_SYMBYTES] = MLKEM_K;
  hash_g(buf, buf, MLKEM_SYMBYTES + 1);

  gen_matrix(a, publicseed, 0 /* no transpose */);

#if MLKEM_K == 2
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, e.vec + 0, e.vec + 1,
                        noiseseed, 0, 1, 2, 3);
#elif MLKEM_K == 3
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, skpv.vec + 2, e.vec + 0,
                        noiseseed, 0, 1, 2, 3);
  poly_getnoise_eta1_4x(e.vec + 1, e.vec + 2, pkpv.vec + 0, pkpv.vec + 1,
                        noiseseed, 4, 5, 6, 7);
#elif MLKEM_K == 4
  poly_getnoise_eta1_4x(skpv.vec + 0, skpv.vec + 1, skpv.vec + 2, skpv.vec + 3,
                        noiseseed, 0, 1, 2, 3);
  poly_getnoise_eta1_4x(e.vec + 0, e.vec + 1, e.vec + 2, e.vec + 3, noiseseed,
                        4, 5, 6, 7);
#endif

  polyvec_ntt(&skpv);
  polyvec_ntt(&e);

  polyvec_mulcache_compute(&skpv_cache, &skpv);
  matvec_mul(&pkpv, a, &skpv, &skpv_cache);
  polyvec_tomont(&pkpv);

  // Arithmetic cannot overflow, see static assertion at the top
  polyvec_add(&pkpv, &e);
  polyvec_reduce(&pkpv);
  polyvec_reduce(&skpv);

  pack_sk(sk, &skpv);
  pack_pk(pk, &pkpv, publicseed);
}

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
 *              - const uint8_t *pk: pointer to input public key
 *                                   (of length MLKEM_INDCPA_PUBLICKEYBYTES)
 *              - const uint8_t *coins: pointer to input random coins used as
 *seed (of length MLKEM_SYMBYTES) to deterministically generate all randomness
 **************************************************/

// Check that the arithmetic in indcpa_enc() does not overflow
STATIC_ASSERT(INVNTT_BOUND + MLKEM_ETA1 < INT16_MAX, indcpa_enc_bound_0)
STATIC_ASSERT(INVNTT_BOUND + MLKEM_ETA2 + MLKEM_Q < INT16_MAX,
              indcpa_enc_bound_1)

void indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                const uint8_t coins[MLKEM_SYMBYTES]) {
  uint8_t seed[MLKEM_SYMBYTES] ALIGN;
  polyvec sp, pkpv, ep, at[MLKEM_K], b;
  poly v, k, epp;
  polyvec_mulcache sp_cache;

  unpack_pk(&pkpv, seed, pk);
  poly_frommsg(&k, m);
  gen_matrix(at, seed, 1 /* transpose */);

#if MLKEM_K == 2
  poly_getnoise_eta1122_4x(sp.vec + 0, sp.vec + 1, ep.vec + 0, ep.vec + 1,
                           coins, 0, 1, 2, 3);
  poly_getnoise_eta2(&epp, coins, 4);
#elif MLKEM_K == 3
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, ep.vec + 0, coins,
                        0, 1, 2, 3);
  poly_getnoise_eta1_4x(ep.vec + 1, ep.vec + 2, &epp, b.vec + 0, coins, 4, 5, 6,
                        7);
#elif MLKEM_K == 4
  poly_getnoise_eta1_4x(sp.vec + 0, sp.vec + 1, sp.vec + 2, sp.vec + 3, coins,
                        0, 1, 2, 3);
  poly_getnoise_eta1_4x(ep.vec + 0, ep.vec + 1, ep.vec + 2, ep.vec + 3, coins,
                        4, 5, 6, 7);
  poly_getnoise_eta2(&epp, coins, 8);
#endif

  polyvec_ntt(&sp);

  polyvec_mulcache_compute(&sp_cache, &sp);
  matvec_mul(&b, at, &sp, &sp_cache);
  polyvec_basemul_acc_montgomery_cached(&v, &pkpv, &sp, &sp_cache);

  polyvec_invntt_tomont(&b);
  poly_invntt_tomont(&v);

  // Arithmetic cannot overflow, see static assertion at the top
  polyvec_add(&b, &ep);
  poly_add(&v, &epp);
  poly_add(&v, &k);

  polyvec_reduce(&b);
  poly_reduce(&v);

  pack_ciphertext(c, &b, &v);
}

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
 *              - const uint8_t *sk: pointer to input secret key
 *                                   (of length MLKEM_INDCPA_SECRETKEYBYTES)
 **************************************************/

// Check that the arithmetic in indcpa_dec() does not overflow
STATIC_ASSERT(INVNTT_BOUND + MLKEM_Q < INT16_MAX, indcpa_dec_bound_0)

void indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES]) {
  polyvec b, skpv;
  poly v, sb;

  unpack_ciphertext(&b, &v, c);
  unpack_sk(&skpv, sk);

  polyvec_ntt(&b);
  polyvec_basemul_acc_montgomery(&sb, &skpv, &b);
  poly_invntt_tomont(&sb);

  // Arithmetic cannot overflow, see static assertion at the top
  poly_sub(&v, &sb);
  poly_reduce(&v);

  poly_tomsg(m, &v);
}
