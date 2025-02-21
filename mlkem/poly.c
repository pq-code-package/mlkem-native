/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "common.h"
#if !defined(MLK_MULTILEVEL_BUILD_NO_SHARED)

#include <stdint.h>
#include <string.h>
#include "arith_backend.h"
#include "cbmc.h"
#include "debug.h"
#include "poly.h"
#include "sampling.h"
#include "symmetric.h"
#include "verify.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define fqmul MLK_NAMESPACE(fqmul)
#define barrett_reduce MLK_NAMESPACE(barrett_reduce)
#define scalar_signed_to_unsigned_q MLK_NAMESPACE(scalar_signed_to_unsigned_q)

/* Forward NTT Internal functions */
#define ct_butterfly MLK_NAMESPACE(ct_butterfly)
#define ntt_layer123 MLK_NAMESPACE(ntt_layer123)
#define ntt_layer45_butterfly MLK_NAMESPACE(ntt_layer45_butterfly)
#define ntt_layer45 MLK_NAMESPACE(ntt_layer45)
#define ntt_layer6 MLK_NAMESPACE(ntt_layer6)
#define ntt_layer7 MLK_NAMESPACE(ntt_layer7)

/* Inverse NTT Internal functions */
#define gs_butterfly_reduce MLK_NAMESPACE(gs_butterfly_reduce)
#define gs_butterfly_defer MLK_NAMESPACE(gs_butterfly_defer)
#define invntt_layer7_invert MLK_NAMESPACE(invntt_layer7_invert)
#define invntt_layer6 MLK_NAMESPACE(invntt_layer6)
#define invntt_layer54_butterfly MLK_NAMESPACE(invntt_layer54_butterfly)
#define invntt_layer54 MLK_NAMESPACE(invntt_layer54)
#define invntt_layer321 MLK_NAMESPACE(invntt_layer321)

/* End of static namespacing */

#if !defined(MLK_USE_NATIVE_POLY_TOMONT) ||           \
    !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
    !defined(MLK_USE_NATIVE_NTT) || !defined(MLK_USE_NATIVE_INTT)
/*************************************************
 * Name:        fqmul
 *
 * Description: Montgomery multiplication modulo MLKEM_Q
 *
 * Arguments:   - int16_t a: first factor
 *                  Can be any int16_t.
 *              - int16_t b: second factor.
 *                  Must be signed canonical (abs value <(MLKEM_Q+1)/2)
 *
 * Returns 16-bit integer congruent to a*b*R^{-1} mod MLKEM_Q, and
 * smaller than MLKEM_Q in absolute value.
 *
 **************************************************/
static MLK_INLINE int16_t fqmul(int16_t a, int16_t b)
__contract__(
  requires(b > -MLKEM_Q_HALF && b < MLKEM_Q_HALF)
  ensures(return_value > -MLKEM_Q && return_value < MLKEM_Q)
)
{
  int16_t res;
  debug_assert_abs_bound(&b, 1, MLKEM_Q_HALF);

  res = montgomery_reduce((int32_t)a * (int32_t)b);
  /* Bounds:
   * |res| <= ceil(|a| * |b| / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil(2^15 * ((MLKEM_Q - 1)/2) / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil((MLKEM_Q - 1) / 4) + (MLKEM_Q + 1) / 2
   *        < MLKEM_Q
   */

  debug_assert_abs_bound(&res, 1, MLKEM_Q);
  return res;
}
#endif /* !defined(MLK_USE_NATIVE_POLY_TOMONT) ||           \
          !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
          !defined(MLK_USE_NATIVE_NTT) ||                   \
          !defined(MLK_USE_NATIVE_INTT) */

#if !defined(MLK_USE_NATIVE_POLY_REDUCE) || !defined(MLK_USE_NATIVE_INTT)
/*************************************************
 * Name:        barrett_reduce
 *
 * Description: Barrett reduction; given a 16-bit integer a, computes
 *              centered representative congruent to a mod q in
 *              {-(q-1)/2,...,(q-1)/2}
 *
 * Arguments:   - int16_t a: input integer to be reduced
 *
 * Returns:     integer in {-(q-1)/2,...,(q-1)/2} congruent to a modulo q.
 **************************************************/
static MLK_INLINE int16_t barrett_reduce(int16_t a)
__contract__(
  ensures(return_value > -MLKEM_Q_HALF && return_value < MLKEM_Q_HALF)
)
{
  /*
   * To divide by MLKEM_Q using Barrett multiplication, the "magic number"
   * multiplier is round_to_nearest(2**26/MLKEM_Q)
   */
  const int BPOWER = 26;
  const int32_t barrett_multiplier = ((1 << BPOWER) + MLKEM_Q / 2) / MLKEM_Q;

  /*
   * Compute round_to_nearest(a/MLKEM_Q) using the multiplier
   * above and shift by BPOWER places.
   * PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
   * implementation-defined for negative left argument. Here,
   * we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
   */
  const int32_t t = (barrett_multiplier * a + (1 << (BPOWER - 1))) >> BPOWER;

  /*
   * t is in -10 .. +10, so we need 32-bit math to
   * evaluate t * MLKEM_Q and the subsequent subtraction
   */
  int16_t res = (int16_t)(a - t * MLKEM_Q);

  debug_assert_abs_bound(&res, 1, MLKEM_Q_HALF);
  return res;
}
#endif /* !defined(MLK_USE_NATIVE_POLY_REDUCE) || \
          !defined(MLK_USE_NATIVE_INTT) */

#if !defined(MLK_USE_NATIVE_POLY_TOMONT)
MLK_INTERNAL_API
void poly_tomont(poly *r)
{
  unsigned i;
  const int16_t f = 1353; /* check-magic: 1353 == signed_mod(2^32, MLKEM_Q) */
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_abs_bound(r->coeffs, 0, i, MLKEM_Q)))
  {
    r->coeffs[i] = fqmul(r->coeffs[i], f);
  }

  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#else  /* MLK_USE_NATIVE_POLY_TOMONT */
MLK_INTERNAL_API
void poly_tomont(poly *r)
{
  poly_tomont_native(r->coeffs);
  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#endif /* MLK_USE_NATIVE_POLY_TOMONT */

#if !defined(MLK_USE_NATIVE_POLY_REDUCE)
/************************************************************
 * Name: scalar_signed_to_unsigned_q
 *
 * Description: Constant-time conversion of signed representatives
 *              modulo MLKEM_Q within range (-(MLKEM_Q-1) .. (MLKEM_Q-1))
 *              into unsigned representatives within range (0..(MLKEM_Q-1)).
 *
 * Arguments: c: signed coefficient to be converted
 ************************************************************/
static MLK_INLINE uint16_t scalar_signed_to_unsigned_q(int16_t c)
__contract__(
  requires(c > -MLKEM_Q && c < MLKEM_Q)
  ensures(return_value >= 0 && return_value < MLKEM_Q)
  ensures(return_value == (int32_t)c + (((int32_t)c < 0) * MLKEM_Q)))
{
  debug_assert_abs_bound(&c, 1, MLKEM_Q);

  /* Add Q if c is negative, but in constant time */
  c = ct_sel_int16(c + MLKEM_Q, c, ct_cmask_neg_i16(c));

  /* and therefore cast to uint16_t is safe. */
  debug_assert_bound(&c, 1, 0, MLKEM_Q);
  return (uint16_t)c;
}

MLK_INTERNAL_API
void poly_reduce(poly *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_bound(r->coeffs, 0, i, 0, MLKEM_Q)))
  {
    /* Barrett reduction, giving signed canonical representative */
    int16_t t = barrett_reduce(r->coeffs[i]);
    /* Conditional addition to get unsigned canonical representative */
    r->coeffs[i] = scalar_signed_to_unsigned_q(t);
  }

  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#else  /* MLK_USE_NATIVE_POLY_REDUCE */
MLK_INTERNAL_API
void poly_reduce(poly *r)
{
  poly_reduce_native(r->coeffs);
  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#endif /* MLK_USE_NATIVE_POLY_REDUCE */

MLK_INTERNAL_API
void poly_add(poly *r, const poly *b)
{
  unsigned i;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(forall(k0, i, MLKEM_N, r->coeffs[k0] == loop_entry(*r).coeffs[k0]))
    invariant(forall(k1, 0, i, r->coeffs[k1] == loop_entry(*r).coeffs[k1] + b->coeffs[k1])))
  {
    r->coeffs[i] = r->coeffs[i] + b->coeffs[i];
  }
}

MLK_INTERNAL_API
void poly_sub(poly *r, const poly *b)
{
  unsigned i;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(forall(k0, i, MLKEM_N, r->coeffs[k0] == loop_entry(*r).coeffs[k0]))
    invariant(forall(k1, 0, i, r->coeffs[k1] == loop_entry(*r).coeffs[k1] - b->coeffs[k1])))
  {
    r->coeffs[i] = r->coeffs[i] - b->coeffs[i];
  }
}

/* Include zeta table unless NTT, invNTT and mulcache computation
 * have been replaced by native implementations. */
#if !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
    !defined(MLK_USE_NATIVE_NTT) || !defined(MLK_USE_NATIVE_INTT)
#include "zetas.inc"
#endif /* !MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE && \
    !MLK_USE_NATIVE_NTT && !MLK_USE_NATIVE_INTT */

#if !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE)
MLK_INTERNAL_API
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 4; i++)
  __loop__(
    invariant(i <= MLKEM_N / 4)
    invariant(array_abs_bound(x->coeffs, 0, 2 * i, MLKEM_Q)))
  {
    x->coeffs[2 * i + 0] = fqmul(a->coeffs[4 * i + 1], zetas[64 + i]);
    x->coeffs[2 * i + 1] = fqmul(a->coeffs[4 * i + 3], -zetas[64 + i]);
  }

  /*
   * This bound is true for the C implementation, but not needed
   * in the higher level bounds reasoning. It is thus omitted
   * them from the spec to not unnecessarily constrain native
   * implementations, but checked here nonetheless.
   */
  debug_assert_abs_bound(x, MLKEM_N / 2, MLKEM_Q);
}
#else  /* MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE */
MLK_INTERNAL_API
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
{
  poly_mulcache_compute_native(x->coeffs, a->coeffs);
  /* Omitting bounds assertion since native implementations may
   * decide not to use a mulcache. Note that the C backend implementation
   * of poly_basemul_montgomery_cached() does still include the check. */
}
#endif /* MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE */

#if !defined(MLK_USE_NATIVE_NTT)

/* 1.1 Forward NTT - Optimized C implementation
 * --------------------------------------------
 *
 * Overview: this implementation aims to strike a balance
 * between readability, formal verifification of type-safety,
 * and performance.
 *
 * Layer merging
 * -------------
 * In this implementation:
 *  Layers 1,2,3 and merged in function ntt_layer123()
 *  Layers 4 and 5 are merged in function ntt_layer45()
 *  Layer 6 stands alone in function ntt_layer6()
 *  Layer 7 stands alone in function ntt_layer7()
 *
 * This particular merging was determined by experimentation
 * and measurement of performance.
 *
 * Coefficient Reduction
 * ---------------------
 * The code defers reduction of coefficients in the core
 * "butterfly" functions in each layer, so that the coefficients
 * grow in absolute magnitiude by MLKEM_Q after each layer.
 * This growth is reflected and verification in the contracts
 * and loop invariants of each layer and their inner functions.
 *
 * Auto-Vectorization
 * ------------------
 * The code is written in a style that is amenable to auto-vectorization
 * on targets that can support it, and using comtemporary compilers - for
 * example, Graviton/AArch64 or Intel/AVX2 using recent versions of GCC
 * or CLANG.
 *
 * Merging 3 layers results in an inner loop that proceses 8
 * coefficients at a time. Similarly, merging 2 layers results
 * in an inner loop that processes 4 coefficients at a time.
 * Compiler for particlar targets may choose to further unroll
 * or transform these loops as they see fit.
 *
 * Inlining of the inner "butterfly" functions is selectively enabled
 * to allow a compiler to inline, to perform partial application, and
 * vectorization of the top-level layer functions.
 */
#define MLK_NTT_BOUND1 (MLKEM_Q)
#define MLK_NTT_BOUND2 (2 * MLKEM_Q)
#define MLK_NTT_BOUND4 (4 * MLKEM_Q)
#define MLK_NTT_BOUND6 (6 * MLKEM_Q)
#define MLK_NTT_BOUND7 (7 * MLKEM_Q)
#define MLK_NTT_BOUND8 (8 * MLKEM_Q)

/* ct_butterfly() performs a single CT Butterfly step   */
/* in polynomial denoted by r, using the coefficients   */
/* indexed by coeff1_index and coeff2_index, and the    */
/* given value of zeta.                                 */
/*                                                      */
/* NOTE that this function is marked MLK_INLINE for     */
/* compilation (for efficiency) and does not have       */
/* contracts, so it is "inlined for proof" by CBMC      */
/* This allows CBMC to keep track of the ranges of the  */
/* modified coefficients in the calling functions.      */
static MLK_INLINE void ct_butterfly(int16_t r[MLKEM_N],
                                    const unsigned coeff1_index,
                                    const unsigned coeff2_index,
                                    const int16_t zeta)
{
  int16_t t1 = r[coeff1_index];
  int16_t t2 = fqmul(r[coeff2_index], zeta);
  r[coeff1_index] = t1 + t2;
  r[coeff2_index] = t1 - t2;
}

static void ntt_layer123(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND4)))
{
  unsigned j;
  for (j = 0; j < 32; j++)
  __loop__(
    /* A single iteration of this loop updates 8 coefficients 3 times each,
     * meaning their bound jumps from MLK_NTT_BOUND1 to MLK_NTT_BOUND4. Other (as yet
     * untouched) coefficients remain bounded by MLK_NTT_BOUND1. When this loop
     * terminates with j == 32, ALL the coefficients have been updated
     * exactly 3 times, so ALL are bounded by MLK_NTT_BOUND4, which establishes
     * the post-condition */
    invariant(j <= 32)
    invariant(array_abs_bound(r,       0,       j, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,       j,      32, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      32,  j + 32, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 32,      64, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      64,  j + 64, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 64,      96, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      96,  j + 96, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 96,     128, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,     128, j + 128, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r, j + 128,     160, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,     160, j + 160, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r, j + 160,     192, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,     192, j + 192, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r, j + 192,     224, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,     224, j + 224, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r, j + 224, MLKEM_N, MLK_NTT_BOUND1)))
  {
    /* 8 coeffifient indexes, starting at element j */
    /* and increasing in strides of 32              */
    const unsigned ci0 = j;
    const unsigned ci1 = ci0 + 32;
    const unsigned ci2 = ci0 + 64;
    const unsigned ci3 = ci0 + 96;
    const unsigned ci4 = ci0 + 128;
    const unsigned ci5 = ci0 + 160;
    const unsigned ci6 = ci0 + 192;
    const unsigned ci7 = ci0 + 224;

    /* Layer 1 */
    ct_butterfly(r, ci0, ci4, zetas[1]);
    ct_butterfly(r, ci1, ci5, zetas[1]);
    ct_butterfly(r, ci2, ci6, zetas[1]);
    ct_butterfly(r, ci3, ci7, zetas[1]);
    /* Layer 2 */
    ct_butterfly(r, ci0, ci2, zetas[2]);
    ct_butterfly(r, ci1, ci3, zetas[2]);
    ct_butterfly(r, ci4, ci6, zetas[3]);
    ct_butterfly(r, ci5, ci7, zetas[3]);
    /* Layer 3 */
    ct_butterfly(r, ci0, ci1, zetas[4]);
    ct_butterfly(r, ci2, ci3, zetas[5]);
    ct_butterfly(r, ci4, ci5, zetas[6]);
    ct_butterfly(r, ci6, ci7, zetas[7]);
  }
}

static MLK_INLINE void ntt_layer45_butterfly(int16_t r[MLKEM_N],
                                             const unsigned zeta_subtree_index,
                                             const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_subtree_index <= 7)
  requires(start <= 224)
  requires(array_abs_bound(r,          0,   start, MLK_NTT_BOUND6))
  requires(array_abs_bound(r,      start, MLKEM_N, MLK_NTT_BOUND4))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures (array_abs_bound(r,          0, start + 32, MLK_NTT_BOUND6))
  ensures (array_abs_bound(r, start + 32,    MLKEM_N, MLK_NTT_BOUND4)))
{
  const unsigned l4zi = 8 + zeta_subtree_index;
  const unsigned l5zi1 = l4zi * 2;
  const unsigned l5zi2 = l5zi1 + 1;

  const int16_t z1 = zetas[l4zi];
  const int16_t z2 = zetas[l5zi1];
  const int16_t z3 = zetas[l5zi2];

  unsigned j;
  for (j = 0; j < 8; j++)
  __loop__(
    invariant(j <= 8)
    invariant(array_abs_bound(r,              0,          start, MLK_NTT_BOUND6))
    invariant(array_abs_bound(r,      start + 0,      start + j, MLK_NTT_BOUND6))
    invariant(array_abs_bound(r,      start + j,      start + 8, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,      start + 8,  start + j + 8, MLK_NTT_BOUND6))
    invariant(array_abs_bound(r,  start + j + 8,     start + 16, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 16, start + j + 16, MLK_NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 16,     start + 24, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 24, start + j + 24, MLK_NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 24,        MLKEM_N, MLK_NTT_BOUND4)))
  {
    /* 4 coeffifient indexes, starting at element j + start */
    /* and increasing in strides of 8                       */
    const unsigned ci1 = j + start;
    const unsigned ci2 = ci1 + 8;
    const unsigned ci3 = ci1 + 16;
    const unsigned ci4 = ci1 + 24;

    /* Layer 4 */
    ct_butterfly(r, ci1, ci3, z1);
    ct_butterfly(r, ci2, ci4, z1);
    /* Layer 5 */
    ct_butterfly(r, ci1, ci2, z2);
    ct_butterfly(r, ci3, ci4, z3);
  }
}


static void ntt_layer45(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND4))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND6)))
{
  /* Manual unroll here to maximize opportunity to inline and partially apply
   * inner functions. Also avoids a complicated loop invariant
   */
  ntt_layer45_butterfly(r, 0, 0);
  ntt_layer45_butterfly(r, 1, 32);
  ntt_layer45_butterfly(r, 2, 64);
  ntt_layer45_butterfly(r, 3, 96);
  ntt_layer45_butterfly(r, 4, 128);
  ntt_layer45_butterfly(r, 5, 160);
  ntt_layer45_butterfly(r, 6, 192);
  ntt_layer45_butterfly(r, 7, 224);
}

static void ntt_layer6(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND6))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND7)))
{
  unsigned j;
  for (j = 0; j < 32; j++)
  __loop__(
    invariant(j <= 32)
    invariant(array_abs_bound(r,     0,   j * 8, MLK_NTT_BOUND7))
    invariant(array_abs_bound(r, j * 8, MLKEM_N, MLK_NTT_BOUND6)))
  {
    const int16_t zeta = zetas[j + 32];
    const unsigned ci0 = j * 8;

    /* Process 8 coefficients here, all of which need the same Zeta value */
    ct_butterfly(r, ci0, ci0 + 4, zeta);
    ct_butterfly(r, ci0 + 1, ci0 + 5, zeta);
    ct_butterfly(r, ci0 + 2, ci0 + 6, zeta);
    ct_butterfly(r, ci0 + 3, ci0 + 7, zeta);
  }
}

static void ntt_layer7(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND7))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND8)))
{
  unsigned j;
  for (j = 0; j < 64; j++)
  __loop__(
    invariant(j <= 64)
    invariant(array_abs_bound(r,     0,   j * 4, MLK_NTT_BOUND8))
    invariant(array_abs_bound(r, j * 4, MLKEM_N, MLK_NTT_BOUND7)))
  {
    const int16_t zeta = zetas[j + 64];
    const unsigned ci0 = j * 4;

    /* Process 4 coefficients here, all of which need the same Zeta value */
    ct_butterfly(r, ci0, ci0 + 2, zeta);
    ct_butterfly(r, ci0 + 1, ci0 + 3, zeta);
  }
}

/*
 * Compute full Forward NTT
 */
MLK_INTERNAL_API
void poly_ntt(poly *p)
{
  int16_t *r;
  debug_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  r = p->coeffs;

  ntt_layer123(r);
  ntt_layer45(r);
  ntt_layer6(r);
  ntt_layer7(r);

  /* Check the stronger bound */
  debug_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}

#else  /* MLK_USE_NATIVE_NTT */

MLK_INTERNAL_API
void poly_ntt(poly *p)
{
  debug_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  ntt_native(p->coeffs);
  debug_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}
#endif /* MLK_USE_NATIVE_NTT */

#if !defined(MLK_USE_NATIVE_INTT)

/* 2.1 Inverse NTT - Optimized C implementation
 * --------------------------------------------
 *
 * Layer merging
 * -------------
 * In this implementation:
 *  Layer 7 stands alone in function invntt_layer7_invert()
 *  Layer 6 stands alone in function invntt_layer6()
 *  Layers 5 and 4 are merged in function invntt_layer45()
 *  Layers 3,2,1 and merged in function invntt_layer123()
 *
 * Coefficient Reduction
 * ---------------------
 * In the Inverse NTT, using the GS-Butterfly, coefficients
 * do not grow linearly with respect to the layer numbering.
 * Instead, some coefficients _double_ in absolute magnitude
 * after each layer, meaning that more reduction steps are
 * required to keep coefficients at or below 8*MLKEM_Q, which
 * is the upper limit that can be accomodated in an int16_t object.
 *
 * The basic approach in this implementation is as follows:
 *
 * Layer 7 can accept any int16_t value for all coefficients
 * as inputs, but inverts and reduces all coefficients,
 * meaning inputs to Layer 6 are bounded by MLK_NTT_BOUND1.
 *
 * Layer 6 defers reduction, meaning all coefficents
 * are bounded by MLK_NTT_BOUND2.
 *
 * Layers 5 and 4 are merged. Layer 5 defers reduction, meaning
 * inputs to layer 4 are bounded by MLK_NTT_BOUND4. Layer 4 reduces
 * all coefficeints so that inputs to layer 3 are bounded by
 * MLK_NTT_BOUND1.
 *
 * Layers 3, 2, and 1 are merged. These all defer reduction,
 * resulting in outputs bounded by MLK_NTT_BOUND8.
 *
 * These bounds are all reflected and verified by the contracts
 * and loop invariants below.
 *
 * This layer merging and reduction strategy is NOT optimal, but
 * offers a reasonable balance between performance, readability
 * and verifiability of the code.
 *
 * Auto-Vectorization
 * ------------------
 *
 * As with the Forward NTT, code is wr itten to handle at most
 * 8 coefficents at once, with selective inlining to maximize
 * opportunity for auto-vectorization.
 */

/* gs_butterfly_reduce() performs a single GS Butterfly */
/* step in polynomial denoted by r, using the           */
/* coefficients indexes coeff1_index and coeff2_index   */
/* and the given value of zeta.                         */
/*                                                      */
/* Like ct_butterfly(), this functions is inlined       */
/* for both compilation and proof.                      */
static MLK_INLINE void gs_butterfly_reduce(int16_t r[MLKEM_N],
                                           const unsigned coeff1_index,
                                           const unsigned coeff2_index,
                                           const int16_t zeta)
{
  const int16_t t1 = r[coeff1_index];
  const int16_t t2 = r[coeff2_index];
  r[coeff1_index] = barrett_reduce(t1 + t2);
  r[coeff2_index] = fqmul((t2 - t1), zeta);
}

/* As gs_butterfly_reduce(), but does not reduce the */
/* coefficient denoted by coeff1_index               */
static MLK_INLINE void gs_butterfly_defer(int16_t r[MLKEM_N],
                                          const unsigned coeff1_index,
                                          const unsigned coeff2_index,
                                          const int16_t zeta)
{
  const int16_t t1 = r[coeff1_index];
  const int16_t t2 = r[coeff2_index];
  r[coeff1_index] = t1 + t2;
  r[coeff2_index] = fqmul((t2 - t1), zeta);
}

/*  MONT_F = mont^2/128 = 1441.                                */
/*  Used to invert and reduce coefficients in the Inverse NTT. */
#define MONT_F 1441

static void invntt_layer7_invert(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND1))
)
{
  unsigned i;
  for (i = 0; i < 64; i++)
  __loop__(
    invariant(i <= 64)
    invariant(array_abs_bound(r, 0, i * 4, MLK_NTT_BOUND1))
  )
  {
    /* Process 4 coefficients here, all of which need the same Zeta value */
    const int16_t zeta = zetas[127 - i];
    const unsigned ci0 = i * 4;
    const unsigned ci1 = ci0 + 1;
    const unsigned ci2 = ci0 + 2;
    const unsigned ci3 = ci0 + 3;

    /* Invert and reduce all coefficients here the first time they */
    /* are read. This is efficient, and also means we can accept   */
    /* any int16_t value for all coefficients as input.            */
    r[ci0] = fqmul(r[ci0], MONT_F);
    r[ci1] = fqmul(r[ci1], MONT_F);
    r[ci2] = fqmul(r[ci2], MONT_F);
    r[ci3] = fqmul(r[ci3], MONT_F);

    /* Reduce all coefficients here to meet the precondition of Layer 6 */
    gs_butterfly_reduce(r, ci0, ci2, zeta);
    gs_butterfly_reduce(r, ci1, ci3, zeta);
  }
}

static void invntt_layer6(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND2))
)
{
  unsigned i;
  for (i = 0; i < 32; i++)
  __loop__(
    invariant(i <= 32)
    invariant(array_abs_bound(r, 0,       i * 8, MLK_NTT_BOUND2))
    invariant(array_abs_bound(r, i * 8, MLKEM_N, MLK_NTT_BOUND1))
  )
  {
    const int16_t zeta = zetas[63 - i];
    const unsigned ci0 = i * 8;

    /* Process 8 coefficients here, all of which need the same Zeta value */
    /* Defer reduction of coefficients 0, 1, 2, and 3 here so they        */
    /* are bounded to MLK_NTT_BOUND2 after Layer6                         */
    gs_butterfly_defer(r, ci0, ci0 + 4, zeta);
    gs_butterfly_defer(r, ci0 + 1, ci0 + 5, zeta);
    gs_butterfly_defer(r, ci0 + 2, ci0 + 6, zeta);
    gs_butterfly_defer(r, ci0 + 3, ci0 + 7, zeta);
  }
}


static MLK_INLINE void invntt_layer54_butterfly(int16_t r[MLKEM_N],
                                                const unsigned zeta_index,
                                                const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_index <= 7)
  requires(start <= 224)
  requires(start % 32 == 0)
  requires(array_abs_bound(r, 0,       start, MLK_NTT_BOUND1))
  requires(array_abs_bound(r, start, MLKEM_N, MLK_NTT_BOUND2))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0,          start + 32, MLK_NTT_BOUND1))
  ensures(array_abs_bound(r, start + 32,    MLKEM_N, MLK_NTT_BOUND2))
)
{
  const unsigned l4zi = 8 + zeta_index;
  const unsigned l5zi1 = l4zi * 2;
  const unsigned l5zi2 = l5zi1 + 1;

  const int16_t l4zeta = zetas[l4zi];
  const int16_t l5zeta1 = zetas[l5zi1];
  const int16_t l5zeta2 = zetas[l5zi2];

  unsigned j;
  for (j = 0; j < 8; j++)
  __loop__(
    invariant(j <= 8)
    invariant(array_abs_bound(r,              0,          start, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      start + 0,      start + j, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      start + j,      start + 8, MLK_NTT_BOUND2))
    invariant(array_abs_bound(r,      start + 8,  start + j + 8, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,  start + j + 8,     start + 16, MLK_NTT_BOUND2))
    invariant(array_abs_bound(r,     start + 16, start + j + 16, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r, start + j + 16,     start + 24, MLK_NTT_BOUND2))
    invariant(array_abs_bound(r,     start + 24, start + j + 24, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r, start + j + 24,        MLKEM_N, MLK_NTT_BOUND2)))
  {
    const unsigned ci0 = j + start;
    const unsigned ci8 = ci0 + 8;
    const unsigned ci16 = ci0 + 16;
    const unsigned ci24 = ci0 + 24;

    /* Layer 5 - Defer reduction of coeffs 0 and 16 here */
    gs_butterfly_defer(r, ci0, ci8, l5zeta2);
    gs_butterfly_defer(r, ci16, ci24, l5zeta1);
    /* Layer 4 - reduce all coefficients to be in MLK_NTT_BOUND1 */
    /* to meet the pre-condition of Layer321                     */
    gs_butterfly_reduce(r, ci0, ci16, l4zeta);
    gs_butterfly_reduce(r, ci8, ci24, l4zeta);
  }
}

static void invntt_layer54(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND2))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND1))
)
{
  /* Manual unroll here to maximize opportunity to inline and partially apply
   * inner functions. Also avoids a complicated loop invariant
   */
  invntt_layer54_butterfly(r, 7, 0);
  invntt_layer54_butterfly(r, 6, 32);
  invntt_layer54_butterfly(r, 5, 64);
  invntt_layer54_butterfly(r, 4, 96);
  invntt_layer54_butterfly(r, 3, 128);
  invntt_layer54_butterfly(r, 2, 160);
  invntt_layer54_butterfly(r, 1, 192);
  invntt_layer54_butterfly(r, 0, 224);
}

static void invntt_layer321(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND8)))
{
  unsigned j;
  for (j = 0; j < 32; j++)
  __loop__(
    invariant(j <= 32)
    invariant(array_abs_bound(r,       0,       j, MLK_NTT_BOUND8))
    invariant(array_abs_bound(r,       j,      32, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      32,  j + 32, MLK_NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 32,      64, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      64,  j + 64, MLK_NTT_BOUND2))
    invariant(array_abs_bound(r,  j + 64,      96, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,      96,  j + 96, MLK_NTT_BOUND2))
    invariant(array_abs_bound(r,  j + 96,     128, MLK_NTT_BOUND1))
    invariant(array_abs_bound(r,     128, MLKEM_N, MLK_NTT_BOUND1)))
  {
    const unsigned ci0 = j + 0;
    const unsigned ci32 = j + 32;
    const unsigned ci64 = j + 64;
    const unsigned ci96 = j + 96;
    const unsigned ci128 = j + 128;
    const unsigned ci160 = j + 160;
    const unsigned ci192 = j + 192;
    const unsigned ci224 = j + 224;

    /* Layer 3 */
    gs_butterfly_defer(r, ci0, ci32, zetas[7]);
    gs_butterfly_defer(r, ci64, ci96, zetas[6]);
    gs_butterfly_defer(r, ci128, ci160, zetas[5]);
    gs_butterfly_defer(r, ci192, ci224, zetas[4]);
    /* Layer 2 */
    gs_butterfly_defer(r, ci0, ci64, zetas[3]);
    gs_butterfly_defer(r, ci32, ci96, zetas[3]);
    gs_butterfly_defer(r, ci128, ci192, zetas[2]);
    gs_butterfly_defer(r, ci160, ci224, zetas[2]);
    /* Layer 1 */
    gs_butterfly_defer(r, ci0, ci128, zetas[1]);
    gs_butterfly_defer(r, ci32, ci160, zetas[1]);
    gs_butterfly_defer(r, ci64, ci192, zetas[1]);
    gs_butterfly_defer(r, ci96, ci224, zetas[1]);
  }
}

MLK_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  int16_t *r = p->coeffs;
  invntt_layer7_invert(r);
  invntt_layer6(r);
  invntt_layer54(r);
  invntt_layer321(r);

  debug_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}

#else  /* MLK_USE_NATIVE_INTT */

MLK_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  intt_native(p->coeffs);
  debug_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}
#endif /* MLK_USE_NATIVE_INTT */

#else /* MLK_MULTILEVEL_BUILD_NO_SHARED */

MLK_EMPTY_CU(poly)

#endif /* MLK_MULTILEVEL_BUILD_NO_SHARED */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef fqmul
#undef barrett_reduce
#undef scalar_signed_to_unsigned_q
#undef ct_butterfly
#undef ntt_layer123
#undef ntt_layer45_butterfly
#undef ntt_layer45
#undef ntt_layer6
#undef ntt_layer7
#undef gs_butterfly_reduce
#undef gs_butterfly_defer
#undef invntt_layer7_invert
#undef invntt_layer6
#undef invntt_layer54_butterfly
#undef invntt_layer54
#undef invntt_layer321
#undef MLK_NTT_BOUND1
#undef MLK_NTT_BOUND2
#undef MLK_NTT_BOUND4
#undef MLK_NTT_BOUND6
#undef MLK_NTT_BOUND7
#undef MLK_NTT_BOUND8
#undef MONT_F
