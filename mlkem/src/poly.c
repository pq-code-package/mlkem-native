/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [NeonNTT]
 *   Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1
 *   Becker, Hwang, Kannwischer, Yang, Yang
 *   https://eprint.iacr.org/2021/986
 *
 * - [REF]
 *   CRYSTALS-Kyber C reference implementation
 *   Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/kyber/tree/main/ref
 */

#include "common.h"
#if !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include <stdint.h>

#include "cbmc.h"
#include "debug.h"
#include "poly.h"
#include "sampling.h"
#include "symmetric.h"
#include "verify.h"

/*************************************************
 * Name:        mlk_fqmul
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

/* Reference: `fqmul()` in the reference implementation @[REF]. */
static MLK_INLINE int16_t mlk_fqmul(int16_t a, int16_t b)
__contract__(
  requires(b > -MLKEM_Q_HALF && b < MLKEM_Q_HALF)
  ensures(return_value > -MLKEM_Q && return_value < MLKEM_Q)
)
{
  int16_t res;
  mlk_assert_abs_bound(&b, 1, MLKEM_Q_HALF);

  res = mlk_montgomery_reduce((int32_t)a * (int32_t)b);
  /* Bounds:
   * |res| <= ceil(|a| * |b| / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil(2^15 * ((MLKEM_Q - 1)/2) / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil((MLKEM_Q - 1) / 4) + (MLKEM_Q + 1) / 2
   *        < MLKEM_Q
   */

  mlk_assert_abs_bound(&res, 1, MLKEM_Q);
  return res;
}

/*************************************************
 * Name:        mlk_barrett_reduce
 *
 * Description: Barrett reduction; given a 16-bit integer a, computes
 *              centered representative congruent to a mod q in
 *              {-(q-1)/2,...,(q-1)/2}
 *
 * Arguments:   - int16_t a: input integer to be reduced
 *
 * Returns:     integer in {-(q-1)/2,...,(q-1)/2} congruent to a modulo q.
 *
 **************************************************/

/* Reference: `barrett_reduce()` in the reference implementation @[REF]. */
static MLK_INLINE int16_t mlk_barrett_reduce(int16_t a)
__contract__(
  ensures(return_value > -MLKEM_Q_HALF && return_value < MLKEM_Q_HALF)
)
{
  /* Barrett reduction approximates
   * ```
   *     round(a/MLKEM_Q)
   *   = round(a*(2^N/MLKEM_Q))/2^N)
   *  ~= round(a*round(2^N/MLKEM_Q)/2^N)
   * ```
   * Here, we pick N=26.
   */
  const int32_t magic = 20159; /* check-magic: 20159 == round(2^26 / MLKEM_Q) */

  /*
   * PORTABILITY: Right-shift on a signed integer is
   * implementation-defined for negative left argument.
   * Here, we assume it's sign-preserving "arithmetic" shift right.
   * See (C99 6.5.7 (5))
   */
  const int32_t t = (magic * a + (1 << 25)) >> 26;

  /*
   * t is in -10 .. +10, so we need 32-bit math to
   * evaluate t * MLKEM_Q and the subsequent subtraction
   */
  int16_t res = (int16_t)(a - t * MLKEM_Q);

  mlk_assert_abs_bound(&res, 1, MLKEM_Q_HALF);
  return res;
}

/* Reference: `poly_tomont()` in the reference implementation @[REF]. */
MLK_STATIC_TESTABLE void mlk_poly_tomont_c(mlk_poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(mlk_poly)))
  assigns(memory_slice(r, sizeof(mlk_poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_Q))
)
{
  unsigned i;
  const int16_t f = 1353; /* check-magic: 1353 == signed_mod(2^32, MLKEM_Q) */
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_abs_bound(r->coeffs, 0, i, MLKEM_Q)))
  {
    r->coeffs[i] = mlk_fqmul(r->coeffs[i], f);
  }

  mlk_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}

MLK_INTERNAL_API
void mlk_poly_tomont(mlk_poly *r)
{
#if defined(MLK_USE_NATIVE_POLY_TOMONT)
  int ret;
  ret = mlk_poly_tomont_native(r->coeffs);
  if (ret == MLK_NATIVE_FUNC_SUCCESS)
  {
    mlk_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
    return;
  }
#endif /* MLK_USE_NATIVE_POLY_TOMONT */

  mlk_poly_tomont_c(r);
}

/************************************************************
 * Name: mlk_scalar_signed_to_unsigned_q
 *
 * Description: Constant-time conversion of signed representatives
 *              modulo MLKEM_Q within range (-(MLKEM_Q-1) .. (MLKEM_Q-1))
 *              into unsigned representatives within range (0..(MLKEM_Q-1)).
 *
 * Arguments: c: signed coefficient to be converted
 *
 ************************************************************/

/* Reference: Not present in the reference implementation @[REF].
 *            - Used here to implement different semantics of `poly_reduce()`;
 *              see below. in the reference implementation @[REF], this logic is
 *              part of all compression functions (see `compress.c`). */
static MLK_INLINE uint16_t mlk_scalar_signed_to_unsigned_q(int16_t c)
__contract__(
  requires(c > -MLKEM_Q && c < MLKEM_Q)
  ensures(return_value >= 0 && return_value < MLKEM_Q)
  ensures(return_value == (int32_t)c + (((int32_t)c < 0) * MLKEM_Q)))
{
  mlk_assert_abs_bound(&c, 1, MLKEM_Q);

  /* Add Q if c is negative, but in constant time */
  c = mlk_ct_sel_int16(c + MLKEM_Q, c, mlk_ct_cmask_neg_i16(c));

  /* and therefore cast to uint16_t is safe. */
  mlk_assert_bound(&c, 1, 0, MLKEM_Q);
  return (uint16_t)c;
}

/* Reference: `poly_reduce()` in the reference implementation @[REF]
 *            - We use _unsigned_ canonical outputs, while the reference
 *              implementation uses _signed_ canonical outputs.
 *              Accordingly, we need a conditional addition of MLKEM_Q
 *              here to go from signed to unsigned representatives.
 *              This conditional addition is then dropped from all
 *              polynomial compression functions instead (see `compress.c`). */
MLK_STATIC_TESTABLE void mlk_poly_reduce_c(mlk_poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(mlk_poly)))
  assigns(memory_slice(r, sizeof(mlk_poly)))
  ensures(array_bound(r->coeffs, 0, MLKEM_N, 0, MLKEM_Q))
)
{
  unsigned i;

  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_bound(r->coeffs, 0, i, 0, MLKEM_Q)))
  {
    /* Barrett reduction, giving signed canonical representative */
    int16_t t = mlk_barrett_reduce(r->coeffs[i]);
    /* Conditional addition to get unsigned canonical representative */
    r->coeffs[i] = mlk_scalar_signed_to_unsigned_q(t);
  }

  mlk_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}

MLK_INTERNAL_API
void mlk_poly_reduce(mlk_poly *r)
{
#if defined(MLK_USE_NATIVE_POLY_REDUCE)
  int ret;
  ret = mlk_poly_reduce_native(r->coeffs);
  if (ret == MLK_NATIVE_FUNC_SUCCESS)
  {
    mlk_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
    return;
  }
#endif /* MLK_USE_NATIVE_POLY_REDUCE */

  mlk_poly_reduce_c(r);
}

/* Reference: `poly_add()` in the reference implementation @[REF].
 *            - We use destructive version (output=first input) to avoid
 *              reasoning about aliasing in the CBMC specification */
MLK_INTERNAL_API
void mlk_poly_add(mlk_poly *r, const mlk_poly *b)
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

/* Reference: `poly_sub()` in the reference implementation @[REF].
 *            - We use destructive version (output=first input) to avoid
 *              reasoning about aliasing in the CBMC specification */
MLK_INTERNAL_API
void mlk_poly_sub(mlk_poly *r, const mlk_poly *b)
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

#include "zetas.inc"

/* Reference: Does not exist in the reference implementation @[REF].
 *            - The reference implementation does not use a
 *              multiplication cache ('mulcache'). This idea originates
 *              from @[NeonNTT] and is used at the C level here. */
MLK_STATIC_TESTABLE void mlk_poly_mulcache_compute_c(mlk_poly_mulcache *x,
                                                     const mlk_poly *a)
__contract__(
  requires(memory_no_alias(x, sizeof(mlk_poly_mulcache)))
  requires(memory_no_alias(a, sizeof(mlk_poly)))
  assigns(object_whole(x))
)
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 4; i++)
  __loop__(
    invariant(i <= MLKEM_N / 4)
    invariant(array_abs_bound(x->coeffs, 0, 2 * i, MLKEM_Q)))
  {
    x->coeffs[2 * i + 0] = mlk_fqmul(a->coeffs[4 * i + 1], mlk_zetas[64 + i]);
    x->coeffs[2 * i + 1] = mlk_fqmul(a->coeffs[4 * i + 3], -mlk_zetas[64 + i]);
  }

  /*
   * This bound is true for the C implementation, but not needed
   * in the higher level bounds reasoning. It is thus omitted
   * from the spec to not unnecessarily constrain native
   * implementations, but checked here nonetheless.
   */
  mlk_assert_abs_bound(x, MLKEM_N / 2, MLKEM_Q);
}

MLK_INTERNAL_API
void mlk_poly_mulcache_compute(mlk_poly_mulcache *x, const mlk_poly *a)
{
#if defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE)
  int ret;
  ret = mlk_poly_mulcache_compute_native(x->coeffs, a->coeffs);
  if (ret == MLK_NATIVE_FUNC_SUCCESS)
  {
    return;
  }
#endif /* MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE */

  mlk_poly_mulcache_compute_c(x, a);
}

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

/* mlk_ct_butterfly() performs a single CT Butterfly       */
/* step in polynomial denoted by r, using the coefficients */
/* indexed by coeff1_index and coeff2_index, and the       */
/* given value of zeta.                                    */
/*                                                         */
/* NOTE that this function is marked MLK_INLINE for        */
/* compilation (for efficiency) and does not have          */
/* contracts, so it is "inlined for proof" by CBMC         */
/* This allows CBMC to keep track of the ranges of the     */
/* modified coefficients in the calling functions.         */
static MLK_INLINE void mlk_ct_butterfly(int16_t r[MLKEM_N],
                                        const unsigned coeff1_index,
                                        const unsigned coeff2_index,
                                        const int16_t zeta)
{
  int16_t t1 = r[coeff1_index];
  int16_t t2 = mlk_fqmul(r[coeff2_index], zeta);
  r[coeff1_index] = t1 + t2;
  r[coeff2_index] = t1 - t2;
}

static void mlk_ntt_layer123(int16_t r[MLKEM_N])
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
    mlk_ct_butterfly(r, ci0, ci4, mlk_zetas[1]);
    mlk_ct_butterfly(r, ci1, ci5, mlk_zetas[1]);
    mlk_ct_butterfly(r, ci2, ci6, mlk_zetas[1]);
    mlk_ct_butterfly(r, ci3, ci7, mlk_zetas[1]);
    /* Layer 2 */
    mlk_ct_butterfly(r, ci0, ci2, mlk_zetas[2]);
    mlk_ct_butterfly(r, ci1, ci3, mlk_zetas[2]);
    mlk_ct_butterfly(r, ci4, ci6, mlk_zetas[3]);
    mlk_ct_butterfly(r, ci5, ci7, mlk_zetas[3]);
    /* Layer 3 */
    mlk_ct_butterfly(r, ci0, ci1, mlk_zetas[4]);
    mlk_ct_butterfly(r, ci2, ci3, mlk_zetas[5]);
    mlk_ct_butterfly(r, ci4, ci5, mlk_zetas[6]);
    mlk_ct_butterfly(r, ci6, ci7, mlk_zetas[7]);
  }
}

static MLK_INLINE void mlk_ntt_layer45_block(int16_t r[MLKEM_N],
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

  const int16_t z1 = mlk_zetas[l4zi];
  const int16_t z2 = mlk_zetas[l5zi1];
  const int16_t z3 = mlk_zetas[l5zi2];

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
    mlk_ct_butterfly(r, ci1, ci3, z1);
    mlk_ct_butterfly(r, ci2, ci4, z1);
    /* Layer 5 */
    mlk_ct_butterfly(r, ci1, ci2, z2);
    mlk_ct_butterfly(r, ci3, ci4, z3);
  }
}


static void mlk_ntt_layer45(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND4))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND6)))
{
  /* Manual unroll here to maximize opportunity to inline and partially apply
   * inner functions. Also avoids a complicated loop invariant
   */
  mlk_ntt_layer45_block(r, 0, 0);
  mlk_ntt_layer45_block(r, 1, 32);
  mlk_ntt_layer45_block(r, 2, 64);
  mlk_ntt_layer45_block(r, 3, 96);
  mlk_ntt_layer45_block(r, 4, 128);
  mlk_ntt_layer45_block(r, 5, 160);
  mlk_ntt_layer45_block(r, 6, 192);
  mlk_ntt_layer45_block(r, 7, 224);
}

static void mlk_ntt_layer6(int16_t r[MLKEM_N])
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
    const int16_t zeta = mlk_zetas[j + 32];
    const unsigned ci0 = j * 8;

    /* Process 8 coefficients here, all of which need the same Zeta value */
    mlk_ct_butterfly(r, ci0, ci0 + 4, zeta);
    mlk_ct_butterfly(r, ci0 + 1, ci0 + 5, zeta);
    mlk_ct_butterfly(r, ci0 + 2, ci0 + 6, zeta);
    mlk_ct_butterfly(r, ci0 + 3, ci0 + 7, zeta);
  }
}

static void mlk_ntt_layer7(int16_t r[MLKEM_N])
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
    const int16_t zeta = mlk_zetas[j + 64];
    const unsigned ci0 = j * 4;

    /* Process 4 coefficients here, all of which need the same Zeta value */
    mlk_ct_butterfly(r, ci0, ci0 + 2, zeta);
    mlk_ct_butterfly(r, ci0 + 1, ci0 + 3, zeta);
  }
}

/*
 * Compute full Forward NTT
 */

/* Reference: `ntt()` in the reference implementation @[REF].
 * - Iterate over `layer` instead of `len` in the outer loop
 *   to simplify computation of zeta index. */
MLK_STATIC_TESTABLE void mlk_poly_ntt_c(mlk_poly *p)
__contract__(
  requires(memory_no_alias(p, sizeof(mlk_poly)))
  requires(array_abs_bound(p->coeffs, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(p, sizeof(mlk_poly)))
  ensures(array_abs_bound(p->coeffs, 0, MLKEM_N, MLK_NTT_BOUND))
)
{
  int16_t *r;

  mlk_assert_abs_bound(p, MLKEM_N, MLKEM_Q);

  r = p->coeffs;

  mlk_ntt_layer123(r);
  mlk_ntt_layer45(r);
  mlk_ntt_layer6(r);
  mlk_ntt_layer7(r);

  /* Check the stronger bound */
  mlk_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}

MLK_INTERNAL_API
void mlk_poly_ntt(mlk_poly *p)
{
  mlk_assert_abs_bound(p, MLKEM_N, MLKEM_Q);

#if defined(MLK_USE_NATIVE_NTT)
  {
    int ret;
    ret = mlk_ntt_native(p->coeffs);
    if (ret == MLK_NATIVE_FUNC_SUCCESS)
    {
      mlk_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
      return;
    }
  }
#endif /* MLK_USE_NATIVE_NTT */

  mlk_poly_ntt_c(p);
}



/* 2.1 Inverse NTT - Optimized C implementation
 * --------------------------------------------
 *
 * Layer merging
 * -------------
 * In this implementation:
 *  Layer 7 stands alone in function mlk_invntt_layer7_invert()
 *  Layer 6 stands alone in function mlk_invntt_layer6()
 *  Layers 5 and 4 are merged in function mlk_invntt_layer45()
 *  Layers 3,2,1 and merged in function mlk_invntt_layer123()
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

/* mlk_gs_butterfly_reduce() performs a single GS Butterfly */
/* step in polynomial denoted by r, using the               */
/* coefficients indexes coeff1_index and coeff2_index       */
/* and the given value of zeta.                             */
/*                                                          */
/* Like mlk_ct_butterfly(), this functions is inlined       */
/* for both compilation and proof.                          */
static MLK_INLINE void mlk_gs_butterfly_reduce(int16_t r[MLKEM_N],
                                               const unsigned coeff1_index,
                                               const unsigned coeff2_index,
                                               const int16_t zeta)
{
  const int16_t t1 = r[coeff1_index];
  const int16_t t2 = r[coeff2_index];
  r[coeff1_index] = mlk_barrett_reduce(t1 + t2);
  r[coeff2_index] = mlk_fqmul((t2 - t1), zeta);
}

/* As mlk_gs_butterfly_reduce(), but does not reduce the */
/* coefficient denoted by coeff1_index                   */
static MLK_INLINE void mlk_gs_butterfly_defer(int16_t r[MLKEM_N],
                                              const unsigned coeff1_index,
                                              const unsigned coeff2_index,
                                              const int16_t zeta)
{
  const int16_t t1 = r[coeff1_index];
  const int16_t t2 = r[coeff2_index];
  r[coeff1_index] = t1 + t2;
  r[coeff2_index] = mlk_fqmul((t2 - t1), zeta);
}

static void mlk_invntt_layer7_invert(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLK_NTT_BOUND1))
)
{
  const int16_t f = 1441; /* check-magic: 1441 == pow(2,32 - 7,MLKEM_Q) */
  unsigned i;
  for (i = 0; i < 64; i++)
  __loop__(
    invariant(i <= 64)
    invariant(array_abs_bound(r, 0, i * 4, MLK_NTT_BOUND1))
  )
  {
    /* Process 4 coefficients here, all of which need the same Zeta value */
    const int16_t zeta = mlk_zetas[127 - i];
    const unsigned ci0 = i * 4;
    const unsigned ci1 = ci0 + 1;
    const unsigned ci2 = ci0 + 2;
    const unsigned ci3 = ci0 + 3;

    /* Invert and reduce all coefficients here the first time they */
    /* are read. This is efficient, and also means we can accept   */
    /* any int16_t value for all coefficients as input.            */
    r[ci0] = mlk_fqmul(r[ci0], f);
    r[ci1] = mlk_fqmul(r[ci1], f);
    r[ci2] = mlk_fqmul(r[ci2], f);
    r[ci3] = mlk_fqmul(r[ci3], f);

    /* Reduce all coefficients here to meet the precondition of Layer 6 */
    mlk_gs_butterfly_reduce(r, ci0, ci2, zeta);
    mlk_gs_butterfly_reduce(r, ci1, ci3, zeta);
  }
}

static void mlk_invntt_layer6(int16_t r[MLKEM_N])
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
    const int16_t zeta = mlk_zetas[63 - i];
    const unsigned ci0 = i * 8;

    /* Process 8 coefficients here, all of which need the same Zeta value */
    /* Defer reduction of coefficients 0, 1, 2, and 3 here so they        */
    /* are bounded to MLK_NTT_BOUND2 after Layer6                         */
    mlk_gs_butterfly_defer(r, ci0, ci0 + 4, zeta);
    mlk_gs_butterfly_defer(r, ci0 + 1, ci0 + 5, zeta);
    mlk_gs_butterfly_defer(r, ci0 + 2, ci0 + 6, zeta);
    mlk_gs_butterfly_defer(r, ci0 + 3, ci0 + 7, zeta);
  }
}


static MLK_INLINE void mlk_invntt_layer54_block(int16_t r[MLKEM_N],
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

  const int16_t l4zeta = mlk_zetas[l4zi];
  const int16_t l5zeta1 = mlk_zetas[l5zi1];
  const int16_t l5zeta2 = mlk_zetas[l5zi2];

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
    mlk_gs_butterfly_defer(r, ci0, ci8, l5zeta2);
    mlk_gs_butterfly_defer(r, ci16, ci24, l5zeta1);
    /* Layer 4 - reduce all coefficients to be in MLK_NTT_BOUND1 */
    /* to meet the pre-condition of Layer321                     */
    mlk_gs_butterfly_reduce(r, ci0, ci16, l4zeta);
    mlk_gs_butterfly_reduce(r, ci8, ci24, l4zeta);
  }
}

static void mlk_invntt_layer54(int16_t r[MLKEM_N])
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
  mlk_invntt_layer54_block(r, 7, 0);
  mlk_invntt_layer54_block(r, 6, 32);
  mlk_invntt_layer54_block(r, 5, 64);
  mlk_invntt_layer54_block(r, 4, 96);
  mlk_invntt_layer54_block(r, 3, 128);
  mlk_invntt_layer54_block(r, 2, 160);
  mlk_invntt_layer54_block(r, 1, 192);
  mlk_invntt_layer54_block(r, 0, 224);
}

static void mlk_invntt_layer321(int16_t r[MLKEM_N])
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
    mlk_gs_butterfly_defer(r, ci0, ci32, mlk_zetas[7]);
    mlk_gs_butterfly_defer(r, ci64, ci96, mlk_zetas[6]);
    mlk_gs_butterfly_defer(r, ci128, ci160, mlk_zetas[5]);
    mlk_gs_butterfly_defer(r, ci192, ci224, mlk_zetas[4]);
    /* Layer 2 */
    mlk_gs_butterfly_defer(r, ci0, ci64, mlk_zetas[3]);
    mlk_gs_butterfly_defer(r, ci32, ci96, mlk_zetas[3]);
    mlk_gs_butterfly_defer(r, ci128, ci192, mlk_zetas[2]);
    mlk_gs_butterfly_defer(r, ci160, ci224, mlk_zetas[2]);
    /* Layer 1 */
    mlk_gs_butterfly_defer(r, ci0, ci128, mlk_zetas[1]);
    mlk_gs_butterfly_defer(r, ci32, ci160, mlk_zetas[1]);
    mlk_gs_butterfly_defer(r, ci64, ci192, mlk_zetas[1]);
    mlk_gs_butterfly_defer(r, ci96, ci224, mlk_zetas[1]);
  }
}

/* Reference: `invntt()` in the reference implementation @[REF]
 *            - We normalize at the beginning of the inverse NTT,
 *              while the reference implementation normalizes at
 *              the end. This allows us to drop a call to `poly_reduce()`
 *              from the base multiplication. */
MLK_STATIC_TESTABLE void mlk_poly_invntt_tomont_c(mlk_poly *p)
__contract__(
  requires(memory_no_alias(p, sizeof(mlk_poly)))
  assigns(memory_slice(p, sizeof(mlk_poly)))
  ensures(array_abs_bound(p->coeffs, 0, MLKEM_N, MLK_INVNTT_BOUND))
)
{
  int16_t *r = p->coeffs;
  mlk_invntt_layer7_invert(r);
  mlk_invntt_layer6(r);
  mlk_invntt_layer54(r);
  mlk_invntt_layer321(r);

  mlk_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}

MLK_INTERNAL_API
void mlk_poly_invntt_tomont(mlk_poly *p)
{
#if defined(MLK_USE_NATIVE_INTT)
  int ret;
  ret = mlk_intt_native(p->coeffs);
  if (ret == MLK_NATIVE_FUNC_SUCCESS)
  {
    mlk_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
    return;
  }
#endif /* MLK_USE_NATIVE_INTT */

  mlk_poly_invntt_tomont_c(p);
}

#else /* !MLK_CONFIG_MULTILEVEL_NO_SHARED */

MLK_EMPTY_CU(mlk_poly)

#endif /* MLK_CONFIG_MULTILEVEL_NO_SHARED */
