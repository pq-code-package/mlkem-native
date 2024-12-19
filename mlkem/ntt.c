/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "common.h"
#if !defined(MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED)

#include <stdint.h>
#include "arith_backend.h"
#include "debug.h"
#include "ntt.h"
#include "reduce.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define ct_butterfly MLKEM_NAMESPACE(ct_butterfly)
#define ntt_layer123 MLKEM_NAMESPACE(ntt_layer123)
#define ntt_layer45_butterfly MLKEM_NAMESPACE(ntt_layer45_butterfly)
#define ntt_layer45 MLKEM_NAMESPACE(ntt_layer45)
#define ntt_layer6_butterfly MLKEM_NAMESPACE(ntt_layer6_butterfly)
#define ntt_layer6 MLKEM_NAMESPACE(ntt_layer6)
#define ntt_layer7_butterfly MLKEM_NAMESPACE(ntt_layer7_butterfly)
#define ntt_layer7 MLKEM_NAMESPACE(ntt_layer7)

#define gs_butterfly_reduce MLKEM_NAMESPACE(gs_butterfly_reduce)
#define gs_butterfly_defer MLKEM_NAMESPACE(gs_butterfly_defer)
#define invntt_layer7_invert_butterfly \
  MLKEM_NAMESPACE(invntt_layer7_invert_butterfly)
#define invntt_layer7_invert MLKEM_NAMESPACE(invntt_layer7_invert)
#define invntt_layer6_butterfly MLKEM_NAMESPACE(invntt_layer6_butterfly)
#define invntt_layer6 MLKEM_NAMESPACE(invntt_layer6)
#define invntt_layer54_butterfly MLKEM_NAMESPACE(invntt_layer54_butterfly)
#define invntt_layer54 MLKEM_NAMESPACE(invntt_layer54)
#define invntt_layer321 MLKEM_NAMESPACE(invntt_layer321)
/* End of static namespacing */

/* Forward and Inverse NTT for MLKEM
 * =================================
 * Contents:
 *  1. Forward NTT
 *     1.1 Optimized C code implementation
 *     1.2 Binding to native (assembly language) implementation
 *  2. Inverse NTT
 *     2.1 Optimized C code implementation
 *     2.2 Binding to native (assembly language) implementation
 */


/* 1. Forward NTT
 * ==============
 */

#if !defined(MLKEM_USE_NATIVE_NTT)

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
#define NTT_BOUND1 (MLKEM_Q)
#define NTT_BOUND2 (2 * MLKEM_Q)
#define NTT_BOUND4 (4 * MLKEM_Q)
#define NTT_BOUND6 (6 * MLKEM_Q)
#define NTT_BOUND7 (7 * MLKEM_Q)
#define NTT_BOUND8 (8 * MLKEM_Q)

/* Zeta tables are auto-generated into the file zetas.i */
/* That file is included here in the body of the this   */
/* translation unit to make the literal values of the   */
/* constants directly available the compiler in support */
/* of auto-vectorization and optimization of the code   */
#include "zetas.i"

/* ct_butterfly() performs a single CT Butterfly step   */
/* in polynomial denoted by r, using the coefficients   */
/* indexed by coeff1_index and coeff2_index, and the    */
/* given value of zeta.                                 */
/*                                                      */
/* NOTE that this function is marked INLINE for         */
/* compilation (for efficiency) and does not have       */
/* contracts, so it is "inlined for proof" by CBMC      */
/* This allows CBMC to keep track of the ranges of the  */
/* modified coefficients in the calling functions.      */
static INLINE void ct_butterfly(int16_t r[MLKEM_N], const unsigned coeff1_index,
                                const unsigned coeff2_index, const int16_t zeta)
{
  int16_t t1 = r[coeff1_index];
  int16_t t2 = fqmul(r[coeff2_index], zeta);
  r[coeff1_index] = t1 + t2;
  r[coeff2_index] = t1 - t2;
}

static void ntt_layer123(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND4)))
{
  unsigned j;
  for (j = 0; j < 32; j++)
  __loop__(
    /* A single iteration of this loop updates 8 coefficients 3 times each,
     * meaning their bound jumps from NTT_BOUND1 to NTT_BOUND4. Other (as yet
     * untouched) coefficients remain bounded by NTT_BOUND1. When this loop
     * terminates with j == 32, ALL the coefficients have been updated
     * exactly 3 times, so ALL are bounded by NTT_BOUND4, which establishes
     * the post-condition */
    invariant(j <= 32)
    invariant(array_abs_bound(r,       0,       j, NTT_BOUND4))
    invariant(array_abs_bound(r,       j,      32, NTT_BOUND1))
    invariant(array_abs_bound(r,      32,  j + 32, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 32,      64, NTT_BOUND1))
    invariant(array_abs_bound(r,      64,  j + 64, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 64,      96, NTT_BOUND1))
    invariant(array_abs_bound(r,      96,  j + 96, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 96,     128, NTT_BOUND1))
    invariant(array_abs_bound(r,     128, j + 128, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 128,     160, NTT_BOUND1))
    invariant(array_abs_bound(r,     160, j + 160, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 160,     192, NTT_BOUND1))
    invariant(array_abs_bound(r,     192, j + 192, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 192,     224, NTT_BOUND1))
    invariant(array_abs_bound(r,     224, j + 224, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 224, MLKEM_N, NTT_BOUND1)))
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
    ct_butterfly(r, ci0, ci4, l1zeta1);
    ct_butterfly(r, ci1, ci5, l1zeta1);
    ct_butterfly(r, ci2, ci6, l1zeta1);
    ct_butterfly(r, ci3, ci7, l1zeta1);
    /* Layer 2 */
    ct_butterfly(r, ci0, ci2, l2zeta2);
    ct_butterfly(r, ci1, ci3, l2zeta2);
    ct_butterfly(r, ci4, ci6, l2zeta3);
    ct_butterfly(r, ci5, ci7, l2zeta3);
    /* Layer 3 */
    ct_butterfly(r, ci0, ci1, l3zeta4);
    ct_butterfly(r, ci2, ci3, l3zeta5);
    ct_butterfly(r, ci4, ci5, l3zeta6);
    ct_butterfly(r, ci6, ci7, l3zeta7);
  }
}

static INLINE void ntt_layer45_butterfly(int16_t r[MLKEM_N],
                                         const unsigned zeta_subtree_index,
                                         const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_subtree_index <= 7)
  requires(start <= 224)
  requires(array_abs_bound(r,          0,   start, NTT_BOUND6))
  requires(array_abs_bound(r,      start, MLKEM_N, NTT_BOUND4))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures (array_abs_bound(r,          0, start + 32, NTT_BOUND6))
  ensures (array_abs_bound(r, start + 32,    MLKEM_N, NTT_BOUND4)))
{
  const int16_t z1 = layer4_zetas[zeta_subtree_index];
  const int16_t z2 = layer5_even_zetas[zeta_subtree_index];
  const int16_t z3 = layer5_odd_zetas[zeta_subtree_index];

  unsigned j;
  for (j = 0; j < 8; j++)
  __loop__(
    invariant(j <= 8)
    invariant(array_abs_bound(r,              0,          start, NTT_BOUND6))
    invariant(array_abs_bound(r,      start + 0,      start + j, NTT_BOUND6))
    invariant(array_abs_bound(r,      start + j,      start + 8, NTT_BOUND4))
    invariant(array_abs_bound(r,      start + 8,  start + j + 8, NTT_BOUND6))
    invariant(array_abs_bound(r,  start + j + 8,     start + 16, NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 16, start + j + 16, NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 16,     start + 24, NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 24, start + j + 24, NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 24,        MLKEM_N, NTT_BOUND4)))
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
  requires(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND4))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND6)))
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

static INLINE void ntt_layer6_butterfly(int16_t r[MLKEM_N],
                                        const unsigned zeta_index,
                                        const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_index <= 31)
  requires(start <= 248)
  requires(array_abs_bound(r,          0,   start, NTT_BOUND7))
  requires(array_abs_bound(r,      start, MLKEM_N, NTT_BOUND6))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures (array_abs_bound(r,         0, start + 8, NTT_BOUND7))
  ensures (array_abs_bound(r, start + 8,   MLKEM_N, NTT_BOUND6)))
{
  const int16_t zeta = layer6_zetas[zeta_index];

  unsigned j;
  for (j = 0; j < 4; j++)
  __loop__(
    invariant(j <= 4)
    invariant(array_abs_bound(r,             0,         start, NTT_BOUND7))
    invariant(array_abs_bound(r,     start + 0,     start + j, NTT_BOUND7))
    invariant(array_abs_bound(r,     start + j,     start + 4, NTT_BOUND6))
    invariant(array_abs_bound(r,     start + 4, start + j + 4, NTT_BOUND7))
    invariant(array_abs_bound(r, start + j + 4,       MLKEM_N, NTT_BOUND6)))
  {
    const unsigned ci1 = j + start;
    const unsigned ci2 = ci1 + 4;

    ct_butterfly(r, ci1, ci2, zeta);
  }
}

static void ntt_layer6(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND6))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND7)))
{
  unsigned j;
  for (j = 0; j < 32; j++)
  __loop__(
    invariant(j <= 32)
    invariant(array_abs_bound(r,     0,   j * 8, NTT_BOUND7))
    invariant(array_abs_bound(r, j * 8, MLKEM_N, NTT_BOUND6)))
  {
    ntt_layer6_butterfly(r, j, j * 8);
  }
}

static INLINE void ntt_layer7_butterfly(int16_t r[MLKEM_N],
                                        const unsigned zeta_index,
                                        const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_index <= 63)
  requires(start <= 252)
  requires(array_abs_bound(r,          0,   start, NTT_BOUND8))
  requires(array_abs_bound(r,      start, MLKEM_N, NTT_BOUND7))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures (array_abs_bound(r,         0, start + 4, NTT_BOUND8))
  ensures (array_abs_bound(r, start + 4,   MLKEM_N, NTT_BOUND7)))
{
  const int32_t zeta = (int32_t)layer7_zetas[zeta_index];
  const unsigned ci0 = start;
  const unsigned ci1 = ci0 + 1;
  const unsigned ci2 = ci0 + 2;
  const unsigned ci3 = ci0 + 3;

  ct_butterfly(r, ci0, ci2, zeta);
  ct_butterfly(r, ci1, ci3, zeta);
}

static void ntt_layer7(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND7))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND8)))
{
  unsigned j;
  for (j = 0; j < 64; j++)
  __loop__(
    invariant(j <= 64)
    invariant(array_abs_bound(r,     0,   j * 4, NTT_BOUND8))
    invariant(array_abs_bound(r, j * 4, MLKEM_N, NTT_BOUND7)))
  {
    ntt_layer7_butterfly(r, j, j * 4);
  }
}

/*
 * Compute full Forward NTT
 */
MLKEM_NATIVE_INTERNAL_API
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
  debug_assert_abs_bound(p, MLKEM_N, NTT_BOUND);
}

#else  /* MLKEM_USE_NATIVE_NTT */

/* 1.2 Forward NTT - Binding to native implementation
 * --------------------------------------------------
 */

MLKEM_NATIVE_INTERNAL_API
void poly_ntt(poly *p)
{
  debug_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  ntt_native(p);
  debug_assert_abs_bound(p, MLKEM_N, NTT_BOUND);
}
#endif /* MLKEM_USE_NATIVE_NTT */


/* 2. Inverse NTT
 * ==============
 */

#if !defined(MLKEM_USE_NATIVE_INTT)

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
 * meaning inputs to Layer 6 are bounded by NTT_BOUND1.
 *
 * Layer 6 defers reduction, meaning all coefficents
 * are bounded by NTT_BOUND2.
 *
 * Layers 5 and 4 are merged. Layer 5 defers reduction, meaning
 * inputs to layer 4 are bounded by NTT_BOUND4. Layer 4 reduces
 * all coefficeints so that inputs to layer 3 are bounded by
 * NTT_BOUND1.
 *
 * Layers 3, 2, and 1 are merged. These all defer reduction,
 * resulting in outputs bounded by NTT_BOUND8.
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

/*  MONT_F = mont^2/128 = 1441.                                */
/*  Used to invert and reduce coefficients in the Inverse NTT. */
#define MONT_F 1441

/* gs_butterfly_reduce() performs a single GS Butterfly */
/* step in polynomial denoted by r, using the           */
/* coefficients indexes coeff1_index and coeff2_index   */
/* and the given value of zeta.                         */
/*                                                      */
/* Like ct_butterfly(), this functions is inlined       */
/* for both compilation and proof.                      */
static INLINE void gs_butterfly_reduce(int16_t r[MLKEM_N],
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
static INLINE void gs_butterfly_defer(int16_t r[MLKEM_N],
                                      const unsigned coeff1_index,
                                      const unsigned coeff2_index,
                                      const int16_t zeta)
{
  const int16_t t1 = r[coeff1_index];
  const int16_t t2 = r[coeff2_index];
  r[coeff1_index] = t1 + t2;
  r[coeff2_index] = fqmul((t2 - t1), zeta);
}

static INLINE void invntt_layer7_invert_butterfly(int16_t r[MLKEM_N],
                                                  const unsigned zeta_index,
                                                  const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_index <= 63)
  requires(start <= 252)
  requires(array_abs_bound(r, 0, start, NTT_BOUND1))
  requires(array_bound(r, start, start + 4, INT16_MIN, 32768))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, start + 4, NTT_BOUND1))
  ensures(array_bound(r, start + 4, MLKEM_N, INT16_MIN, 32768))
)
{
  const int32_t zeta = (int32_t)layer7_zetas[zeta_index];
  const unsigned ci0 = start;
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

static void invntt_layer7_invert(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND1))
)
{
  unsigned i;
  for (i = 0; i < 64; i++)
  __loop__(
    invariant(i <= 64)
    invariant(array_abs_bound(r, 0, i * 4, NTT_BOUND1))
  )
  {
    invntt_layer7_invert_butterfly(r, 63 - i, i * 4);
  }
}

static INLINE void invntt_layer6_butterfly(int16_t r[MLKEM_N],
                                           const unsigned zeta_index,
                                           const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_index <= 31)
  requires(start <= 248)
  requires(start % 8 == 0)
  requires(array_abs_bound(r, 0,       start, NTT_BOUND2))
  requires(array_abs_bound(r, start, MLKEM_N, NTT_BOUND1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0,       start + 8, NTT_BOUND2))
  ensures(array_abs_bound(r, start + 8, MLKEM_N, NTT_BOUND1))
)
{
  const int32_t zeta = (int32_t)layer6_zetas[zeta_index];
  const unsigned ci0 = start;
  const unsigned ci1 = ci0 + 1;
  const unsigned ci2 = ci0 + 2;
  const unsigned ci3 = ci0 + 3;
  const unsigned ci4 = ci0 + 4;
  const unsigned ci5 = ci0 + 5;
  const unsigned ci6 = ci0 + 6;
  const unsigned ci7 = ci0 + 7;

  /* Defer reduction of coefficients 0, 1, 2, and 3 here so they */
  /* are bounded to NTT_BOUND2 after Layer6                      */
  gs_butterfly_defer(r, ci0, ci4, zeta);
  gs_butterfly_defer(r, ci1, ci5, zeta);
  gs_butterfly_defer(r, ci2, ci6, zeta);
  gs_butterfly_defer(r, ci3, ci7, zeta);
}

static void invntt_layer6(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND2))
)
{
  unsigned i;
  for (i = 0; i < 32; i++)
  __loop__(
    invariant(i <= 32)
    invariant(array_abs_bound(r, 0,       i * 8, NTT_BOUND2))
    invariant(array_abs_bound(r, i * 8, MLKEM_N, NTT_BOUND1))
  )
  {
    invntt_layer6_butterfly(r, 31 - i, i * 8);
  }
}


static INLINE void invntt_layer54_butterfly(int16_t r[MLKEM_N],
                                            const unsigned zeta_index,
                                            const unsigned start)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(zeta_index <= 7)
  requires(start <= 224)
  requires(start % 32 == 0)
  requires(array_abs_bound(r, 0,       start, NTT_BOUND1))
  requires(array_abs_bound(r, start, MLKEM_N, NTT_BOUND2))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0,          start + 32, NTT_BOUND1))
  ensures(array_abs_bound(r, start + 32,    MLKEM_N, NTT_BOUND2))
)
{
  const int16_t l4zeta = layer4_zetas[zeta_index];
  const int16_t l5zeta1 = layer5_even_zetas[zeta_index];
  const int16_t l5zeta2 = layer5_odd_zetas[zeta_index];

  unsigned j;
  for (j = 0; j < 8; j++)
  __loop__(
    invariant(j <= 8)
    invariant(array_abs_bound(r,              0,          start, NTT_BOUND1))
    invariant(array_abs_bound(r,      start + 0,      start + j, NTT_BOUND1))
    invariant(array_abs_bound(r,      start + j,      start + 8, NTT_BOUND2))
    invariant(array_abs_bound(r,      start + 8,  start + j + 8, NTT_BOUND1))
    invariant(array_abs_bound(r,  start + j + 8,     start + 16, NTT_BOUND2))
    invariant(array_abs_bound(r,     start + 16, start + j + 16, NTT_BOUND1))
    invariant(array_abs_bound(r, start + j + 16,     start + 24, NTT_BOUND2))
    invariant(array_abs_bound(r,     start + 24, start + j + 24, NTT_BOUND1))
    invariant(array_abs_bound(r, start + j + 24,        MLKEM_N, NTT_BOUND2)))
  {
    const unsigned ci0 = j + start;
    const unsigned ci8 = ci0 + 8;
    const unsigned ci16 = ci0 + 16;
    const unsigned ci24 = ci0 + 24;

    /* Layer 5 - Defer reduction of coeffs 0 and 16 here */
    gs_butterfly_defer(r, ci0, ci8, l5zeta2);
    gs_butterfly_defer(r, ci16, ci24, l5zeta1);
    /* Layer 4 - reduce all coefficients to be in NTT_BOUND1 */
    /* to meet the pre-condition of Layer321                 */
    gs_butterfly_reduce(r, ci0, ci16, l4zeta);
    gs_butterfly_reduce(r, ci8, ci24, l4zeta);
  }
}

static void invntt_layer54(int16_t r[MLKEM_N])
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND2))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND1))
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
  requires(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND1))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, NTT_BOUND8)))
{
  unsigned j;
  for (j = 0; j < 32; j++)
  __loop__(
    invariant(j <= 32)
    invariant(array_abs_bound(r,       0,       j, NTT_BOUND8))
    invariant(array_abs_bound(r,       j,      32, NTT_BOUND1))
    invariant(array_abs_bound(r,      32,  j + 32, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 32,      64, NTT_BOUND1))
    invariant(array_abs_bound(r,      64,  j + 64, NTT_BOUND2))
    invariant(array_abs_bound(r,  j + 64,      96, NTT_BOUND1))
    invariant(array_abs_bound(r,      96,  j + 96, NTT_BOUND2))
    invariant(array_abs_bound(r,  j + 96,     128, NTT_BOUND1))
    invariant(array_abs_bound(r,     128, MLKEM_N, NTT_BOUND1)))
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
    gs_butterfly_defer(r, ci0, ci32, l3zeta7);
    gs_butterfly_defer(r, ci64, ci96, l3zeta6);
    gs_butterfly_defer(r, ci128, ci160, l3zeta5);
    gs_butterfly_defer(r, ci192, ci224, l3zeta4);
    /* Layer 2 */
    gs_butterfly_defer(r, ci0, ci64, l2zeta3);
    gs_butterfly_defer(r, ci32, ci96, l2zeta3);
    gs_butterfly_defer(r, ci128, ci192, l2zeta2);
    gs_butterfly_defer(r, ci160, ci224, l2zeta2);
    /* Layer 1 */
    gs_butterfly_defer(r, ci0, ci128, l1zeta1);
    gs_butterfly_defer(r, ci32, ci160, l1zeta1);
    gs_butterfly_defer(r, ci64, ci192, l1zeta1);
    gs_butterfly_defer(r, ci96, ci224, l1zeta1);
  }
}

MLKEM_NATIVE_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  int16_t *r = p->coeffs;
  invntt_layer7_invert(r);
  invntt_layer6(r);
  invntt_layer54(r);
  invntt_layer321(r);

  debug_assert_abs_bound(p, MLKEM_N, INVNTT_BOUND);
}

#else  /* MLKEM_USE_NATIVE_INTT */

/* 2.2 Inverse NTT - Binding to native implementation
 * --------------------------------------------------
 */

MLKEM_NATIVE_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  intt_native(p);
  debug_assert_abs_bound(p, MLKEM_N, INVNTT_BOUND);
}
#endif /* MLKEM_USE_NATIVE_INTT */

#else /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */

#define empty_cu_ntt MLKEM_NAMESPACE_K(empty_cu_ntt)
int empty_cu_ntt;

#endif /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */
