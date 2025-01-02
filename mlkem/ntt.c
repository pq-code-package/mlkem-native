/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stdint.h>

#include "arith_backend.h"
#include "debug/debug.h"
#include "ntt.h"
#include "reduce.h"

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
 * Inner loops of the butterfly functions process at most 8 coefficients
 * at once, since 8 * 16-bit = 128 bits, which is the width of a Vector
 * register on many targets.
 *
 * Inlining of the inner "butterfly" functions is selectively enabled
 * to allow a compiler to inline, to perform partial application, and
 * vectorization of the top-level layer functions.
 */

#define NTT_BOUND1 (MLKEM_Q - 1)
#define NTT_BOUND2 (2 * MLKEM_Q - 1)
#define NTT_BOUND4 (4 * MLKEM_Q - 1)
#define NTT_BOUND6 (6 * MLKEM_Q - 1)
#define NTT_BOUND7 (7 * MLKEM_Q - 1)
#define NTT_BOUND8 (8 * MLKEM_Q - 1)

/* "pc" == "polynomial coefficients" */
typedef int16_t pc[MLKEM_N];

/* Zeta tables are auto-generated into the file zetas.i */
/* That file is included here in the body of the this   */
/* translation unit to make the literal values of the   */
/* constants directly available the compiler in support */
/* of auto-vectorization and optimization of the code   */
#include "zetas.i"

STATIC_NO_INLINE_TESTABLE void ntt_layer123(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND1))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND4)))
{
  int j;
  for (j = 0; j < 32; j++)
  __loop__(
    /* A single iteration of this loop updates 8 coefficients 3 times each,
     * meaning their bound jumps from NTT_BOUND1 to NTT_BOUND4. Other (as yet
     * untouched) coefficients remain bounded by NTT_BOUND1. When this loop
     * terminates with j == 32, ALL the coefficients have been updated
     * exactly 3 times, so ALL are bounded by NTT_BOUND4, which establishes
     * the post-condition */
    invariant(0 <= j && j <= 32)
    invariant(array_abs_bound(r,       0,   j - 1, NTT_BOUND4))
    invariant(array_abs_bound(r,       j,      31, NTT_BOUND1))
    invariant(array_abs_bound(r,      32,  j + 31, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 32,      63, NTT_BOUND1))
    invariant(array_abs_bound(r,      64,  j + 63, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 64,      95, NTT_BOUND1))
    invariant(array_abs_bound(r,      96,  j + 95, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 96,     127, NTT_BOUND1))
    invariant(array_abs_bound(r,     128, j + 127, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 128,     159, NTT_BOUND1))
    invariant(array_abs_bound(r,     160, j + 159, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 160,     191, NTT_BOUND1))
    invariant(array_abs_bound(r,     192, j + 191, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 192,     223, NTT_BOUND1))
    invariant(array_abs_bound(r,     224, j + 223, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 224, (MLKEM_N - 1), NTT_BOUND1)))
  {
    const int ci1 = j + 0;
    const int ci2 = j + 32;
    const int ci3 = j + 64;
    const int ci4 = j + 96;
    const int ci5 = j + 128;
    const int ci6 = j + 160;
    const int ci7 = j + 192;
    const int ci8 = j + 224;
    int16_t t1, t2;

    /* Layer 1 */
    t1 = fqmul(r[ci5], mlkem_l1zeta1);
    t2 = r[ci1];
    r[ci5] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci7], mlkem_l1zeta1);
    t2 = r[ci3];
    r[ci7] = t2 - t1;
    r[ci3] = t2 + t1;

    t1 = fqmul(r[ci6], mlkem_l1zeta1);
    t2 = r[ci2];
    r[ci6] = t2 - t1;
    r[ci2] = t2 + t1;

    t1 = fqmul(r[ci8], mlkem_l1zeta1);
    t2 = r[ci4];
    r[ci8] = t2 - t1;
    r[ci4] = t2 + t1;

    /* Layer 2 */
    t1 = fqmul(r[ci3], mlkem_l2zeta2);
    t2 = r[ci1];
    r[ci3] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci7], mlkem_l2zeta3);
    t2 = r[ci5];
    r[ci7] = t2 - t1;
    r[ci5] = t2 + t1;

    t1 = fqmul(r[ci4], mlkem_l2zeta2);
    t2 = r[ci2];
    r[ci4] = t2 - t1;
    r[ci2] = t2 + t1;

    t1 = fqmul(r[ci8], mlkem_l2zeta3);
    t2 = r[ci6];
    r[ci8] = t2 - t1;
    r[ci6] = t2 + t1;

    /* Layer 3 */
    t1 = fqmul(r[ci2], mlkem_l3zeta4);
    t2 = r[ci1];
    r[ci2] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci4], mlkem_l3zeta5);
    t2 = r[ci3];
    r[ci4] = t2 - t1;
    r[ci3] = t2 + t1;

    t1 = fqmul(r[ci6], mlkem_l3zeta6);
    t2 = r[ci5];
    r[ci6] = t2 - t1;
    r[ci5] = t2 + t1;

    t1 = fqmul(r[ci8], mlkem_l3zeta7);
    t2 = r[ci7];
    r[ci8] = t2 - t1;
    r[ci7] = t2 + t1;
  }
}

STATIC_INLINE_TESTABLE void ntt_layer45_butterfly(pc r, int zeta_subtree_index,
                                                  int start)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(zeta_subtree_index >= 0 && zeta_subtree_index <= 7)
  requires(start >= 0 && start <= 224)
  requires(array_abs_bound(r,          0,    start -  1, NTT_BOUND6))
  requires(array_abs_bound(r,      start, (MLKEM_N - 1), NTT_BOUND4))
  assigns(memory_slice(r, sizeof(pc)))
  ensures (array_abs_bound(r,          0,    start + 31, NTT_BOUND6))
  ensures (array_abs_bound(r, start + 32, (MLKEM_N - 1), NTT_BOUND4)))
{
  const int16_t z1 = mlkem_layer4_zetas[zeta_subtree_index];
  const int16_t z2 = mlkem_layer5_even_zetas[zeta_subtree_index];
  const int16_t z3 = mlkem_layer5_odd_zetas[zeta_subtree_index];

  int j;
  for (j = 0; j < 8; j++)
  __loop__(
    invariant(j >= 0 && j <= 8)
    invariant(array_abs_bound(r,              0,     start -  1, NTT_BOUND6))
    invariant(array_abs_bound(r,      start + 0,  start + j - 1, NTT_BOUND6))
    invariant(array_abs_bound(r,      start + j,      start + 7, NTT_BOUND4))
    invariant(array_abs_bound(r,      start + 8,  start + j + 7, NTT_BOUND6))
    invariant(array_abs_bound(r,  start + j + 8,     start + 15, NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 16, start + j + 15, NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 16,     start + 23, NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 24, start + j + 23, NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 24,  (MLKEM_N - 1), NTT_BOUND4)))
  {
    const int ci1 = j + start;
    const int ci2 = ci1 + 8;
    const int ci3 = ci1 + 16;
    const int ci4 = ci1 + 24;
    int16_t t1, t2;

    /* Layer 4 */
    t1 = fqmul(r[ci3], z1);
    t2 = r[ci1];
    r[ci3] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci4], z1);
    t2 = r[ci2];
    r[ci4] = t2 - t1;
    r[ci2] = t2 + t1;

    /* Layer 5 */
    t1 = fqmul(r[ci2], z2);
    t2 = r[ci1];
    r[ci2] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci4], z3);
    t2 = r[ci3];
    r[ci4] = t2 - t1;
    r[ci3] = t2 + t1;
  }
}


STATIC_NO_INLINE_TESTABLE void ntt_layer45(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND4))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND6)))
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

STATIC_INLINE_TESTABLE void ntt_layer6_butterfly(pc r, const int zeta_index,
                                                 const int start)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(zeta_index >= 0 && zeta_index <= 31)
  requires(start >= 0 && start <= 248)
  requires(array_abs_bound(r,          0,    start -  1, NTT_BOUND7))
  requires(array_abs_bound(r,      start, (MLKEM_N - 1), NTT_BOUND6))
  assigns(memory_slice(r, sizeof(pc)))
  ensures (array_abs_bound(r,         0,     start + 7, NTT_BOUND7))
  ensures (array_abs_bound(r, start + 8, (MLKEM_N - 1), NTT_BOUND6)))
{
  const int16_t zeta = mlkem_layer6_zetas[zeta_index];

  int j;
  for (j = 0; j < 4; j++)
  __loop__(
    invariant(j >= 0 && j <= 4)
    invariant(array_abs_bound(r,             0,     start -  1, NTT_BOUND7))
    invariant(array_abs_bound(r,     start + 0,  start + j - 1, NTT_BOUND7))
    invariant(array_abs_bound(r,     start + j,      start + 3, NTT_BOUND6))
    invariant(array_abs_bound(r,     start + 4,  start + j + 3, NTT_BOUND7))
    invariant(array_abs_bound(r, start + j + 4,  (MLKEM_N - 1), NTT_BOUND6)))
  {
    const int ci1 = j + start;
    const int ci2 = ci1 + 4;
    const int16_t t = fqmul(r[ci2], zeta);
    const int16_t t2 = r[ci1];
    r[ci2] = t2 - t;
    r[ci1] = t2 + t;
  }
}

STATIC_NO_INLINE_TESTABLE void ntt_layer6(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND6))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND7)))
{
  int j;
  for (j = 0; j < 32; j++)
  __loop__(
    invariant(j >= 0 && j <= 32)
    invariant(array_abs_bound(r,     0,     j * 8 - 1, NTT_BOUND7))
    invariant(array_abs_bound(r, j * 8, (MLKEM_N - 1), NTT_BOUND6)))
  {
    ntt_layer6_butterfly(r, j, j * 8);
  }
}

STATIC_INLINE_TESTABLE void ntt_layer7_butterfly(pc r, int zeta_index,
                                                 int start)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(zeta_index >= 0 && zeta_index <= 63)
  requires(start >= 0 && start <= 252)
  requires(array_abs_bound(r,          0,    start -  1, NTT_BOUND8))
  requires(array_abs_bound(r,      start, (MLKEM_N - 1), NTT_BOUND7))
  assigns(memory_slice(r, sizeof(pc)))
  ensures (array_abs_bound(r,         0,     start + 3, NTT_BOUND8))
  ensures (array_abs_bound(r, start + 4, (MLKEM_N - 1), NTT_BOUND7)))
{
  const int32_t zeta = (int32_t)mlkem_layer7_zetas[zeta_index];
  /* Coefficient indexes 0 through 3 */
  const unsigned int ci0 = start;
  const unsigned int ci1 = ci0 + 1;
  const unsigned int ci2 = ci0 + 2;
  const unsigned int ci3 = ci0 + 3;

  /* Read and write coefficients in natural order of
   * increasing memory location
   */
  const int16_t c0 = r[ci0];
  const int16_t c1 = r[ci1];
  const int16_t c2 = r[ci2];
  const int16_t c3 = r[ci3];

  const int16_t zc2 = fqmul(c2, zeta);
  const int16_t zc3 = fqmul(c3, zeta);

  r[ci0] = c0 + zc2;
  r[ci1] = c1 + zc3;
  r[ci2] = c0 - zc2;
  r[ci3] = c1 - zc3;
}

STATIC_NO_INLINE_TESTABLE void ntt_layer7(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND7))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND8)))
{
  int j;
  for (j = 0; j < 64; j++)
  __loop__(
    invariant(j >= 0 && j <= 64)
    invariant(array_abs_bound(r,     0,     j * 4 - 1, NTT_BOUND8))
    invariant(array_abs_bound(r, j * 4, (MLKEM_N - 1), NTT_BOUND7)))
  {
    ntt_layer7_butterfly(r, j, j * 4);
  }
}

/*
 * Compute full Forward NTT
 */
void poly_ntt(poly *p)
{
  int16_t *r;
  POLY_BOUND_MSG(p, MLKEM_Q, "ref ntt input");
  r = p->coeffs;

  ntt_layer123(r);
  ntt_layer45(r);
  ntt_layer6(r);
  ntt_layer7(r);

  /* Check the stronger bound */
  POLY_BOUND_MSG(p, NTT_BOUND, "ref ntt output");
}

#else  /* MLKEM_USE_NATIVE_NTT */

/* 1.2 Forward NTT - Binding to native implementation
 * --------------------------------------------------
 */

/* Check that bound for native NTT implies contractual bound */
STATIC_ASSERT(NTT_BOUND_NATIVE <= NTT_BOUND, invntt_bound)

void poly_ntt(poly *p)
{
  POLY_BOUND_MSG(p, MLKEM_Q, "native ntt input");
  ntt_native(p);
  POLY_BOUND_MSG(p, NTT_BOUND_NATIVE, "native ntt output");
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

/* Check that bound for reference invNTT implies contractual bound */
#define INVNTT_BOUND_REF NTT_BOUND8
STATIC_ASSERT(INVNTT_BOUND_REF <= INVNTT_BOUND, invntt_bound)


/*  MONT_F = mont^2/128 = 1441.                                */
/*  Used to invert and reduce coefficients in the Inverse NTT. */
#define MONT_F 1441

STATIC_INLINE_TESTABLE void invntt_layer7_invert_butterfly(pc r, int zeta_index,
                                                           int start)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(zeta_index >= 0 && zeta_index <= 63)
  requires(start >= 0 && start <= 252)
  requires(array_abs_bound(r, 0, start - 1, NTT_BOUND1))
  requires(array_bound(r, start, start + 3, INT16_MIN, INT16_MAX))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, start + 3, NTT_BOUND1))
  ensures(array_bound(r, start + 4, (MLKEM_N - 1), INT16_MIN, INT16_MAX))
)
{
  const int32_t zeta = (int32_t)mlkem_layer7_zetas[zeta_index];
  const int ci0 = start;
  const int ci1 = ci0 + 1;
  const int ci2 = ci0 + 2;
  const int ci3 = ci0 + 3;

  /* Invert and reduce all coefficients here the first time they */
  /* are read. This is efficient, and also means we can accept   */
  /* any int16_t value for all coefficients as input.            */
  const int16_t c0 = fqmul(r[ci0], MONT_F);
  const int16_t c1 = fqmul(r[ci1], MONT_F);
  const int16_t c2 = fqmul(r[ci2], MONT_F);
  const int16_t c3 = fqmul(r[ci3], MONT_F);

  /* Reduce all coefficients here to meet the precondition of Layer 6 */
  r[ci0] = barrett_reduce(c0 + c2);
  r[ci2] = fqmul((c2 - c0), zeta);

  r[ci1] = barrett_reduce(c1 + c3);
  r[ci3] = fqmul((c3 - c1), zeta);
}

STATIC_NO_INLINE_TESTABLE void invntt_layer7_invert(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, (MLKEM_N - 1), NTT_BOUND1))
)
{
  int i;
  for (i = 0; i < 64; i++)
  __loop__(
    invariant(0 <= i && i <= 64)
    invariant(array_abs_bound(r, 0, (i - 1) * 4 + 3, NTT_BOUND1))
  )
  {
    invntt_layer7_invert_butterfly(r, 63 - i, i * 4);
  }
}

STATIC_INLINE_TESTABLE void invntt_layer6_butterfly(pc r, int zeta_index,
                                                    int start)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(zeta_index >= 0 && zeta_index <= 31)
  requires(start >= 0 && start <= 248)
  requires(start % 8 == 0)
  requires(array_abs_bound(r, 0,     start - 1, NTT_BOUND2))
  requires(array_abs_bound(r, start, (MLKEM_N - 1), NTT_BOUND1))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0,         start + 7, NTT_BOUND2))
  ensures(array_abs_bound(r, start + 8, (MLKEM_N - 1),       NTT_BOUND1))
)
{
  const int32_t zeta = (int32_t)mlkem_layer6_zetas[zeta_index];
  const int ci0 = start;
  const int ci1 = ci0 + 1;
  const int ci2 = ci0 + 2;
  const int ci3 = ci0 + 3;
  const int ci4 = ci0 + 4;
  const int ci5 = ci0 + 5;
  const int ci6 = ci0 + 6;
  const int ci7 = ci0 + 7;
  const int16_t c0 = r[ci0];
  const int16_t c1 = r[ci1];
  const int16_t c2 = r[ci2];
  const int16_t c3 = r[ci3];
  const int16_t c4 = r[ci4];
  const int16_t c5 = r[ci5];
  const int16_t c6 = r[ci6];
  const int16_t c7 = r[ci7];

  /* Defer reduction of coefficients 0, 1, 2, and 3 here so they */
  /* are bounded to NTT_BOUND2 after Layer6                      */
  r[ci0] = c0 + c4;
  r[ci4] = fqmul((c4 - c0), zeta);

  r[ci1] = c1 + c5;
  r[ci5] = fqmul((c5 - c1), zeta);

  r[ci2] = c2 + c6;
  r[ci6] = fqmul((c6 - c2), zeta);

  r[ci3] = c3 + c7;
  r[ci7] = fqmul((c7 - c3), zeta);
}

STATIC_NO_INLINE_TESTABLE void invntt_layer6(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, (MLKEM_N - 1), NTT_BOUND1))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, (MLKEM_N - 1), NTT_BOUND2))
)
{
  int i;
  for (i = 0; i < 32; i++)
  __loop__(
    invariant(0 <= i && i <= 32)
    invariant(array_abs_bound(r, 0,     i * 8 - 1, NTT_BOUND2))
    invariant(array_abs_bound(r, i * 8, (MLKEM_N - 1), NTT_BOUND1))
  )
  {
    invntt_layer6_butterfly(r, 31 - i, i * 8);
  }
}


STATIC_INLINE_TESTABLE void invntt_layer54_butterfly(pc r, int zeta_index,
                                                     int start)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(zeta_index >= 0 && zeta_index <= 7)
  requires(start >= 0 && start <= 224)
  requires(start % 32 == 0)
  requires(array_abs_bound(r, 0,     start - 1, NTT_BOUND1))
  requires(array_abs_bound(r, start, (MLKEM_N - 1), NTT_BOUND2))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0,          start + 31, NTT_BOUND1))
  ensures(array_abs_bound(r, start + 32, (MLKEM_N - 1), NTT_BOUND2))
)
{
  const int16_t l4zeta = mlkem_layer4_zetas[zeta_index];
  const int16_t l5zeta1 = mlkem_layer5_even_zetas[zeta_index];
  const int16_t l5zeta2 = mlkem_layer5_odd_zetas[zeta_index];

  int j;
  for (j = 0; j < 8; j++)
  __loop__(
    invariant(j >= 0 && j <= 8)
    invariant(array_abs_bound(r,              0,     start -  1, NTT_BOUND1))
    invariant(array_abs_bound(r,      start + 0,  start + j - 1, NTT_BOUND1))
    invariant(array_abs_bound(r,      start + j,      start + 7, NTT_BOUND2))
    invariant(array_abs_bound(r,      start + 8,  start + j + 7, NTT_BOUND1))
    invariant(array_abs_bound(r,  start + j + 8,     start + 15, NTT_BOUND2))
    invariant(array_abs_bound(r,     start + 16, start + j + 15, NTT_BOUND1))
    invariant(array_abs_bound(r, start + j + 16,     start + 23, NTT_BOUND2))
    invariant(array_abs_bound(r,     start + 24, start + j + 23, NTT_BOUND1))
    invariant(array_abs_bound(r, start + j + 24,  (MLKEM_N - 1), NTT_BOUND2)))
  {
    const int ci0 = j + start;
    const int ci8 = ci0 + 8;
    const int ci16 = ci0 + 16;
    const int ci24 = ci0 + 24;

    /* Layer 5 */
    {
      const int16_t c0 = r[ci0];
      const int16_t c8 = r[ci8];
      const int16_t c16 = r[ci16];
      const int16_t c24 = r[ci24];

      /* Defer reduction of coeffs 0 and 16 here */
      r[ci0] = c0 + c8;
      r[ci8] = fqmul(c8 - c0, l5zeta2);

      r[ci16] = c16 + c24;
      r[ci24] = fqmul(c24 - c16, l5zeta1);
    }

    /* Layer 4 */
    {
      const int16_t c0 = r[ci0];
      const int16_t c8 = r[ci8];
      const int16_t c16 = r[ci16];
      const int16_t c24 = r[ci24];

      /* In layer 4, reduce all coefficients to be in NTT_BOUND1 */
      /* to meet the pre-condition of Layer321                   */
      r[ci0] = barrett_reduce(c0 + c16);
      r[ci16] = fqmul(c16 - c0, l4zeta);

      r[ci8] = barrett_reduce(c8 + c24);
      r[ci24] = fqmul(c24 - c8, l4zeta);
    }
  }
}

STATIC_NO_INLINE_TESTABLE void invntt_layer54(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, (MLKEM_N - 1), NTT_BOUND2))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, (MLKEM_N - 1), NTT_BOUND1))
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

STATIC_NO_INLINE_TESTABLE void invntt_layer321(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND1))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND8)))
{
  int j;
  for (j = 0; j < 32; j++)
  __loop__(
    invariant(0 <= j && j <= 32)
    invariant(array_abs_bound(r,       0,   j - 1, NTT_BOUND8))
    invariant(array_abs_bound(r,       j,      31, NTT_BOUND1))
    invariant(array_abs_bound(r,      32,  j + 31, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 32,      63, NTT_BOUND1))
    invariant(array_abs_bound(r,      64,  j + 63, NTT_BOUND2))
    invariant(array_abs_bound(r,  j + 64,      95, NTT_BOUND1))
    invariant(array_abs_bound(r,      96,  j + 95, NTT_BOUND2))
    invariant(array_abs_bound(r,  j + 96,     127, NTT_BOUND1))
    invariant(array_abs_bound(r,     128, (MLKEM_N - 1), NTT_BOUND1)))
  {
    const int ci0 = j + 0;
    const int ci32 = j + 32;
    const int ci64 = j + 64;
    const int ci96 = j + 96;
    const int ci128 = j + 128;
    const int ci160 = j + 160;
    const int ci192 = j + 192;
    const int ci224 = j + 224;

    /* Layer 3 */
    {
      const int16_t c0 = r[ci0];
      const int16_t c32 = r[ci32];
      const int16_t c64 = r[ci64];
      const int16_t c96 = r[ci96];
      const int16_t c128 = r[ci128];
      const int16_t c160 = r[ci160];
      const int16_t c192 = r[ci192];
      const int16_t c224 = r[ci224];

      r[ci0] = c0 + c32;
      r[ci32] = fqmul(c32 - c0, mlkem_l3zeta7);

      r[ci64] = c64 + c96;
      r[ci96] = fqmul(c96 - c64, mlkem_l3zeta6);

      r[ci128] = c128 + c160;
      r[ci160] = fqmul(c160 - c128, mlkem_l3zeta5);

      r[ci192] = c192 + c224;
      r[ci224] = fqmul(c224 - c192, mlkem_l3zeta4);
    }

    /* Layer 2 */
    {
      const int16_t c0 = r[ci0];
      const int16_t c32 = r[ci32];
      const int16_t c64 = r[ci64];
      const int16_t c96 = r[ci96];
      const int16_t c128 = r[ci128];
      const int16_t c160 = r[ci160];
      const int16_t c192 = r[ci192];
      const int16_t c224 = r[ci224];

      r[ci0] = c0 + c64;
      r[ci64] = fqmul(c64 - c0, mlkem_l2zeta3);

      r[ci32] = c32 + c96;
      r[ci96] = fqmul(c96 - c32, mlkem_l2zeta3);

      r[ci128] = c128 + c192;
      r[ci192] = fqmul(c192 - c128, mlkem_l2zeta2);

      r[ci160] = c160 + c224;
      r[ci224] = fqmul(c224 - c160, mlkem_l2zeta2);
    }

    /* Layer 1 */
    {
      const int16_t c0 = r[ci0];
      const int16_t c32 = r[ci32];
      const int16_t c64 = r[ci64];
      const int16_t c96 = r[ci96];
      const int16_t c128 = r[ci128];
      const int16_t c160 = r[ci160];
      const int16_t c192 = r[ci192];
      const int16_t c224 = r[ci224];

      r[ci0] = c0 + c128;
      r[ci128] = fqmul(c128 - c0, mlkem_l1zeta1);

      r[ci32] = c32 + c160;
      r[ci160] = fqmul(c160 - c32, mlkem_l1zeta1);

      r[ci64] = c64 + c192;
      r[ci192] = fqmul(c192 - c64, mlkem_l1zeta1);

      r[ci96] = c96 + c224;
      r[ci224] = fqmul(c224 - c96, mlkem_l1zeta1);
    }
  }
}

void poly_invntt_tomont(poly *p)
{
  int16_t *r = p->coeffs;
  invntt_layer7_invert(r);
  invntt_layer6(r);
  invntt_layer54(r);
  invntt_layer321(r);

  POLY_BOUND_MSG(p, INVNTT_BOUND_REF, "ref intt output");
}

#else  /* MLKEM_USE_NATIVE_INTT */

/* 2.2 Inverse NTT - Binding to native implementation
 * --------------------------------------------------
 */

/* Check that bound for native invNTT implies contractual bound */
STATIC_ASSERT(INVNTT_BOUND_NATIVE <= INVNTT_BOUND, invntt_bound)

void poly_invntt_tomont(poly *p)
{
  intt_native(p);
  POLY_BOUND_MSG(p, INVNTT_BOUND_NATIVE, "native intt output");
}
#endif /* MLKEM_USE_NATIVE_INTT */
