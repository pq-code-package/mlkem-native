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
#include <string.h>
#include "cbmc.h"
#include "debug.h"
#include "poly.h"
#include "sampling.h"
#include "symmetric.h"
#include "verify.h"

#if !defined(MLK_USE_NATIVE_POLY_TOMONT) ||           \
    !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
    !defined(MLK_USE_NATIVE_NTT) || !defined(MLK_USE_NATIVE_INTT)
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
#endif /* !MLK_USE_NATIVE_POLY_TOMONT || !MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE \
          || !MLK_USE_NATIVE_NTT || !MLK_USE_NATIVE_INTT */

#if !defined(MLK_USE_NATIVE_POLY_REDUCE) || !defined(MLK_USE_NATIVE_INTT)
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
#endif /* !MLK_USE_NATIVE_POLY_REDUCE || !MLK_USE_NATIVE_INTT */

#if !defined(MLK_USE_NATIVE_POLY_TOMONT)
/* Reference: `poly_tomont()` in the reference implementation @[REF]. */
MLK_INTERNAL_API
void mlk_poly_tomont(mlk_poly *r)
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
#else  /* !MLK_USE_NATIVE_POLY_TOMONT */
MLK_INTERNAL_API
void mlk_poly_tomont(mlk_poly *r)
{
  mlk_poly_tomont_native(r->coeffs);
  mlk_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#endif /* MLK_USE_NATIVE_POLY_TOMONT */

#if !defined(MLK_USE_NATIVE_POLY_REDUCE)
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
MLK_INTERNAL_API
void mlk_poly_reduce(mlk_poly *r)
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
#else  /* !MLK_USE_NATIVE_POLY_REDUCE */
MLK_INTERNAL_API
void mlk_poly_reduce(mlk_poly *r)
{
  mlk_poly_reduce_native(r->coeffs);
  mlk_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#endif /* MLK_USE_NATIVE_POLY_REDUCE */

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

/* Include zeta table unless NTT, invNTT and mulcache computation
 * have been replaced by native implementations. */
#if !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
    !defined(MLK_USE_NATIVE_NTT) || !defined(MLK_USE_NATIVE_INTT)
#include "zetas.inc"
#endif

#if !defined(MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE)
/* Reference: Does not exist in the reference implementation @[REF].
 *            - The reference implementation does not use a
 *              multiplication cache ('mulcache'). This idea originates
 *              from @[NeonNTT] and is used at the C level here. */
MLK_INTERNAL_API
void mlk_poly_mulcache_compute(mlk_poly_mulcache *x, const mlk_poly *a)
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
#else  /* !MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE */
MLK_INTERNAL_API
void mlk_poly_mulcache_compute(mlk_poly_mulcache *x, const mlk_poly *a)
{
  mlk_poly_mulcache_compute_native(x->coeffs, a->coeffs);
}
#endif /* MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE */

#if !defined(MLK_USE_NATIVE_NTT)

/* Reference: Embedded in `ntt()` in the reference implementation. */
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

/*
 * Compute one layer of forward NTT
 * Parameters:
 * - r: Pointer to base of polynomial
 * - layer: Variable indicating which layer is being applied.
 */

/* Reference: Embedded in `ntt()` in the reference implementation [@REF]. */
static void mlk_ntt_1_layer(int16_t r[MLKEM_N], unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 7)
  requires(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, (layer + 1) * MLKEM_Q)))
{
  const unsigned len = MLKEM_N >> layer;
  unsigned start, k;
  /* Twiddle factors for layer n start at index 2 ** (layer-1) */
  k = 1 << (layer - 1);
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(start < MLKEM_N + 2 * len)
    invariant(k <= MLKEM_N / 2 && 2 * len * k == start + MLKEM_N)
    invariant(array_abs_bound(r, 0, start, layer * MLKEM_Q + MLKEM_Q))
    invariant(array_abs_bound(r, start, MLKEM_N, layer * MLKEM_Q))
  )
  {
    const int16_t zeta = zetas[k++];
    unsigned j;
    for (j = 0; j < len; j++)
    __loop__(
      invariant(j <= len)
      invariant(array_abs_bound(r,               0, start,           layer * MLKEM_Q + MLKEM_Q))
      invariant(array_abs_bound(r,           start, start + j,       layer * MLKEM_Q + MLKEM_Q))
      invariant(array_abs_bound(r,       start + j, start + len,     layer * MLKEM_Q))
      invariant(array_abs_bound(r,     start + len, start + len + j, layer * MLKEM_Q + MLKEM_Q))
      invariant(array_abs_bound(r, start + len + j, start + 2 * len, layer * MLKEM_Q))
      invariant(array_abs_bound(r, start + 2 * len, MLKEM_N,         layer * MLKEM_Q))
    )
    {
      mlk_ct_butterfly(r, start + j, start + len + j, zeta);
    }
  }
}

static void mlk_ntt_2_layers(int16_t r[MLKEM_N], unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 6)
  requires(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, (layer + 2) * MLKEM_Q)))
{
  const unsigned len = MLKEM_N >> layer;
  unsigned start, k;
  /* Twiddle factors for layer n start at index 2 ** (layer-1) */
  k = 1 << (layer - 1);
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(start < MLKEM_N + 2 * len)
    invariant(len % 2 == 0)
    invariant(len == 4 || len == 8 || len == 16 || len == 32 || len == 64 || len == 128)
    invariant(k <= MLKEM_N / 2 && 2 * len * k == start + MLKEM_N)
    invariant(array_abs_bound(r, 0, start, (layer + 2) * MLKEM_Q))
    invariant(array_abs_bound(r, start, MLKEM_N, layer * MLKEM_Q))
  )
  {
    unsigned j;
    const int16_t this_layer_zeta = zetas[k];
    const int16_t next_layer_zeta1 = zetas[k * 2];
    const int16_t next_layer_zeta2 = zetas[k * 2 + 1];
    k++;

    for (j = 0; j < len / 2; j++)
    __loop__(
      invariant(j <= len / 2)
      invariant(len % 2 == 0)
      invariant(len == 4 || len == 8 || len == 16 || len == 32 || len == 64 || len == 128)

      invariant(array_abs_bound(r, 0,                         start,                     layer * MLKEM_Q + MLKEM_Q))

      invariant(array_abs_bound(r, start,                     start + j,                 (layer + 2) * MLKEM_Q))
      invariant(array_abs_bound(r, start + j,                 start + len / 2,           layer * MLKEM_Q))

      invariant(array_abs_bound(r, start + len / 2,           start + len / 2 + j,       (layer + 2) * MLKEM_Q))
      invariant(array_abs_bound(r, start + len / 2 + j,       start + len,               layer * MLKEM_Q))

      invariant(array_abs_bound(r, start + len,               start + len + j,           (layer + 2) * MLKEM_Q))
      invariant(array_abs_bound(r, start + len + j,           start + len + len / 2,     layer * MLKEM_Q))

      invariant(array_abs_bound(r, start + len + len / 2,     start + len + len / 2 + j, (layer + 2) * MLKEM_Q))
      invariant(array_abs_bound(r, start + len + len / 2 + j, start + 2 * len,           layer * MLKEM_Q))

      invariant(array_abs_bound(r, start + 2 * len,           MLKEM_N,                   layer * MLKEM_Q))
    )
    {
      const unsigned ci0 = j + start;
      const unsigned ci1 = ci0 + len / 2;
      const unsigned ci2 = ci1 + len / 2;
      const unsigned ci3 = ci2 + len / 2;

      mlk_ct_butterfly(r, ci0, ci2, this_layer_zeta);
      mlk_ct_butterfly(r, ci1, ci3, this_layer_zeta);
      mlk_ct_butterfly(r, ci0, ci1, next_layer_zeta1);
      mlk_ct_butterfly(r, ci2, ci3, next_layer_zeta2);
    }
  }
}

static void mlk_ntt_3_layers(int16_t r[MLKEM_N], unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 5)
  requires(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, (layer + 3) * MLKEM_Q)))
{
  const unsigned len = MLKEM_N >> layer;
  unsigned start, k;
  /* Twiddle factors for layer n start at index 2 ** (layer-1) */
  k = 1 << (layer - 1);
  for (start = 0; start < MLKEM_N; start += 2 * len)
  {
    unsigned j;
    const int16_t first_layer_zeta = zetas[k];
    const unsigned second_layer_zi1 = k * 2;
    const unsigned second_layer_zi2 = k * 2 + 1;
    const int16_t second_layer_zeta1 = zetas[second_layer_zi1];
    const int16_t second_layer_zeta2 = zetas[second_layer_zi2];
    const int16_t third_layer_zeta1 = zetas[second_layer_zi1 * 2];
    const int16_t third_layer_zeta2 = zetas[second_layer_zi1 * 2 + 1];
    const int16_t third_layer_zeta3 = zetas[second_layer_zi2 * 2];
    const int16_t third_layer_zeta4 = zetas[second_layer_zi2 * 2 + 1];
    k++;

    for (j = 0; j < len / 4; j++)
    {
      const unsigned ci0 = j + start;
      const unsigned ci1 = ci0 + len / 4;
      const unsigned ci2 = ci1 + len / 4;
      const unsigned ci3 = ci2 + len / 4;
      const unsigned ci4 = ci3 + len / 4;
      const unsigned ci5 = ci4 + len / 4;
      const unsigned ci6 = ci5 + len / 4;
      const unsigned ci7 = ci6 + len / 4;

      mlk_ct_butterfly(r, ci0, ci4, first_layer_zeta);
      mlk_ct_butterfly(r, ci1, ci5, first_layer_zeta);
      mlk_ct_butterfly(r, ci2, ci6, first_layer_zeta);
      mlk_ct_butterfly(r, ci3, ci7, first_layer_zeta);

      mlk_ct_butterfly(r, ci0, ci2, second_layer_zeta1);
      mlk_ct_butterfly(r, ci1, ci3, second_layer_zeta1);
      mlk_ct_butterfly(r, ci4, ci6, second_layer_zeta2);
      mlk_ct_butterfly(r, ci5, ci7, second_layer_zeta2);

      mlk_ct_butterfly(r, ci0, ci1, third_layer_zeta1);
      mlk_ct_butterfly(r, ci2, ci3, third_layer_zeta2);
      mlk_ct_butterfly(r, ci4, ci5, third_layer_zeta3);
      mlk_ct_butterfly(r, ci6, ci7, third_layer_zeta4);
    }
  }
}

/*
 * Compute full forward NTT
 * NOTE: This particular implementation satisfies a much tighter
 * bound on the output coefficients (5*q) than the contractual one (8*q),
 * but this is not needed in the calling code. Should we change the
 * base multiplication strategy to require smaller NTT output bounds,
 * the proof may need strengthening.
 */

/* Reference: `ntt()` in the reference implementation @[REF].
 * - Iterate over `layer` instead of `len` in the outer loop
 *   to simplify computation of zeta index. */
MLK_INTERNAL_API
void mlk_poly_ntt(mlk_poly *p)
{
  int16_t *r;
  mlk_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  r = p->coeffs;

  mlk_ntt_3_layers(r, 1);
  mlk_ntt_2_layers(r, 4);
  mlk_ntt_1_layer(r, 6);
  mlk_ntt_1_layer(r, 7);

  /* Check the stronger bound */
  mlk_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}
#else  /* !MLK_USE_NATIVE_NTT */

MLK_INTERNAL_API
void mlk_poly_ntt(mlk_poly *p)
{
  mlk_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  mlk_ntt_native(p->coeffs);
  mlk_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}
#endif /* MLK_USE_NATIVE_NTT */

#if !defined(MLK_USE_NATIVE_INTT)

/* Compute one layer of inverse NTT */

/* Reference: Embedded into `invntt()` in the reference implementation @[REF] */
static void mlk_invntt_layer(int16_t *r, unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 7)
  requires(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
{
  unsigned start, k, len;
  len = (MLKEM_N >> layer);
  k = (1u << layer) - 1;
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
    invariant(start <= MLKEM_N && k <= 127)
    /* Normalised form of k == MLKEM_N / len - 1 - start / (2 * len) */
    invariant(2 * len * k + start == 2 * MLKEM_N - 2 * len))
  {
    unsigned j;
    int16_t zeta = mlk_zetas[k--];
    for (j = start; j < start + len; j++)
    __loop__(
      invariant(start <= j && j <= start + len)
      invariant(start <= MLKEM_N && k <= 127)
      invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
    {
      int16_t t = r[j];
      r[j] = mlk_barrett_reduce(t + r[j + len]);
      r[j + len] = r[j + len] - t;
      r[j + len] = mlk_fqmul(r[j + len], zeta);
    }
  }
}

/* Reference: `invntt()` in the reference implementation @[REF]
 *            - We normalize at the beginning of the inverse NTT,
 *              while the reference implementation normalizes at
 *              the end. This allows us to drop a call to `poly_reduce()`
 *              from the base multiplication. */
MLK_INTERNAL_API
void mlk_poly_invntt_tomont(mlk_poly *p)
{
  /*
   * Scale input polynomial to account for Montgomery factor
   * and NTT twist. This also brings coefficients down to
   * absolute value < MLKEM_Q.
   */
  unsigned j, layer;
  const int16_t f = 1441; /* check-magic: 1441 == pow(2,32 - 7,MLKEM_Q) */
  int16_t *r = p->coeffs;

  for (j = 0; j < MLKEM_N; j++)
  __loop__(
    invariant(j <= MLKEM_N)
    invariant(array_abs_bound(r, 0, j, MLKEM_Q)))
  {
    r[j] = mlk_fqmul(r[j], f);
  }

  /* Run the invNTT layers */
  for (layer = 7; layer > 0; layer--)
  __loop__(
    invariant(0 <= layer && layer < 8)
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
  {
    mlk_invntt_layer(r, layer);
  }

  mlk_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}
#else  /* !MLK_USE_NATIVE_INTT */

MLK_INTERNAL_API
void mlk_poly_invntt_tomont(mlk_poly *p)
{
  mlk_intt_native(p->coeffs);
  mlk_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}
#endif /* MLK_USE_NATIVE_INTT */

#else /* !MLK_CONFIG_MULTILEVEL_NO_SHARED */

MLK_EMPTY_CU(mlk_poly)

#endif /* MLK_CONFIG_MULTILEVEL_NO_SHARED */
