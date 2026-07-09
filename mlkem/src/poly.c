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


#include "cbmc.h"
#include "debug.h"
#include "poly.h"
#include "sampling.h"
#include "symmetric.h"
#include "verify.h"

/**
 * Montgomery multiplication modulo MLKEM_Q with precomputed twist.
 *
 * @reference{`fqmul()` in the reference implementation @[REF].}
 *
 * @param a         First factor. Can be any int16_t.
 * @param b         Second factor. Must be signed canonical
 *                  (abs value < (MLKEM_Q+1)/2).
 * @param b_twisted Precomputed `b * MLKEM_Q^{-1} mod 2^16` (signed canonical).
 *
 * @return 16-bit integer congruent to a*b*R^{-1} mod MLKEM_Q, and
 *         smaller than MLKEM_Q in absolute value.
 */
static MLK_INLINE int16_t mlk_fqmul(int16_t a, int16_t b, int16_t b_twisted)
__contract__(
  requires(b > -MLKEM_Q_HALF && b < MLKEM_Q_HALF)
  ensures(return_value > -MLKEM_Q && return_value < MLKEM_Q)
)
{
  uint16_t lo0;
  int16_t res, hi, lo, correction;
  mlk_assert_abs_bound(&b, 1, MLKEM_Q_HALF);

  /* High 16 bits of the signed product a * b. */
  hi = (int16_t)(((int32_t)a * b) >> 16);
  /* Low 16 bits of a * b_twisted (== a * b * MLKEM_Q^{-1} mod 2^16).
   * This is just a 16x16->16 bit low multiplication, but we express
   * it as a 16x16->32 widening multiplication with an explicit truncation
   * to avoid unsigned overflow errors from CBMC. The compiler will be smart
   * enough to realize to optimize this away. */
  lo0 = (uint16_t)(((uint32_t)mlk_cast_int16_to_uint16(a) *
                    mlk_cast_int16_to_uint16(b_twisted)) &
                   UINT16_MAX);
  /* Lift low product to signed (!) 16-bit integer */
  lo = mlk_cast_uint16_to_int16(lo0);

  /* 16x16->16 bit high multiplication
   *
   * PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
   * implementation-defined for negative left argument. Here,
   * we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
   *
   * Bounds: |correction| <= ceil(2^15 * MLKEM_Q / 2^16) = (MLKEM_Q + 1)/2
   *
   * Safety: The bounds argument above demonstrates that the truncation is safe.
   */
  correction = (int16_t)(((int32_t)lo * MLKEM_Q) >> 16);

  /* Bounds:
   * |res| <= |hi| + |correction|
   *       <= ceil(|a| * |b| / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil(2^15 * ((MLKEM_Q - 1)/2) / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil((MLKEM_Q - 1) / 4) + (MLKEM_Q + 1) / 2
   *        < MLKEM_Q
   */
  res = (int16_t)(hi - correction);

  mlk_assert_abs_bound(&res, 1, MLKEM_Q);
  return res;
}

/**
 * Barrett reduction; given a 16-bit integer a, computes the centered
 * representative congruent to a mod MLKEM_Q in [-(MLKEM_Q-1)/2, (MLKEM_Q-1)/2].
 *
 * @reference{`barrett_reduce()` in the reference implementation @[REF].}
 *
 * @param a Input integer to be reduced.
 *
 * @return Integer in [-(MLKEM_Q-1)/2, (MLKEM_Q-1)/2] congruent to @p a modulo
 *         MLKEM_Q.
 */
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
  const int32_t t = (magic * a + ((int32_t)1 << 25)) >> 26;

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
  /* check-magic:
       20553 == signed_mod(1353 * pow(MLKEM_Q, -1, 2^16), 2^16) */
  const int16_t f_twisted = 20553;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_abs_bound(r->coeffs, 0, i, MLKEM_Q))
    decreases(MLKEM_N - i))
  {
    r->coeffs[i] = mlk_fqmul(r->coeffs[i], f, f_twisted);
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

/**
 * Constant-time conversion of signed representatives modulo MLKEM_Q within
 * range [-(MLKEM_Q-1), MLKEM_Q-1] into unsigned representatives within
 * range [0, MLKEM_Q-1].
 *
 * @reference{Not present in the reference implementation @[REF]. Used here
 * to implement different semantics of `poly_reduce()`; see below. In the
 * reference implementation @[REF] this logic is part of all compression
 * functions (see `compress.c`).}
 *
 * @param c Signed coefficient to be converted.
 *
 * @return Unsigned representative in [0, MLKEM_Q).
 */
static MLK_INLINE int16_t mlk_scalar_signed_to_unsigned_q(int16_t c)
__contract__(
  requires(c > -MLKEM_Q && c < MLKEM_Q)
  ensures(return_value >= 0 && return_value < MLKEM_Q)
  ensures(return_value == (int32_t)c + (((int32_t)c < 0) * MLKEM_Q)))
{
  mlk_assert_abs_bound(&c, 1, MLKEM_Q);

  /* Add MLKEM_Q if c is negative, but in constant time.
   *
   * Note that c + MLKEM_Q does not overflow in int16_t,
   * so the cast to uint16_t is safe. */
  c = mlk_ct_sel_int16((int16_t)(c + MLKEM_Q), c, mlk_ct_cmask_neg_i16(c));

  mlk_assert_bound(&c, 1, 0, MLKEM_Q);
  return c;
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
    invariant(array_bound(r->coeffs, 0, i, 0, MLKEM_Q))
    decreases(MLKEM_N - i))
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
    invariant(forall(k1, 0, i, r->coeffs[k1] == loop_entry(*r).coeffs[k1] + b->coeffs[k1]))
    decreases(MLKEM_N - i))
  {
    /* The preconditions imply that the addition stays within int16_t. */
    r->coeffs[i] = (int16_t)(r->coeffs[i] + b->coeffs[i]);
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
    invariant(forall(k1, 0, i, r->coeffs[k1] == loop_entry(*r).coeffs[k1] - b->coeffs[k1]))
    decreases(MLKEM_N - i))
  {
    /* The preconditions imply that the subtraction stays within int16_t. */
    r->coeffs[i] = (int16_t)(r->coeffs[i] - b->coeffs[i]);
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
  assigns(memory_slice(x, sizeof(mlk_poly_mulcache)))
)
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 4; i++)
  __loop__(
    invariant(i <= MLKEM_N / 4)
    invariant(array_abs_bound(x->coeffs, 0, 2 * i, MLKEM_Q))
    decreases(MLKEM_N / 4 - i))
  {
    const int16_t z = mlk_zetas[64 + i][0];
    const int16_t z_t = mlk_zetas[64 + i][1];
    x->coeffs[2 * i + 0] = mlk_fqmul(a->coeffs[4 * i + 1], z, z_t);
    /* The values in zeta table are <= MLKEM_Q in absolute value,
     * so the negation in int16_t is safe. */
    x->coeffs[2 * i + 1] =
        mlk_fqmul(a->coeffs[4 * i + 3], (int16_t)(-z), (int16_t)(-z_t));
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

/* Cooley-Tukey butterfly */
static MLK_INLINE void mlk_ct_butterfly(int16_t r[MLKEM_N], unsigned i,
                                        unsigned j, int16_t z, int16_t zt)
{
  const int16_t t = mlk_fqmul(r[j], z, zt);
  r[j] = (int16_t)(r[i] - t);
  r[i] = (int16_t)(r[i] + t);
}

/* Gentleman-Sande butterfly without reduction.
 *
 * The twiddles `z`, `zt` are implicitly negated: we compute `b - a` instead
 * of `a - b`, which is equivalent to multiplying by `-z`.
 */
static MLK_INLINE void mlk_gs_butterfly(int16_t r[MLKEM_N], unsigned i,
                                        unsigned j, int16_t z, int16_t zt)
{
  const int16_t a = r[i];
  const int16_t b = r[j];
  r[i] = (int16_t)(a + b);
  r[j] = mlk_fqmul((int16_t)(b - a), z, zt);
}

/*
 * Two merged forward-NTT layers, applied to one outer block.
 */
static MLK_INLINE void mlk_ntt_2_layers_block(
    int16_t r[MLKEM_N], unsigned start, unsigned len, int16_t z0, int16_t z0t,
    int16_t z1, int16_t z1t, int16_t z2, int16_t z2t, const int16_t bound)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(0 < bound && bound < INT16_MAX - 2 * MLKEM_Q)
  requires(1 <= len && len <= MLKEM_N / 4)
  requires(start <= MLKEM_N - 4 * len)
  requires(z0 > -MLKEM_Q_HALF && z0 < MLKEM_Q_HALF)
  requires(z1 > -MLKEM_Q_HALF && z1 < MLKEM_Q_HALF)
  requires(z2 > -MLKEM_Q_HALF && z2 < MLKEM_Q_HALF)
  requires(array_abs_bound(r, start, MLKEM_N, bound))
  requires(array_abs_bound(r, 0, start, bound + 2 * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, start + 4 * len, MLKEM_N, bound))
  ensures(array_abs_bound(r, 0, start + 4 * len, bound + 2 * MLKEM_Q))
)
{
  unsigned j = 0;
  /* `bound` is a ghost variable referenced only in the CBMC contract. */
  ((void)bound);
  for (j = 0; j < len; j++)
  __loop__(
    assigns(j, memory_slice(r, sizeof(int16_t) * MLKEM_N))
    invariant(j <= len)
    /* Static bounds */
    invariant(array_abs_bound(r, 0, start, bound + 2 * MLKEM_Q))
    invariant(array_abs_bound(r, start + 4 * len, MLKEM_N, bound))
    /* Dynamic bounds */
    invariant(array_abs_bound(r, start + 0 * len,     start + 0 * len + j, bound + 2 * MLKEM_Q))
    invariant(array_abs_bound(r, start + 1 * len,     start + 1 * len + j, bound + 2 * MLKEM_Q))
    invariant(array_abs_bound(r, start + 2 * len,     start + 2 * len + j, bound + 2 * MLKEM_Q))
    invariant(array_abs_bound(r, start + 3 * len,     start + 3 * len + j, bound + 2 * MLKEM_Q))
    invariant(array_abs_bound(r, start + 0 * len + j, start + 1 * len,     bound))
    invariant(array_abs_bound(r, start + 1 * len + j, start + 2 * len,     bound))
    invariant(array_abs_bound(r, start + 2 * len + j, start + 3 * len,     bound))
    invariant(array_abs_bound(r, start + 3 * len + j, start + 4 * len,     bound))
    decreases(len - j))
  {
    const unsigned i0 = start + j;
    const unsigned i1 = i0 + 1 * len;
    const unsigned i2 = i0 + 2 * len;
    const unsigned i3 = i0 + 3 * len;

    mlk_ct_butterfly(r, i0, i2, z0, z0t);
    mlk_ct_butterfly(r, i1, i3, z0, z0t);
    mlk_ct_butterfly(r, i0, i1, z1, z1t);
    mlk_ct_butterfly(r, i2, i3, z2, z2t);
  }
}

/*
 * Two merged forward-NTT layers.
 */
static MLK_INLINE void mlk_ntt_2_layers(int16_t r[MLKEM_N],
                                        const unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(layer == 1 || layer == 3 || layer == 5)
  requires(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, (layer + 2) * MLKEM_Q)))
{
  const unsigned len_outer = (unsigned)MLKEM_N >> layer;
  const unsigned len = len_outer >> 1;
  unsigned start, k;
  k = 1u << (layer - 1);
  for (start = 0; start < MLKEM_N; start += 2 * len_outer)
  __loop__(
    invariant(start <= MLKEM_N)
    invariant((1u << (layer - 1)) <= k && k <= (1u << layer))
    invariant(2 * len_outer * k == start + MLKEM_N)
    invariant(array_abs_bound(r, 0, start, (layer + 2) * MLKEM_Q))
    invariant(array_abs_bound(r, start, MLKEM_N, layer * MLKEM_Q))
    decreases(MLKEM_N - start))
  {
    /* Negation of the zetas is embedded in
     * mlk_ntt_2_layers_blocks -> mlk_gs_butterfly */
    const int16_t z0 = mlk_zetas[k][0];
    const int16_t z1 = mlk_zetas[2 * k][0];
    const int16_t z2 = mlk_zetas[2 * k + 1][0];

    const int16_t z0t = mlk_zetas[k][1];
    const int16_t z1t = mlk_zetas[2 * k][1];
    const int16_t z2t = mlk_zetas[2 * k + 1][1];

    k++;
    mlk_ntt_2_layers_block(r, start, len, z0, z0t, z1, z1t, z2, z2t,
                           (int16_t)(layer * MLKEM_Q));
  }
}

/*
 * Single-layer forward NTT, used for the leftover layer 7 (len=2) after the
 * three merged 2-layer calls.
 */

/* Reference: Embedded in `ntt()` in the reference implementation @[REF]. */
static void mlk_ntt_butterfly_block(int16_t r[MLKEM_N], int16_t zeta,
                                    int16_t zeta_t, unsigned start,
                                    unsigned len, unsigned bound)
__contract__(
  requires(start < MLKEM_N)
  requires(1 <= len && len <= MLKEM_N / 2 && start + 2 * len <= MLKEM_N)
  requires(0 <= bound && bound < INT16_MAX - MLKEM_Q)
  requires(-MLKEM_Q_HALF < zeta && zeta < MLKEM_Q_HALF)
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(r, 0, start, bound + MLKEM_Q))
  requires(array_abs_bound(r, start, MLKEM_N, bound))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, start + 2*len, bound + MLKEM_Q))
  ensures(array_abs_bound(r, start + 2 * len, MLKEM_N, bound)))
{
  /* `bound` is a ghost variable only needed in the CBMC specification */
  unsigned j;
  ((void)bound);
  for (j = start; j < start + len; j++)
  __loop__(
    invariant(start <= j && j <= start + len)
    /*
     * Coefficients are updated in strided pairs, so the bounds for the
     * intermediate states alternate twice between the old and new bound
     */
    invariant(array_abs_bound(r, 0,           j,           bound + MLKEM_Q))
    invariant(array_abs_bound(r, j,           start + len, bound))
    invariant(array_abs_bound(r, start + len, j + len,     bound + MLKEM_Q))
    invariant(array_abs_bound(r, j + len,     MLKEM_N,     bound))
    decreases(start + len - j))
  {
    int16_t t;
    t = mlk_fqmul(r[j + len], zeta, zeta_t);
    /* The precondition implies that the arithmetic does not overflow. */
    r[j + len] = (int16_t)(r[j] - t);
    r[j] = (int16_t)(r[j] + t);
  }
}

/* Reference: Embedded in `ntt()` in the reference implementation @[REF]. */
static void mlk_ntt_layer(int16_t r[MLKEM_N], unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 7)
  requires(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, (layer + 1) * MLKEM_Q)))
{
  unsigned start, k, len;
  /* Twiddle factors for layer n are at indices 2^(n-1)..2^n-1. */
  k = 1u << (layer - 1);
  len = (unsigned)MLKEM_N >> layer;
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(start < MLKEM_N + 2 * len)
    invariant(k <= MLKEM_N / 2 && 2 * len * k == start + MLKEM_N)
    invariant(array_abs_bound(r, 0, start, layer * MLKEM_Q + MLKEM_Q))
    invariant(array_abs_bound(r, start, MLKEM_N, layer * MLKEM_Q))
    decreases(MLKEM_N - start))
  {
    const int16_t zeta = mlk_zetas[k][0];
    const int16_t zeta_t = mlk_zetas[k][1];
    k++;
    mlk_ntt_butterfly_block(r, zeta, zeta_t, start, len, layer * MLKEM_Q);
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

  mlk_ntt_2_layers(r, 1);
  mlk_ntt_2_layers(r, 3);
  mlk_ntt_2_layers(r, 5);
  /* Layer 7 is left as a single layer because the 2-layer merge only covers
   * an even number of layers (ML-KEM has 7). */
  mlk_ntt_layer(r, 7);

  /* Check the stronger bound */
  mlk_assert_abs_bound(p, MLKEM_N, MLK_NTT_BOUND);
}

MLK_INTERNAL_API
void mlk_poly_ntt(mlk_poly *r)
{
#if defined(MLK_USE_NATIVE_NTT)
  int ret;
  mlk_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
  ret = mlk_ntt_native(r->coeffs);
  if (ret == MLK_NATIVE_FUNC_SUCCESS)
  {
    mlk_assert_abs_bound(r, MLKEM_N, MLK_NTT_BOUND);
    return;
  }
#endif /* MLK_USE_NATIVE_NTT */

  mlk_poly_ntt_c(r);
}


/*
 * Two merged inverse-NTT layers, applied to one outer block.
 *
 * Bound discipline (int16_t): on entry every coefficient is <MLKEM_Q. After
 * the first pair of GS butterflies the additive outputs are <2*MLKEM_Q; the
 * second pair leaves the multiplicative outputs <MLKEM_Q via fqmul, and we
 * Barrett-reduce the additive outputs explicitly so all four coefficients are
 * again <MLKEM_Q.
 */
static MLK_INLINE void mlk_invntt_2_layers_block(int16_t r[MLKEM_N],
                                                 unsigned start, unsigned len,
                                                 int16_t z0, int16_t z0t,
                                                 int16_t z1, int16_t z1t,
                                                 int16_t z2, int16_t z2t)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= len && len <= MLKEM_N / 4)
  requires(start <= MLKEM_N - 4 * len)
  requires(z0 > -MLKEM_Q_HALF && z0 < MLKEM_Q_HALF)
  requires(z1 > -MLKEM_Q_HALF && z1 < MLKEM_Q_HALF)
  requires(z2 > -MLKEM_Q_HALF && z2 < MLKEM_Q_HALF)
  requires(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
)
{
  unsigned j = 0;
  for (j = 0; j < len; j++)
  __loop__(
    assigns(j, memory_slice(r, sizeof(int16_t) * MLKEM_N))
    invariant(j <= len)
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
    decreases(len - j))
  {
    const unsigned i0 = start + j;
    const unsigned i1 = i0 + 1 * len;
    const unsigned i2 = i0 + 2 * len;
    const unsigned i3 = i0 + 3 * len;
    /* Bounds: MLKEM_Q */
    mlk_gs_butterfly(r, i0, i1, z1, z1t);
    mlk_gs_butterfly(r, i2, i3, z2, z2t);
    /* Bounds: 2 * MLKEM_Q */
    mlk_gs_butterfly(r, i0, i2, z0, z0t);
    mlk_gs_butterfly(r, i1, i3, z0, z0t);
    /* Barrett-reduce the additive outputs back to <MLKEM_Q. */
    r[i0] = mlk_barrett_reduce(r[i0]);
    r[i1] = mlk_barrett_reduce(r[i1]);
  }
}

/*
 * Two merged inverse-NTT layers.
 */
static MLK_INLINE void mlk_invntt_2_layers(int16_t r[MLKEM_N],
                                           const unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(layer == 2 || layer == 4 || layer == 6)
  requires(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
{
  const unsigned len = (unsigned)MLKEM_N >> layer;
  const unsigned len_outer = len << 1;
  unsigned start, k;
  k = (1u << (layer - 1)) - 1u;
  for (start = 0; start < MLKEM_N; start += 2 * len_outer)
  __loop__(
    invariant(start <= MLKEM_N)
    invariant(k < (1u << (layer - 1)))
    invariant(2 * len_outer * k + 2 * len_outer == 2 * MLKEM_N - start)
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
    decreases(MLKEM_N - start))
  {
    /* Zetas are passed un-negated; mlk_gs_butterfly absorbs the negation. */
    const int16_t z0 = mlk_zetas[k][0];
    const int16_t z1 = mlk_zetas[2 * k + 1][0];
    const int16_t z2 = mlk_zetas[2 * k][0];

    const int16_t z0t = mlk_zetas[k][1];
    const int16_t z1t = mlk_zetas[2 * k + 1][1];
    const int16_t z2t = mlk_zetas[2 * k][1];

    k--;
    mlk_invntt_2_layers_block(r, start, len, z0, z0t, z1, z1t, z2, z2t);
  }
}

/* Single-layer inverse NTT, used for the leftover layer 7 (len=1) before
 * the three merged 2-layer calls. */

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
  len = (unsigned)MLKEM_N >> layer;
  k = (1u << layer) - 1;
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
    invariant(start <= MLKEM_N && k <= 127)
    /* Normalised form of k == MLKEM_N / len - 1 - start / (2 * len) */
    invariant(2 * len * k + start == 2 * MLKEM_N - 2 * len)
    decreases(MLKEM_N - start))
  {
    unsigned j;
    const int16_t zeta = mlk_zetas[k][0];
    const int16_t zeta_t = mlk_zetas[k][1];
    k--;
    for (j = start; j < start + len; j++)
    __loop__(
      invariant(start <= j && j <= start + len)
      invariant(start <= MLKEM_N && k <= 127)
      invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
      decreases(start + len - j))
    {
      int16_t t = r[j];
      /* The preconditions imply that the arithmetic does not overflow. */
      r[j] = mlk_barrett_reduce((int16_t)(t + r[j + len]));
      r[j + len] = (int16_t)(r[j + len] - t);
      r[j + len] = mlk_fqmul(r[j + len], zeta, zeta_t);
    }
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
  unsigned j;
  const int16_t f = 1441; /* check-magic: 1441 == pow(2,32 - 7,MLKEM_Q) */
  /* check-magic:
       -10079 == signed_mod(1441 * pow(MLKEM_Q, -1, 2^16), 2^16) */
  const int16_t f_twisted = -10079;
  int16_t *r = p->coeffs;

  /*
   * Scale input polynomial to account for Montgomery factor
   * and NTT twist. This also brings coefficients down to
   * absolute value < MLKEM_Q.
   */
  for (j = 0; j < MLKEM_N; j++)
  __loop__(
    invariant(j <= MLKEM_N)
    invariant(array_abs_bound(r, 0, j, MLKEM_Q))
    decreases(MLKEM_N - j))
  {
    r[j] = mlk_fqmul(r[j], f, f_twisted);
  }

  /* Layer 7 is left as a single layer because the 2-layer merge only covers
   * an even number of layers (ML-KEM has 7). */
  mlk_invntt_layer(r, 7);
  mlk_invntt_2_layers(r, 6);
  mlk_invntt_2_layers(r, 4);
  mlk_invntt_2_layers(r, 2);

  mlk_assert_abs_bound(p, MLKEM_N, MLK_INVNTT_BOUND);
}

MLK_INTERNAL_API
void mlk_poly_invntt_tomont(mlk_poly *r)
{
#if defined(MLK_USE_NATIVE_INTT)
  int ret;
  ret = mlk_intt_native(r->coeffs);
  if (ret == MLK_NATIVE_FUNC_SUCCESS)
  {
    mlk_assert_abs_bound(r, MLKEM_N, MLK_INVNTT_BOUND);
    return;
  }
#endif /* MLK_USE_NATIVE_INTT */

  mlk_poly_invntt_tomont_c(r);
}

#else /* !MLK_CONFIG_MULTILEVEL_NO_SHARED */

MLK_EMPTY_CU(mlk_poly)

#endif /* MLK_CONFIG_MULTILEVEL_NO_SHARED */
