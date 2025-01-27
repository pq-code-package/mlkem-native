/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "common.h"
#if !defined(MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED)

#include <stdint.h>
#include <string.h>
#include "arith_backend.h"
#include "cbmc.h"
#include "debug.h"
#include "fips202/fips202x4.h"
#include "poly.h"
#include "symmetric.h"
#include "verify.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define cast_uint16_to_int16 MLKEM_NAMESPACE(cast_uint16_to_int16)
#define montgomery_reduce_generic MLKEM_NAMESPACE(montgomery_reduce_generic)
#define montgomery_reduce MLKEM_NAMESPACE(montgomery_reduce)
#define fqmul MLKEM_NAMESPACE(fqmul)
#define barrett_reduce MLKEM_NAMESPACE(barrett_reduce)
#define basemul_cached MLKEM_NAMESPACE(basemul_cached)
#define scalar_signed_to_unsigned_q MLKEM_NAMESPACE(scalar_signed_to_unsigned_q)
#define ntt_butterfly_block MLKEM_NAMESPACE(ntt_butterfly_block)
#define ntt_layer MLKEM_NAMESPACE(ntt_layer)
#define invntt_layer MLKEM_NAMESPACE(invntt_layer)
#define rej_uniform MLKEM_NAMESPACE(rej_uniform)
#define rej_uniform_scalar MLKEM_NAMESPACE(rej_uniform_scalar)
#define load32_littleendian MLKEM_NAMESPACE(load32_littleendian)
#define load24_littleendian MLKEM_NAMESPACE(load24_littleendian)
/* End of static namespacing */

/*************************************************
 * Name:        cast_uint16_to_int16
 *
 * Description: Cast uint16 value to int16
 *
 * Returns:
 *   input x in     0 .. 32767: returns value unchanged
 *   input x in 32768 .. 65535: returns (x - 65536)
 **************************************************/
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"
#endif
ALWAYS_INLINE
static INLINE int16_t cast_uint16_to_int16(uint16_t x)
{
  /*
   * PORTABILITY: This relies on uint16_t -> int16_t
   * being implemented as the inverse of int16_t -> uint16_t,
   * which is implementation-defined (C99 6.3.1.3 (3))
   * CBMC (correctly) fails to prove this conversion is OK,
   * so we have to suppress that check here
   */
  return (int16_t)x;
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/*************************************************
 * Name:        montgomery_reduce_generic
 *
 * Description: Generic Montgomery reduction; given a 32-bit integer a, computes
 *              16-bit integer congruent to a * R^-1 mod q, where R=2^16
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *
 * Returns:     integer congruent to a * R^-1 modulo q, with absolute value
 *                <= ceil(|a| / 2^16) + (MLKEM_Q + 1)/2
 *
 **************************************************/
ALWAYS_INLINE
static INLINE int16_t montgomery_reduce_generic(int32_t a)
{
  /* QINV == -3327 converted to uint16_t == -3327 + 65536 == 62209 */
  const uint32_t QINV = 62209; /* q^-1 mod 2^16 */

  /*  Compute a*q^{-1} mod 2^16 in unsigned representatives */
  const uint16_t a_reduced = a & UINT16_MAX;
  const uint16_t a_inverted = (a_reduced * QINV) & UINT16_MAX;

  /* Lift to signed canonical representative mod 2^16. */
  const int16_t t = cast_uint16_to_int16(a_inverted);

  int32_t r = a - ((int32_t)t * MLKEM_Q);
  /* Bounds: |r| <= |a| + 2^15 * MLKEM_Q */

  /*
   * PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
   * implementation-defined for negative left argument. Here,
   * we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
   */
  r = r >> 16;
  /* Bounds: |r >> 16| <= ceil(|r| / 2^16)
   *                   <= ceil(|a| / 2^16 + MLKEM_Q / 2)
   *                   <= ceil(|a| / 2^16) + (MLKEM_Q + 1) / 2
   *
   * (Note that |a >> n| = ceil(|a| / 2^16) for negative a)
   */

  return (int16_t)r;
}

/*************************************************
 * Name:        montgomery_reduce
 *
 * Description: Montgomery reduction
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *                  Must be smaller than 2 * 2^12 * 2^15 in absolute value.
 *
 * Returns:     integer congruent to a * R^-1 modulo q,
 *              smaller than 2 * q in absolute value.
 **************************************************/
static INLINE int16_t montgomery_reduce(int32_t a)
__contract__(
  requires(a > -(2 * UINT12_LIMIT * 32768))
  requires(a <  (2 * UINT12_LIMIT * 32768))
  ensures(return_value > -2 * MLKEM_Q && return_value < 2 * MLKEM_Q)
)
{
  int16_t res;
  debug_assert_abs_bound(&a, 1, 2 * UINT12_LIMIT * 32768);

  res = montgomery_reduce_generic(a);
  /* Bounds:
   * |res| <= ceil(|a| / 2^16) + (MLKEM_Q + 1) / 2
   *       <= ceil(2 * UINT12_LIMIT * 32768 / 65536) + (MLKEM_Q + 1) / 2
   *       <= UINT12_LIMIT + (MLKEM_Q + 1) / 2
   *        < 2 * MLKEM_Q */

  debug_assert_abs_bound(&res, 1, 2 * MLKEM_Q);
  return res;
}

#if !defined(MLKEM_USE_NATIVE_POLY_TOMONT) ||           \
    !defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
    !defined(MLKEM_USE_NATIVE_NTT) || !defined(MLKEM_USE_NATIVE_INTT)
/*************************************************
 * Name:        fqmul
 *
 * Description: Montgomery multiplication modulo q=3329
 *
 * Arguments:   - int16_t a: first factor
 *                  Can be any int16_t.
 *              - int16_t b: second factor.
 *                  Must be signed canonical (abs value <(q+1)/2)
 *
 * Returns 16-bit integer congruent to a*b*R^{-1} mod q, and
 * smaller than q in absolute value.
 *
 **************************************************/
static INLINE int16_t fqmul(int16_t a, int16_t b)
__contract__(
  requires(b > -HALF_Q)
  requires(b < HALF_Q)
  ensures(return_value > -MLKEM_Q && return_value < MLKEM_Q)
)
{
  int16_t res;
  debug_assert_abs_bound(&b, 1, HALF_Q);

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
#endif /* !defined(MLKEM_USE_NATIVE_POLY_TOMONT) ||           \
          !defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE) || \
          !defined(MLKEM_USE_NATIVE_NTT) ||                   \
          !defined(MLKEM_USE_NATIVE_INTT) */

#if !defined(MLKEM_USE_NATIVE_POLY_REDUCE) || !defined(MLKEM_USE_NATIVE_INTT)
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
static INLINE int16_t barrett_reduce(int16_t a)
__contract__(
  ensures(return_value > -HALF_Q && return_value < HALF_Q)
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

  debug_assert_abs_bound(&res, 1, HALF_Q);
  return res;
}
#endif /* !defined(MLKEM_USE_NATIVE_POLY_REDUCE) || \
          !defined(MLKEM_USE_NATIVE_INTT) */

static void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                           int16_t b_cached)
__contract__(
  requires(memory_no_alias(r, 2 * sizeof(int16_t)))
  requires(memory_no_alias(a, 2 * sizeof(int16_t)))
  requires(memory_no_alias(b, 2 * sizeof(int16_t)))
  requires(array_bound(a, 0, 2, 0, UINT12_LIMIT))
  assigns(memory_slice(r, 2 * sizeof(int16_t)))
  ensures(array_abs_bound(r, 0, 2, 2 * MLKEM_Q)))
{
  int32_t t0, t1;
  debug_assert_bound(a, 2, 0, UINT12_LIMIT);

  t0 = (int32_t)a[1] * b_cached;
  t0 += (int32_t)a[0] * b[0];
  t1 = (int32_t)a[0] * b[1];
  t1 += (int32_t)a[1] * b[0];

  /* |ti| < 2 * q * 2^15 */
  r[0] = montgomery_reduce(t0);
  r[1] = montgomery_reduce(t1);

  debug_assert_abs_bound(r, 2, 2 * MLKEM_Q);
}

MLKEM_NATIVE_INTERNAL_API
void poly_basemul_montgomery_cached(poly *r, const poly *a, const poly *b,
                                    const poly_mulcache *b_cache)
{
  unsigned i;
  debug_assert_bound(a, MLKEM_N, 0, UINT12_LIMIT);

  for (i = 0; i < MLKEM_N / 4; i++)
  __loop__(
    assigns(i, object_whole(r))
    invariant(i <= MLKEM_N / 4)
    invariant(array_abs_bound(r->coeffs, 0, 4 * i, 2 * MLKEM_Q)))
  {
    basemul_cached(&r->coeffs[4 * i], &a->coeffs[4 * i], &b->coeffs[4 * i],
                   b_cache->coeffs[2 * i]);
    basemul_cached(&r->coeffs[4 * i + 2], &a->coeffs[4 * i + 2],
                   &b->coeffs[4 * i + 2], b_cache->coeffs[2 * i + 1]);
  }

  debug_assert_abs_bound(r, MLKEM_N, 2 * MLKEM_Q);
}

#if !defined(MLKEM_USE_NATIVE_POLY_TOMONT)
MLKEM_NATIVE_INTERNAL_API
void poly_tomont(poly *r)
{
  unsigned i;
  const int16_t f = (1ULL << 32) % MLKEM_Q; /* 1353 */
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(array_abs_bound(r->coeffs, 0, i, MLKEM_Q)))
  {
    r->coeffs[i] = fqmul(r->coeffs[i], f);
  }

  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#else  /* MLKEM_USE_NATIVE_POLY_TOMONT */
MLKEM_NATIVE_INTERNAL_API
void poly_tomont(poly *r)
{
  poly_tomont_native(r->coeffs);
  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#endif /* MLKEM_USE_NATIVE_POLY_TOMONT */

#if !defined(MLKEM_USE_NATIVE_POLY_REDUCE)
/************************************************************
 * Name: scalar_signed_to_unsigned_q
 *
 * Description: converts signed polynomial coefficient
 *              from signed (-3328 .. 3328) form to
 *              unsigned form (0 .. 3328).
 *
 * Note: Cryptographic constant time implementation
 *
 * Examples:       0 -> 0
 *                 1 -> 1
 *              3328 -> 3328
 *                -1 -> 3328
 *                -2 -> 3327
 *             -3328 -> 1
 *
 * Arguments: c: signed coefficient to be converted
 ************************************************************/
static INLINE uint16_t scalar_signed_to_unsigned_q(int16_t c)
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

MLKEM_NATIVE_INTERNAL_API
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
#else  /* MLKEM_USE_NATIVE_POLY_REDUCE */
MLKEM_NATIVE_INTERNAL_API
void poly_reduce(poly *r)
{
  poly_reduce_native(r->coeffs);
  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#endif /* MLKEM_USE_NATIVE_POLY_REDUCE */

MLKEM_NATIVE_INTERNAL_API
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

MLKEM_NATIVE_INTERNAL_API
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

#if !defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
MLKEM_NATIVE_INTERNAL_API
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
#else  /* MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE */
MLKEM_NATIVE_INTERNAL_API
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
{
  poly_mulcache_compute_native(x->coeffs, a->coeffs);
  /* Omitting bounds assertion since native implementations may
   * decide not to use a mulcache. Note that the C backend implementation
   * of poly_basemul_montgomery_cached() does still include the check. */
}
#endif /* MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE */

#if !defined(MLKEM_USE_NATIVE_NTT)
/*
 * Computes a block CT butterflies with a fixed twiddle factor,
 * using Montgomery multiplication.
 * Parameters:
 * - r: Pointer to base of polynomial (_not_ the base of butterfly block)
 * - root: Twiddle factor to use for the butterfly. This must be in
 *         Montgomery form and signed canonical.
 * - start: Offset to the beginning of the butterfly block
 * - len: Index difference between coefficients subject to a butterfly
 * - bound: Ghost variable describing coefficient bound: Prior to `start`,
 *          coefficients must be bound by `bound + MLKEM_Q`. Post `start`,
 *          they must be bound by `bound`.
 * When this function returns, output coefficients in the index range
 * [start, start+2*len) have bound bumped to `bound + MLKEM_Q`.
 * Example:
 * - start=8, len=4
 *   This would compute the following four butterflies
 *          8     --    12
 *             9    --     13
 *                10   --     14
 *                   11   --     15
 * - start=4, len=2
 *   This would compute the following two butterflies
 *          4 -- 6
 *             5 -- 7
 */
static void ntt_butterfly_block(int16_t r[MLKEM_N], int16_t zeta,
                                unsigned start, unsigned len, int bound)
__contract__(
  requires(start < MLKEM_N)
  requires(1 <= len && len <= MLKEM_N / 2 && start + 2 * len <= MLKEM_N)
  requires(0 <= bound && bound < INT16_MAX - MLKEM_Q)
  requires(-HALF_Q < zeta && zeta < HALF_Q)
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
    invariant(array_abs_bound(r, j + len,     MLKEM_N,     bound)))
  {
    int16_t t;
    t = fqmul(r[j + len], zeta);
    r[j + len] = r[j] - t;
    r[j] = r[j] + t;
  }
}

/*
 *Compute one layer of forward NTT
 * Parameters:
 * - r: Pointer to base of polynomial
 * - len: Stride of butterflies in this layer.
 * - layer: Ghost variable indicating which layer is being applied.
 *          Must match `len` via `len == MLKEM_N >> layer`.
 * Note: `len` could be dropped and computed in the function, but
 *   we are following the structure of the reference NTT from the
 *   official Kyber implementation here, merely adding `layer` as
 *   a ghost variable for the specifications.
 */
static void ntt_layer(int16_t r[MLKEM_N], unsigned len, unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(1 <= layer && layer <= 7 && len == (MLKEM_N >> layer))
  requires(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, (layer + 1) * MLKEM_Q)))
{
  unsigned start, k;
  /* `layer` is a ghost variable only needed in the CBMC specification */
  ((void)layer);
  /* Twiddle factors for layer n start at index 2^(layer-1) */
  k = MLKEM_N / (2 * len);
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(start < MLKEM_N + 2 * len)
    invariant(k <= MLKEM_N / 2 && 2 * len * k == start + MLKEM_N)
    invariant(array_abs_bound(r, 0, start, layer * MLKEM_Q + MLKEM_Q))
    invariant(array_abs_bound(r, start, MLKEM_N, layer * MLKEM_Q)))
  {
    int16_t zeta = zetas[k++];
    ntt_butterfly_block(r, zeta, start, len, layer * MLKEM_Q);
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

MLKEM_NATIVE_INTERNAL_API
void poly_ntt(poly *p)
{
  unsigned len, layer;
  int16_t *r;
  debug_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  r = p->coeffs;

  for (len = 128, layer = 1; len >= 2; len >>= 1, layer++)
  __loop__(
    invariant(1 <= layer && layer <= 8 && len == (MLKEM_N >> layer))
    invariant(array_abs_bound(r, 0, MLKEM_N, layer * MLKEM_Q)))
  {
    ntt_layer(r, len, layer);
  }

  /* Check the stronger bound */
  debug_assert_abs_bound(p, MLKEM_N, NTT_BOUND);
}
#else  /* MLKEM_USE_NATIVE_NTT */

MLKEM_NATIVE_INTERNAL_API
void poly_ntt(poly *p)
{
  debug_assert_abs_bound(p, MLKEM_N, MLKEM_Q);
  ntt_native(p->coeffs);
  debug_assert_abs_bound(p, MLKEM_N, NTT_BOUND);
}
#endif /* MLKEM_USE_NATIVE_NTT */

#if !defined(MLKEM_USE_NATIVE_INTT)

/* Compute one layer of inverse NTT */
static void invntt_layer(int16_t *r, unsigned len, unsigned layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(2 <= len && len <= 128 && 1 <= layer && layer <= 7)
  requires(len == (1 << (8 - layer)))
  requires(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
{
  unsigned start, k;
  /* `layer` is a ghost variable used only in the specification */
  ((void)layer);
  k = MLKEM_N / len - 1;
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q))
    invariant(start <= MLKEM_N && k <= 127)
    /* Normalised form of k == MLKEM_N / len - 1 - start / (2 * len) */
    invariant(2 * len * k + start == 2 * MLKEM_N - 2 * len))
  {
    unsigned j;
    int16_t zeta = zetas[k--];
    for (j = start; j < start + len; j++)
    __loop__(
      invariant(start <= j && j <= start + len)
      invariant(start <= MLKEM_N && k <= 127)
      invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
    {
      int16_t t = r[j];
      r[j] = barrett_reduce(t + r[j + len]);
      r[j + len] = r[j + len] - t;
      r[j + len] = fqmul(r[j + len], zeta);
    }
  }
}

MLKEM_NATIVE_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  /*
   * Scale input polynomial to account for Montgomery factor
   * and NTT twist. This also brings coefficients down to
   * absolute value < MLKEM_Q.
   */
  unsigned j, len, layer;
  const int16_t f = 1441;
  int16_t *r = p->coeffs;

  for (j = 0; j < MLKEM_N; j++)
  __loop__(
    invariant(j <= MLKEM_N)
    invariant(array_abs_bound(r, 0, j, MLKEM_Q)))
  {
    r[j] = fqmul(r[j], f);
  }

  /* Run the invNTT layers */
  for (len = 2, layer = 7; len <= 128; len <<= 1, layer--)
  __loop__(
    invariant(2 <= len && len <= 256 && layer <= 7 && len == (1 << (8 - layer)))
    invariant(array_abs_bound(r, 0, MLKEM_N, MLKEM_Q)))
  {
    invntt_layer(p->coeffs, len, layer);
  }

  debug_assert_abs_bound(p, MLKEM_N, INVNTT_BOUND);
}
#else  /* MLKEM_USE_NATIVE_INTT */

MLKEM_NATIVE_INTERNAL_API
void poly_invntt_tomont(poly *p)
{
  intt_native(p->coeffs);
  debug_assert_abs_bound(p, MLKEM_N, INVNTT_BOUND);
}
#endif /* MLKEM_USE_NATIVE_INTT */

#if defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || (MLKEM_K == 2 || MLKEM_K == 3)
MLKEM_NATIVE_INTERNAL_API
void poly_compress_d4(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4], const poly *a)
{
  unsigned i;
  debug_assert_bound(a, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_N / 8; i++)
  __loop__(invariant(i <= MLKEM_N / 8))
  {
    unsigned j;
    uint8_t t[8] = {0};
    for (j = 0; j < 8; j++)
    __loop__(
      invariant(i <= MLKEM_N / 8 && j <= 8)
      invariant(array_bound(t, 0, j, 0, 16)))
    {
      t[j] = scalar_compress_d4(a->coeffs[8 * i + j]);
    }

    r[i * 4] = t[0] | (t[1] << 4);
    r[i * 4 + 1] = t[2] | (t[3] << 4);
    r[i * 4 + 2] = t[4] | (t[5] << 4);
    r[i * 4 + 3] = t[6] | (t[7] << 4);
  }
}

MLKEM_NATIVE_INTERNAL_API
void poly_compress_d10(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10], const poly *a)
{
  unsigned j;
  debug_assert_bound(a, MLKEM_N, 0, MLKEM_Q);
  for (j = 0; j < MLKEM_N / 4; j++)
  __loop__(invariant(j <= MLKEM_N / 4))
  {
    unsigned k;
    uint16_t t[4];
    for (k = 0; k < 4; k++)
    __loop__(
      invariant(k <= 4)
      invariant(forall(r, 0, k, t[r] < (1u << 10))))
    {
      t[k] = scalar_compress_d10(a->coeffs[4 * j + k]);
    }

    /*
     * Make all implicit truncation explicit. No data is being
     * truncated for the LHS's since each t[i] is 10-bit in size.
     */
    r[5 * j + 0] = (t[0] >> 0) & 0xFF;
    r[5 * j + 1] = (t[0] >> 8) | ((t[1] << 2) & 0xFF);
    r[5 * j + 2] = (t[1] >> 6) | ((t[2] << 4) & 0xFF);
    r[5 * j + 3] = (t[2] >> 4) | ((t[3] << 6) & 0xFF);
    r[5 * j + 4] = (t[3] >> 2);
  }
}

MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d4(poly *r, const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D4])
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 2; i++)
  __loop__(
    invariant(i <= MLKEM_N / 2)
    invariant(array_bound(r->coeffs, 0, 2 * i, 0, MLKEM_Q)))
  {
    r->coeffs[2 * i + 0] = scalar_decompress_d4((a[i] >> 0) & 0xF);
    r->coeffs[2 * i + 1] = scalar_decompress_d4((a[i] >> 4) & 0xF);
  }

  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}

MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d10(poly *r,
                         const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D10])
{
  unsigned j;
  for (j = 0; j < MLKEM_N / 4; j++)
  __loop__(
    invariant(j <= MLKEM_N / 4)
    invariant(array_bound(r->coeffs, 0, 4 * j, 0, MLKEM_Q)))
  {
    unsigned k;
    uint16_t t[4];
    uint8_t const *base = &a[5 * j];

    t[0] = 0x3FF & ((base[0] >> 0) | ((uint16_t)base[1] << 8));
    t[1] = 0x3FF & ((base[1] >> 2) | ((uint16_t)base[2] << 6));
    t[2] = 0x3FF & ((base[2] >> 4) | ((uint16_t)base[3] << 4));
    t[3] = 0x3FF & ((base[3] >> 6) | ((uint16_t)base[4] << 2));

    for (k = 0; k < 4; k++)
    __loop__(
      invariant(k <= 4)
      invariant(array_bound(r->coeffs, 0, 4 * j + k, 0, MLKEM_Q)))
    {
      r->coeffs[4 * j + k] = scalar_decompress_d10(t[k]);
    }
  }

  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#endif /* defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || (MLKEM_K == 2 \
          || MLKEM_K == 3) */

#if defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || MLKEM_K == 4
MLKEM_NATIVE_INTERNAL_API
void poly_compress_d5(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5], const poly *a)
{
  unsigned i;
  debug_assert_bound(a, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_N / 8; i++)
  __loop__(invariant(i <= MLKEM_N / 8))
  {
    unsigned j;
    uint8_t t[8] = {0};
    for (j = 0; j < 8; j++)
    __loop__(
      invariant(i <= MLKEM_N / 8 && j <= 8)
      invariant(array_bound(t, 0, j, 0, 32)))
    {
      t[j] = scalar_compress_d5(a->coeffs[8 * i + j]);
    }

    /*
     * Explicitly truncate to avoid warning about
     * implicit truncation in CBMC, and use array indexing into
     * r rather than pointer-arithmetic to simplify verification
     */
    r[i * 5] = 0xFF & ((t[0] >> 0) | (t[1] << 5));
    r[i * 5 + 1] = 0xFF & ((t[1] >> 3) | (t[2] << 2) | (t[3] << 7));
    r[i * 5 + 2] = 0xFF & ((t[3] >> 1) | (t[4] << 4));
    r[i * 5 + 3] = 0xFF & ((t[4] >> 4) | (t[5] << 1) | (t[6] << 6));
    r[i * 5 + 4] = 0xFF & ((t[6] >> 2) | (t[7] << 3));
  }
}

MLKEM_NATIVE_INTERNAL_API
void poly_compress_d11(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11], const poly *a)
{
  unsigned j;
  debug_assert_bound(a, MLKEM_N, 0, MLKEM_Q);

  for (j = 0; j < MLKEM_N / 8; j++)
  __loop__(invariant(j <= MLKEM_N / 8))
  {
    unsigned k;
    uint16_t t[8];
    for (k = 0; k < 8; k++)
    __loop__(
      invariant(k <= 8)
      invariant(forall(r, 0, k, t[r] < (1u << 11))))
    {
      t[k] = scalar_compress_d11(a->coeffs[8 * j + k]);
    }

    /*
     * Make all implicit truncation explicit. No data is being
     * truncated for the LHS's since each t[i] is 11-bit in size.
     */
    r[11 * j + 0] = (t[0] >> 0) & 0xFF;
    r[11 * j + 1] = (t[0] >> 8) | ((t[1] << 3) & 0xFF);
    r[11 * j + 2] = (t[1] >> 5) | ((t[2] << 6) & 0xFF);
    r[11 * j + 3] = (t[2] >> 2) & 0xFF;
    r[11 * j + 4] = (t[2] >> 10) | ((t[3] << 1) & 0xFF);
    r[11 * j + 5] = (t[3] >> 7) | ((t[4] << 4) & 0xFF);
    r[11 * j + 6] = (t[4] >> 4) | ((t[5] << 7) & 0xFF);
    r[11 * j + 7] = (t[5] >> 1) & 0xFF;
    r[11 * j + 8] = (t[5] >> 9) | ((t[6] << 2) & 0xFF);
    r[11 * j + 9] = (t[6] >> 6) | ((t[7] << 5) & 0xFF);
    r[11 * j + 10] = (t[7] >> 3);
  }
}

MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d5(poly *r, const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D5])
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 8; i++)
  __loop__(
    invariant(i <= MLKEM_N / 8)
    invariant(array_bound(r->coeffs, 0, 8 * i, 0, MLKEM_Q)))
  {
    unsigned j;
    uint8_t t[8];
    const unsigned offset = i * 5;
    /*
     * Explicitly truncate to avoid warning about
     * implicit truncation in CBMC and unwind loop for ease
     * of proof.
     */

    /*
     * Decompress 5 8-bit bytes (so 40 bits) into
     * 8 5-bit values stored in t[]
     */
    t[0] = 0x1F & (a[offset + 0] >> 0);
    t[1] = 0x1F & ((a[offset + 0] >> 5) | (a[offset + 1] << 3));
    t[2] = 0x1F & (a[offset + 1] >> 2);
    t[3] = 0x1F & ((a[offset + 1] >> 7) | (a[offset + 2] << 1));
    t[4] = 0x1F & ((a[offset + 2] >> 4) | (a[offset + 3] << 4));
    t[5] = 0x1F & (a[offset + 3] >> 1);
    t[6] = 0x1F & ((a[offset + 3] >> 6) | (a[offset + 4] << 2));
    t[7] = 0x1F & (a[offset + 4] >> 3);

    /* and copy to the correct slice in r[] */
    for (j = 0; j < 8; j++)
    __loop__(
      invariant(j <= 8 && i <= MLKEM_N / 8)
      invariant(array_bound(r->coeffs, 0, 8 * i + j, 0, MLKEM_Q)))
    {
      r->coeffs[8 * i + j] = scalar_decompress_d5(t[j]);
    }
  }

  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}

MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d11(poly *r,
                         const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D11])
{
  unsigned j;
  for (j = 0; j < MLKEM_N / 8; j++)
  __loop__(
    invariant(j <= MLKEM_N / 8)
    invariant(array_bound(r->coeffs, 0, 8 * j, 0, MLKEM_Q)))
  {
    unsigned k;
    uint16_t t[8];
    uint8_t const *base = &a[11 * j];
    t[0] = 0x7FF & ((base[0] >> 0) | ((uint16_t)base[1] << 8));
    t[1] = 0x7FF & ((base[1] >> 3) | ((uint16_t)base[2] << 5));
    t[2] = 0x7FF & ((base[2] >> 6) | ((uint16_t)base[3] << 2) |
                    ((uint16_t)base[4] << 10));
    t[3] = 0x7FF & ((base[4] >> 1) | ((uint16_t)base[5] << 7));
    t[4] = 0x7FF & ((base[5] >> 4) | ((uint16_t)base[6] << 4));
    t[5] = 0x7FF & ((base[6] >> 7) | ((uint16_t)base[7] << 1) |
                    ((uint16_t)base[8] << 9));
    t[6] = 0x7FF & ((base[8] >> 2) | ((uint16_t)base[9] << 6));
    t[7] = 0x7FF & ((base[9] >> 5) | ((uint16_t)base[10] << 3));

    for (k = 0; k < 8; k++)
    __loop__(
      invariant(k <= 8)
      invariant(array_bound(r->coeffs, 0, 8 * j + k, 0, MLKEM_Q)))
    {
      r->coeffs[8 * j + k] = scalar_decompress_d11(t[k]);
    }
  }

  debug_assert_bound(r, MLKEM_N, 0, MLKEM_Q);
}
#endif /* MLKEM_NATIVE_MULTILEVEL_BUILD) || MLKEM_K == 4 */

#if !defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
MLKEM_NATIVE_INTERNAL_API
void poly_tobytes(uint8_t r[MLKEM_POLYBYTES], const poly *a)
{
  unsigned i;
  debug_assert_bound(a, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_N / 2; i++)
  __loop__(invariant(i <= MLKEM_N / 2))
  {
    const uint16_t t0 = a->coeffs[2 * i];
    const uint16_t t1 = a->coeffs[2 * i + 1];
    /*
     * t0 and t1 are both < MLKEM_Q, so contain at most 12 bits each of
     * significant data, so these can be packed into 24 bits or exactly
     * 3 bytes, as follows.
     */

    /* Least significant bits 0 - 7 of t0. */
    r[3 * i + 0] = t0 & 0xFF;

    /*
     * Most significant bits 8 - 11 of t0 become the least significant
     * nibble of the second byte. The least significant 4 bits
     * of t1 become the upper nibble of the second byte.
     */
    r[3 * i + 1] = (t0 >> 8) | ((t1 << 4) & 0xF0);

    /* Bits 4 - 11 of t1 become the third byte. */
    r[3 * i + 2] = t1 >> 4;
  }
}
#else  /* MLKEM_USE_NATIVE_POLY_TOBYTES */
MLKEM_NATIVE_INTERNAL_API
void poly_tobytes(uint8_t r[MLKEM_POLYBYTES], const poly *a)
{
  debug_assert_bound(a, MLKEM_N, 0, MLKEM_Q);
  poly_tobytes_native(r, a->coeffs);
}
#endif /* MLKEM_USE_NATIVE_POLY_TOBYTES */

#if !defined(MLKEM_USE_NATIVE_POLY_FROMBYTES)
MLKEM_NATIVE_INTERNAL_API
void poly_frombytes(poly *r, const uint8_t a[MLKEM_POLYBYTES])
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 2; i++)
  __loop__(
    invariant(i <= MLKEM_N / 2)
    invariant(array_bound(r->coeffs, 0, 2 * i, 0, UINT12_LIMIT)))
  {
    const uint8_t t0 = a[3 * i + 0];
    const uint8_t t1 = a[3 * i + 1];
    const uint8_t t2 = a[3 * i + 2];
    r->coeffs[2 * i + 0] = t0 | ((t1 << 8) & 0xFFF);
    r->coeffs[2 * i + 1] = (t1 >> 4) | (t2 << 4);
  }

  /* Note that the coefficients are not canonical */
  debug_assert_bound(r, MLKEM_N, 0, UINT12_LIMIT);
}
#else  /* MLKEM_USE_NATIVE_POLY_FROMBYTES */
MLKEM_NATIVE_INTERNAL_API
void poly_frombytes(poly *r, const uint8_t a[MLKEM_POLYBYTES])
{
  poly_frombytes_native(r->coeffs, a);
}
#endif /* MLKEM_USE_NATIVE_POLY_FROMBYTES */

MLKEM_NATIVE_INTERNAL_API
void poly_frommsg(poly *r, const uint8_t msg[MLKEM_INDCPA_MSGBYTES])
{
  unsigned i;
#if (MLKEM_INDCPA_MSGBYTES != MLKEM_N / 8)
#error "MLKEM_INDCPA_MSGBYTES must be equal to MLKEM_N/8 bytes!"
#endif

  for (i = 0; i < MLKEM_N / 8; i++)
  __loop__(
    invariant(i <= MLKEM_N / 8)
    invariant(array_bound(r->coeffs, 0, 8 * i, 0, MLKEM_Q)))
  {
    unsigned j;
    for (j = 0; j < 8; j++)
    __loop__(
      invariant(i <  MLKEM_N / 8 && j <= 8)
      invariant(array_bound(r->coeffs, 0, 8 * i + j, 0, MLKEM_Q)))
    {
      /* Prevent the compiler from recognizing this as a bit selection */
      uint8_t mask = value_barrier_u8(1u << j);
      r->coeffs[8 * i + j] = ct_sel_int16(HALF_Q, 0, msg[i] & mask);
    }
  }
  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}

MLKEM_NATIVE_INTERNAL_API
void poly_tomsg(uint8_t msg[MLKEM_INDCPA_MSGBYTES], const poly *a)
{
  unsigned i;
  debug_assert_bound(a, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_N / 8; i++)
  __loop__(invariant(i <= MLKEM_N / 8))
  {
    unsigned j;
    msg[i] = 0;
    for (j = 0; j < 8; j++)
    __loop__(
      invariant(i <= MLKEM_N / 8 && j <= 8))
    {
      uint32_t t = scalar_compress_d1(a->coeffs[8 * i + j]);
      msg[i] |= t << j;
    }
  }
}

static unsigned rej_uniform_scalar(int16_t *r, unsigned target, unsigned offset,
                                   const uint8_t *buf, unsigned buflen)
__contract__(
  requires(offset <= target && target <= 4096 && buflen <= 4096 && buflen % 3 == 0)
  requires(memory_no_alias(r, sizeof(int16_t) * target))
  requires(memory_no_alias(buf, buflen))
  requires(array_bound(r, 0, offset, 0, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * target))
  ensures(offset <= return_value && return_value <= target)
  ensures(array_bound(r, 0, return_value, 0, MLKEM_Q))
)
{
  unsigned ctr, pos;
  uint16_t val0, val1;

  debug_assert_bound(r, offset, 0, MLKEM_Q);

  ctr = offset;
  pos = 0;
  /* pos + 3 cannot overflow due to the assumption buflen <= 4096 */
  while (ctr < target && pos + 3 <= buflen)
  __loop__(
    invariant(offset <= ctr && ctr <= target && pos <= buflen)
    invariant(ctr > 0 ==> array_bound(r, 0, ctr, 0, MLKEM_Q)))
  {
    val0 = ((buf[pos + 0] >> 0) | ((uint16_t)buf[pos + 1] << 8)) & 0xFFF;
    val1 = ((buf[pos + 1] >> 4) | ((uint16_t)buf[pos + 2] << 4)) & 0xFFF;
    pos += 3;

    if (val0 < MLKEM_Q)
    {
      r[ctr++] = val0;
    }
    if (ctr < target && val1 < MLKEM_Q)
    {
      r[ctr++] = val1;
    }
  }

  debug_assert_bound(r, ctr, 0, MLKEM_Q);
  return ctr;
}

/*************************************************
 * Name:        rej_uniform
 *
 * Description: Run rejection sampling on uniform random bytes to generate
 *              uniform random integers mod q
 *
 * Arguments:   - int16_t *r:          pointer to output buffer
 *              - unsigned target:     requested number of 16-bit integers
 *                                     (uniform mod q).
 *                                     Must be <= 4096.
 *              - unsigned offset:     number of 16-bit integers that have
 *                                     already been sampled.
 *                                     Must be <= target.
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned buflen:     length of input buffer in bytes
 *                                     Must be <= 4096.
 *                                     Must be a multiple of 3.
 *
 * Note: Strictly speaking, only a few values of buflen near UINT_MAX need
 * excluding. The limit of 128 is somewhat arbitary but sufficient for all
 * uses of this function. Similarly, the actual limit for target is UINT_MAX/2.
 *
 * Returns the new offset of sampled 16-bit integers, at most target,
 * and at least the initial offset.
 * If the new offset is strictly less than len, all of the input buffers
 * is guaranteed to have been consumed. If it is equal to len, no information
 * is provided on how many bytes of the input buffer have been consumed.
 **************************************************/

/*
 * NOTE: The signature differs from the Kyber reference implementation
 * in that it adds the offset and always expects the base of the target
 * buffer. This avoids shifting the buffer base in the caller, which appears
 * tricky to reason about.
 */
static unsigned rej_uniform(int16_t *r, unsigned target, unsigned offset,
                            const uint8_t *buf, unsigned buflen)
__contract__(
  requires(offset <= target && target <= 4096 && buflen <= 4096 && buflen % 3 == 0)
  requires(memory_no_alias(r, sizeof(int16_t) * target))
  requires(memory_no_alias(buf, buflen))
  requires(array_bound(r, 0, offset, 0, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * target))
  ensures(offset <= return_value && return_value <= target)
  ensures(array_bound(r, 0, return_value, 0, MLKEM_Q))
)
{
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
  if (offset == 0)
  {
    int ret = rej_uniform_native(r, target, buf, buflen);
    if (ret != -1)
    {
      unsigned res = (unsigned)ret;
      debug_assert_bound(r, res, 0, MLKEM_Q);
      return res;
    }
  }
#endif /* MLKEM_USE_NATIVE_REJ_UNIFORM */

  return rej_uniform_scalar(r, target, offset, buf, buflen);
}

#ifndef MLKEM_GEN_MATRIX_NBLOCKS
#define MLKEM_GEN_MATRIX_NBLOCKS \
  ((12 * MLKEM_N / 8 * (1 << 12) / MLKEM_Q + XOF_RATE) / XOF_RATE)
#endif

MLKEM_NATIVE_INTERNAL_API
void poly_rej_uniform_x4(poly *vec, uint8_t *seed[4])
{
  /* Temporary buffers for XOF output before rejection sampling */
  ALIGN uint8_t buf0[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  ALIGN uint8_t buf1[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  ALIGN uint8_t buf2[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  ALIGN uint8_t buf3[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];

  /* Tracks the number of coefficients we have already sampled */
  unsigned ctr[KECCAK_WAY];
  xof_x4_ctx statex;
  unsigned buflen;

  /* seed is MLKEM_SYMBYTES + 2 bytes long, but padded to MLKEM_SYMBYTES + 16 */
  xof_x4_init(&statex);
  xof_x4_absorb(&statex, seed[0], seed[1], seed[2], seed[3],
                MLKEM_SYMBYTES + 2);

  /*
   * Initially, squeeze heuristic number of MLKEM_GEN_MATRIX_NBLOCKS.
   * This should generate the matrix entries with high probability.
   */
  xof_x4_squeezeblocks(buf0, buf1, buf2, buf3, MLKEM_GEN_MATRIX_NBLOCKS,
                       &statex);
  buflen = MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE;
  ctr[0] = rej_uniform(vec[0].coeffs, MLKEM_N, 0, buf0, buflen);
  ctr[1] = rej_uniform(vec[1].coeffs, MLKEM_N, 0, buf1, buflen);
  ctr[2] = rej_uniform(vec[2].coeffs, MLKEM_N, 0, buf2, buflen);
  ctr[3] = rej_uniform(vec[3].coeffs, MLKEM_N, 0, buf3, buflen);

  /*
   * So long as not all matrix entries have been generated, squeeze
   * one more block a time until we're done.
   */
  buflen = XOF_RATE;
  while (ctr[0] < MLKEM_N || ctr[1] < MLKEM_N || ctr[2] < MLKEM_N ||
         ctr[3] < MLKEM_N)
  __loop__(
    assigns(ctr, statex, memory_slice(vec, sizeof(poly) * 4), object_whole(buf0),
       object_whole(buf1), object_whole(buf2), object_whole(buf3))
    invariant(ctr[0] <= MLKEM_N && ctr[1] <= MLKEM_N)
    invariant(ctr[2] <= MLKEM_N && ctr[3] <= MLKEM_N)
    invariant(ctr[0] > 0 ==> array_bound(vec[0].coeffs, 0, ctr[0], 0, MLKEM_Q))
    invariant(ctr[1] > 0 ==> array_bound(vec[1].coeffs, 0, ctr[1], 0, MLKEM_Q))
    invariant(ctr[2] > 0 ==> array_bound(vec[2].coeffs, 0, ctr[2], 0, MLKEM_Q))
    invariant(ctr[3] > 0 ==> array_bound(vec[3].coeffs, 0, ctr[3], 0, MLKEM_Q)))
  {
    xof_x4_squeezeblocks(buf0, buf1, buf2, buf3, 1, &statex);
    ctr[0] = rej_uniform(vec[0].coeffs, MLKEM_N, ctr[0], buf0, buflen);
    ctr[1] = rej_uniform(vec[1].coeffs, MLKEM_N, ctr[1], buf1, buflen);
    ctr[2] = rej_uniform(vec[2].coeffs, MLKEM_N, ctr[2], buf2, buflen);
    ctr[3] = rej_uniform(vec[3].coeffs, MLKEM_N, ctr[3], buf3, buflen);
  }

  xof_x4_release(&statex);
}

MLKEM_NATIVE_INTERNAL_API
void poly_rej_uniform(poly *entry, uint8_t seed[MLKEM_SYMBYTES + 2])
{
  xof_ctx state;
  ALIGN uint8_t buf[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  unsigned ctr, buflen;

  xof_init(&state);
  xof_absorb(&state, seed, MLKEM_SYMBYTES + 2);

  /* Initially, squeeze + sample heuristic number of MLKEM_GEN_MATRIX_NBLOCKS.
   */
  /* This should generate the matrix entry with high probability. */
  xof_squeezeblocks(buf, MLKEM_GEN_MATRIX_NBLOCKS, &state);
  buflen = MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE;
  ctr = rej_uniform(entry->coeffs, MLKEM_N, 0, buf, buflen);

  /* Squeeze + sample one more block a time until we're done */
  buflen = XOF_RATE;
  while (ctr < MLKEM_N)
  __loop__(
    assigns(ctr, state, memory_slice(entry, sizeof(poly)), object_whole(buf))
    invariant(ctr <= MLKEM_N)
    invariant(array_bound(entry->coeffs, 0, ctr, 0, MLKEM_Q)))
  {
    xof_squeezeblocks(buf, 1, &state);
    ctr = rej_uniform(entry->coeffs, MLKEM_N, ctr, buf, buflen);
  }

  xof_release(&state);
}

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define load32_littleendian MLKEM_NAMESPACE(load32_littleendian)
#define load24_littleendian MLKEM_NAMESPACE(load24_littleendian)
/* End of static namespacing */

/*************************************************
 * Name:        load32_littleendian
 *
 * Description: load 4 bytes into a 32-bit integer
 *              in little-endian order
 *
 * Arguments:   - const uint8_t *x: pointer to input byte array
 *
 * Returns 32-bit unsigned integer loaded from x
 **************************************************/
static uint32_t load32_littleendian(const uint8_t x[4])
{
  uint32_t r;
  r = (uint32_t)x[0];
  r |= (uint32_t)x[1] << 8;
  r |= (uint32_t)x[2] << 16;
  r |= (uint32_t)x[3] << 24;
  return r;
}

MLKEM_NATIVE_INTERNAL_API
void poly_cbd2(poly *r, const uint8_t buf[2 * MLKEM_N / 4])
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 8; i++)
  __loop__(
    invariant(i <= MLKEM_N / 8)
    invariant(array_abs_bound(r->coeffs, 0, 8 * i, 3)))
  {
    unsigned j;
    uint32_t t = load32_littleendian(buf + 4 * i);
    uint32_t d = t & 0x55555555;
    d += (t >> 1) & 0x55555555;

    for (j = 0; j < 8; j++)
    __loop__(
      invariant(i <= MLKEM_N / 8 && j <= 8)
      invariant(array_abs_bound(r->coeffs, 0, 8 * i + j, 3)))
    {
      const int16_t a = (d >> (4 * j + 0)) & 0x3;
      const int16_t b = (d >> (4 * j + 2)) & 0x3;
      r->coeffs[8 * i + j] = a - b;
    }
  }
}

#if defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || MLKEM_ETA1 == 3
/*************************************************
 * Name:        load24_littleendian
 *
 * Description: load 3 bytes into a 32-bit integer
 *              in little-endian order.
 *              This function is only needed for ML-KEM-512
 *
 * Arguments:   - const uint8_t *x: pointer to input byte array
 *
 * Returns 32-bit unsigned integer loaded from x (most significant byte is zero)
 **************************************************/
static uint32_t load24_littleendian(const uint8_t x[3])
{
  uint32_t r;
  r = (uint32_t)x[0];
  r |= (uint32_t)x[1] << 8;
  r |= (uint32_t)x[2] << 16;
  return r;
}

MLKEM_NATIVE_INTERNAL_API
void poly_cbd3(poly *r, const uint8_t buf[3 * MLKEM_N / 4])
{
  unsigned i;
  for (i = 0; i < MLKEM_N / 4; i++)
  __loop__(
    invariant(i <= MLKEM_N / 4)
    invariant(array_abs_bound(r->coeffs, 0, 4 * i, 4)))
  {
    unsigned j;
    const uint32_t t = load24_littleendian(buf + 3 * i);
    uint32_t d = t & 0x00249249;
    d += (t >> 1) & 0x00249249;
    d += (t >> 2) & 0x00249249;

    for (j = 0; j < 4; j++)
    __loop__(
      invariant(i <= MLKEM_N / 4 && j <= 4)
      invariant(array_abs_bound(r->coeffs, 0, 4 * i + j, 4)))
    {
      const int16_t a = (d >> (6 * j + 0)) & 0x7;
      const int16_t b = (d >> (6 * j + 3)) & 0x7;
      r->coeffs[4 * i + j] = a - b;
    }
  }
}
#endif /* defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || MLKEM_ETA1 == \
          3 */

#else /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */

MLKEM_NATIVE_EMPTY_CU(poly)

#endif /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */
