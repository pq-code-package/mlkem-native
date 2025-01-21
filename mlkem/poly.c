/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "common.h"
#if !defined(MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED)

#include <stdint.h>
#include <string.h>
#include "arith_backend.h"
#include "cbd.h"
#include "cbmc.h"
#include "debug.h"
#include "fips202/fips202x4.h"
#include "ntt.h"
#include "poly.h"
#include "reduce.h"
#include "symmetric.h"
#include "verify.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define basemul_cached MLKEM_NAMESPACE_K(basemul_cached)
/* End of static namespacing */

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
  poly_tobytes_native(r, a);
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
  poly_frombytes_native(r, a);
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

/************************************************************
 * Name: basemul_cached
 *
 * Description: Computes a representative modulo q of
 *              (a0*b0 + a1*b_cached, a0*b1 + a1*b0)/65536
 *
 *              If b_cached is b1*zeta, this represents the
 *              product of (a0 + a1*X) and (b0 + b1*X) in
 *              Fq[X]/(X^2 - zeta).
 *
 * Arguments: - r: Pointer to output polynomial
 *                   Upon return, coefficients are bound by
 *                   2*MLKEM_Q in absolute value.
 *            - a: Pointer to first input polynomial
 *                   Every coefficient must be in [0..4095]
 *            - b: Pointer to second input polynomial
 *                   Can have arbitrary int16_t coefficients
 *            - b_cached: Some precomputed value, typically derived from
 *                   b1 and a twiddle factor. Can be an arbitary int16_t.
 ************************************************************/
static void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                           int16_t b_cached)
__contract__(
  requires(memory_no_alias(r, 2 * sizeof(int16_t)))
  requires(memory_no_alias(a, 2 * sizeof(int16_t)))
  requires(memory_no_alias(b, 2 * sizeof(int16_t)))
  requires(array_bound(a, 0, 2, 0, UINT12_LIMIT))
  assigns(memory_slice(r, 2 * sizeof(int16_t)))
  ensures(array_abs_bound(r, 0, 2, 2 * MLKEM_Q))
)
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
  poly_tomont_native(r);
  debug_assert_abs_bound(r, MLKEM_N, MLKEM_Q);
}
#endif /* MLKEM_USE_NATIVE_POLY_TOMONT */

#if !defined(MLKEM_USE_NATIVE_POLY_REDUCE)
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
  poly_reduce_native(r);
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
    x->coeffs[2 * i + 0] = fqmul(a->coeffs[4 * i + 1], layer7_zetas[i]);
    x->coeffs[2 * i + 1] = fqmul(a->coeffs[4 * i + 3], -layer7_zetas[i]);
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
  poly_mulcache_compute_native(x, a);
  /* Omitting bounds assertion since native implementations may
   * decide not to use a mulcache. Note that the C backend implementation
   * of poly_basemul_montgomery_cached() does still include the check. */
}
#endif /* MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE */

#else /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */

#define empty_cu_poly MLKEM_NAMESPACE_K(empty_cu_poly)
int empty_cu_poly;

#endif /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */
