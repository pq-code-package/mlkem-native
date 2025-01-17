/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "polyvec.h"
#include <stdint.h>
#include "arith_backend.h"
#include "ntt.h"
#include "poly.h"

#include "debug/debug.h"

MLKEM_NATIVE_INTERNAL_API
void polyvec_compress_du(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES_DU],
                         const polyvec *a)
{
  unsigned i;
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_K; i++)
  {
    poly_compress_du(r + i * MLKEM_POLYCOMPRESSEDBYTES_DU, &a->vec[i]);
  }
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_decompress_du(polyvec *r,
                           const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES_DU])
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_decompress_du(&r->vec[i], a + i * MLKEM_POLYCOMPRESSEDBYTES_DU);
  }

  debug_assert_bound_2d(r, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES], const polyvec *a)
{
  unsigned i;
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, MLKEM_Q);

  for (i = 0; i < MLKEM_K; i++)
  {
    poly_tobytes(r + i * MLKEM_POLYBYTES, &a->vec[i]);
  }
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_frombytes(polyvec *r, const uint8_t a[MLKEM_POLYVECBYTES])
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_frombytes(&r->vec[i], a + i * MLKEM_POLYBYTES);
  }

  debug_assert_bound_2d(r, MLKEM_K, MLKEM_N, 0, UINT12_LIMIT);
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_ntt(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_ntt(&r->vec[i]);
  }

  debug_assert_abs_bound_2d(r, MLKEM_K, MLKEM_N, NTT_BOUND);
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_invntt_tomont(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_invntt_tomont(&r->vec[i]);
  }

  debug_assert_abs_bound_2d(r, MLKEM_K, MLKEM_N, INVNTT_BOUND);
}

#if !defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
MLKEM_NATIVE_INTERNAL_API
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache)
{
  unsigned i;
  poly t;
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, UINT12_LIMIT);

  poly_basemul_montgomery_cached(r, &a->vec[0], &b->vec[0], &b_cache->vec[0]);
  for (i = 1; i < MLKEM_K; i++)
  {
    poly_basemul_montgomery_cached(&t, &a->vec[i], &b->vec[i],
                                   &b_cache->vec[i]);
    poly_add(r, &t);
  }

  /*
   * This bound is true for the C implementation, but not needed
   * in the higher level bounds reasoning. It is thus omitted
   * them from the spec to not unnecessarily constrain native
   * implementations, but checked here nonetheless.
   */
  debug_assert_abs_bound(r, MLKEM_K, MLKEM_N * 2 * MLKEM_Q);
}
#else  /* !MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */
MLKEM_NATIVE_INTERNAL_API
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache)
{
  debug_assert_bound_2d(a, MLKEM_K, MLKEM_N, 0, UINT12_LIMIT);
  /* Omitting bounds assertion for cache since native implementations may
   * decide not to use a mulcache. Note that the C backend implementation
   * of poly_basemul_montgomery_cached() does still include the check. */
  polyvec_basemul_acc_montgomery_cached_native(r, a, b, b_cache);
}
#endif /* MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

MLKEM_NATIVE_INTERNAL_API
void polyvec_basemul_acc_montgomery(poly *r, const polyvec *a, const polyvec *b)
{
  polyvec_mulcache b_cache;
  polyvec_mulcache_compute(&b_cache, b);
  polyvec_basemul_acc_montgomery_cached(r, a, b, &b_cache);
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_mulcache_compute(&x->vec[i], &a->vec[i]);
  }
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_reduce(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_reduce(&r->vec[i]);
  }

  debug_assert_bound_2d(r, MLKEM_K, MLKEM_N, 0, MLKEM_Q);
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_add(polyvec *r, const polyvec *b)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_add(&r->vec[i], &b->vec[i]);
  }
}

MLKEM_NATIVE_INTERNAL_API
void polyvec_tomont(polyvec *r)
{
  unsigned i;
  for (i = 0; i < MLKEM_K; i++)
  {
    poly_tomont(&r->vec[i]);
  }

  debug_assert_abs_bound_2d(r, MLKEM_K, MLKEM_N, MLKEM_Q);
}
