/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "common.h"

#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)

#include "consts.h"

#include "poly.h"
#include "polyvec.h"

#include "arith_native_x86_64.h"
#include "x86_64_zetas_mulcache.h"

void poly_mulcache_compute_avx2(poly_mulcache *x, const poly *y)
{
  mulcache_compute_avx2((__m256i *)x->coeffs, (const __m256i *)y->coeffs,
                        (const __m256i *)zetas_mulcache_avx2, qdata.vec);
}

static void poly_basemul_montgomery_avx2(poly *r, const poly *a, const poly *b,
                                         const poly_mulcache *b_cache)
{
  basemul_avx2((__m256i *)r->coeffs, (const __m256i *)a->coeffs,
               (const __m256i *)b->coeffs, qdata.vec,
               (const __m256i *)b_cache->coeffs);
}

/*
 * Implementation from Kyber reference repository
 * https://github.com/pq-crystals/kyber/blob/main/avx2
 */
static void poly_add_avx2(poly *r, const poly *a, const poly *b)
{
  unsigned int i;
  __m256i f0, f1;

  for (i = 0; i < MLKEM_N; i += 16)
  {
    f0 = _mm256_load_si256((const __m256i *)&a->coeffs[i]);
    f1 = _mm256_load_si256((const __m256i *)&b->coeffs[i]);
    f0 = _mm256_add_epi16(f0, f1);
    _mm256_store_si256((__m256i *)&r->coeffs[i], f0);
  }
}

void polyvec_basemul_acc_montgomery_cached_avx2(poly *r, const polyvec *a,
                                                const polyvec *b,
                                                const polyvec_mulcache *b_cache)
{
  unsigned int i;
  poly t;

  /* Coefficient-wise bound of each basemul is 2q.
   * Since we are accumulating at most 4 times, the
   * overall bound is 8q < INT16_MAX. */
  poly_basemul_montgomery_avx2(r, &a->vec[0], &b->vec[0], &b_cache->vec[0]);
  for (i = 1; i < MLKEM_K; i++)
  {
    poly_basemul_montgomery_avx2(&t, &a->vec[i], &b->vec[i], &b_cache->vec[i]);
    poly_add_avx2(r, r, &t);
  }
}

#else /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */

/* Dummy constant to keep compiler happy despite empty CU */

#define empty_cu_avx2_basemul MLKEM_NAMESPACE(empty_cu_avx2_basemul)
int empty_cu_avx2_basemul;

#endif /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */
