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

static const int16_t zetas_avx2[64] = {
  -1103, 555, -1251, 1550, 422, 177, -291, 1574, -246, 1159, -777, -602, -1590, -872, 418, -156,
  430, 843, 871, 105, 587, -235, -460, 1653, 778, -147, 1483, 1119, 644, 349, 329, -75,
  817, 603, 1322, -1465, -1215, 1218, -874, -1187, -1185, -1278, -1510, -870, -108, 996, 958, 1522,
  1097, 610, -1285, 384, -136, -1335, 220, 1670, -1530, 794, -854, 478, -308, 991, -1460, 1628,
};

#define QINV (-3327) /* q^-1 mod 2^16 */

void poly_mulcache_compute_avx2(poly_mulcache *x, const poly *y) {
  __m256i q, qinv, a0, a1, z, t0, t1, s0, s1, r0, r1;

  q    = _mm256_set1_epi16(MLKEM_Q);
  qinv = _mm256_set1_epi16(QINV);

  for (int j = 0; j < 4; j++) {
    a0 = _mm256_load_si256((const __m256i*)&y->coeffs[64*j+16]);
    a1 = _mm256_load_si256((const __m256i*)&y->coeffs[64*j+48]);
    z  = _mm256_load_si256((const __m256i*)&zetas_avx2[16*j]);

    t0 = _mm256_mullo_epi16(a0, qinv);
    t1 = _mm256_mullo_epi16(a1, qinv);
    t0 = _mm256_mullo_epi16(t0, z);
    t1 = _mm256_mullo_epi16(t1, z);

    s0 = _mm256_mulhi_epi16(a0, z);
    s1 = _mm256_mulhi_epi16(a1, z);
    r0 = _mm256_mulhi_epi16(t0, q);
    r1 = _mm256_mulhi_epi16(t1, q);

    r0 = _mm256_sub_epi16(s0, r0);
    r1 = _mm256_sub_epi16(s1, r1);

    _mm256_store_si256((__m256i*)&x->coeffs[32*j], r0);
    _mm256_store_si256((__m256i*)&x->coeffs[32*j+16], r1);
  }
}

static void poly_basemul_montgomery_avx2(poly *r,
                                         const poly *a, const poly *b,
                                         const poly_mulcache *b_cache)
{
  basemul_avx2((__m256i *)r->coeffs,
               (const __m256i *)a->coeffs, (const __m256i *)b->coeffs,
               qdata.vec, (const __m256i *)b_cache->coeffs);
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
