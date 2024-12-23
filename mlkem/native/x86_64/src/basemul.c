/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "../../../common.h"

#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)

#include "arith_native_x86_64.h"
#include "consts.h"

/*
 * Implementation from Kyber reference repository
 * https://github.com/pq-crystals/kyber/blob/main/avx2
 */
static void poly_add_avx2(int16_t r[MLKEM_N], const int16_t a[MLKEM_N],
                          const int16_t b[MLKEM_N])
{
  unsigned i;
  __m256i f0, f1;

  for (i = 0; i < MLKEM_N; i += 16)
  {
    f0 = _mm256_load_si256((const __m256i *)&a[i]);
    f1 = _mm256_load_si256((const __m256i *)&b[i]);
    f0 = _mm256_add_epi16(f0, f1);
    _mm256_store_si256((__m256i *)&r[i], f0);
  }
}

void polyvec_basemul_acc_montgomery_cached_avx2(
    int16_t r[MLKEM_N], const int16_t a[MLKEM_K * MLKEM_N],
    const int16_t b[MLKEM_K * MLKEM_N],
    const int16_t b_cache[MLKEM_K * (MLKEM_N / 2)])
{
  unsigned i;
  int16_t t[MLKEM_N] ALIGN;

  /* Coefficient-wise bound of each basemul is 2q.
   * Since we are accumulating at most 4 times, the
   * overall bound is 8q < INT16_MAX. */
  basemul_avx2((__m256i *)r, (const __m256i *)a, (const __m256i *)b,
               (const __m256i *)qdata.vec, (const __m256i *)b_cache);
  for (i = 1; i < MLKEM_K; i++)
  {
    basemul_avx2((__m256i *)t, (const __m256i *)&a[i * MLKEM_N],
                 (const __m256i *)&b[i * MLKEM_N], (const __m256i *)qdata.vec,
                 (const __m256i *)&b_cache[i * (MLKEM_N / 2)]);
    poly_add_avx2(r, r, t);
  }
}

#else /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */

/* Dummy constant to keep compiler happy despite empty CU */

#define empty_cu_avx2_basemul MLKEM_NAMESPACE(empty_cu_avx2_basemul)
int empty_cu_avx2_basemul;

#endif /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */
