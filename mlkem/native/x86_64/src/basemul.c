/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "../../../common.h"

#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)

#include <string.h>

#include "arith_native_x86_64.h"
#include "consts.h"

ALWAYS_INLINE
static INLINE int16_t cast_uint16_to_int16(uint16_t x) { return (int16_t)x; }

ALWAYS_INLINE
static INLINE int16_t montgomery_reduce(int32_t a)
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

  r = r >> 16;
  return (int16_t)r;
}

static inline void m256i_mulal(__m256i *acc0, __m256i *acc1,
			       __m256i x, __m256i y)
{
    __m256i lo = _mm256_mullo_epi16(x, y);
    __m256i hi = _mm256_mulhi_epi16(x, y);
    __m256i t0 = _mm256_unpacklo_epi16(lo, hi);
    __m256i t1 = _mm256_unpackhi_epi16(lo, hi);
    *acc0 = _mm256_add_epi32(*acc0, t0);
    *acc1 = _mm256_add_epi32(*acc1, t1);
}


static inline void m256i_mulsl(__m256i *acc0, __m256i *acc1,
			       __m256i x, __m256i y)
{
    __m256i lo = _mm256_mullo_epi16(x, y);
    __m256i hi = _mm256_mulhi_epi16(x, y);
    __m256i t0 = _mm256_unpacklo_epi16(lo, hi);
    __m256i t1 = _mm256_unpackhi_epi16(lo, hi);
    *acc0 = _mm256_sub_epi32(*acc0, t0);
    *acc1 = _mm256_sub_epi32(*acc1, t1);
}

void polyvec_basemul_acc_montgomery_cached_avx2(
    int16_t r[RESTRICT MLKEM_N], const int16_t a[RESTRICT(MLKEM_K * MLKEM_N)],
    const int16_t b[RESTRICT(MLKEM_K * MLKEM_N)],
    const int16_t b_cache[RESTRICT(MLKEM_K * (MLKEM_N / 2))])
{
  unsigned i, j, k;
  for (i = 0; i < 4; i++)
  {
      __m256i acc0_lo, acc0_hi, acc1_lo, acc1_hi, r0, r1;
      for (k = 0; k < MLKEM_K; k++)
      {
	  __m256i a0, b0, a1, b1, c0, d0, c1, d1, d0z, d1z;
        a0 = _mm256_load_si256((__m256i*)&a[MLKEM_N * k + 64 * i + 0]);
        b0 = _mm256_load_si256((__m256i*)&a[MLKEM_N * k + 64 * i + 16]);
	a1 = _mm256_load_si256((__m256i*)&a[MLKEM_N * k + 64 * i + 32]);
	b1 = _mm256_load_si256((__m256i*)&a[MLKEM_N * k + 64 * i + 48]);

        c0 = _mm256_load_si256((__m256i*)&b[MLKEM_N * k + 64 * i + 0]);
        d0 = _mm256_load_si256((__m256i*)&b[MLKEM_N * k + 64 * i + 16]);
        c1 = _mm256_load_si256((__m256i*)&b[MLKEM_N * k + 64 * i + 32]);
        d1 = _mm256_load_si256((__m256i*)&b[MLKEM_N * k + 64 * i + 48]);

        d0z = _mm256_load_si256((__m256i*)&b_cache[(MLKEM_N / 2) * k + 32 * i + 0]);
        d1z = _mm256_load_si256((__m256i*)&b_cache[(MLKEM_N / 2) * k + 32 * i + 16]);

	m256i_mulal(&acc0_lo, &acc0_hi, a0, c0);
	m256i_mulal(&acc0_lo, &acc0_hi, b0, d0z);
	m256i_mulal(&acc0_lo, &acc0_hi, a0, d0);
	m256i_mulal(&acc0_lo, &acc0_hi, b0, c0);

	m256i_mulal(&acc1_lo, &acc1_hi, a1, c1);
	m256i_mulsl(&acc1_lo, &acc1_hi, b1, d1z);
	m256i_mulal(&acc1_lo, &acc1_hi, a1, d1);
	m256i_mulal(&acc1_lo, &acc1_hi, b1, c1);
      }

      r0 = m256i_montgomery_reduce(acc0, acc1);
      r1 = m256i_montgomery_reduce(acc0, acc1);
      _mm256_store_si256((__m256i*)&r[64 * i + 0], r0);
      _mm256_store_si256((__m256i*)&r[64 * i + 32], r1);
  }
}

/* void polyvec_basemul_acc_montgomery_cached_avx2( */
/*     int16_t r[RESTRICT MLKEM_N], const int16_t a[RESTRICT(MLKEM_K * MLKEM_N)], */
/*     const int16_t b[RESTRICT(MLKEM_K * MLKEM_N)], */
/*     const int16_t b_cache[RESTRICT(MLKEM_K * (MLKEM_N / 2))]) */
/* { */
/*   unsigned i, j, k; */
/*   for (i = 0; i < 4; i++) */
/*   { */
/*     for (j = 0; j < 16; j++) */
/*     { */
/*       int32_t l0 = 0, h0 = 0, l1 = 0, h1 = 0; */
/*       for (k = 0; k < MLKEM_K; k++) */
/*       { */
/*         int16_t a0, b0, a1, b1, c0, d0, c1, d1, d0z, d1z; */
/*         a0 = a[MLKEM_N * k + 64 * i + 0 + j]; */
/*         b0 = a[MLKEM_N * k + 64 * i + 16 + j]; */
/*         a1 = a[MLKEM_N * k + 64 * i + 32 + j]; */
/*         b1 = a[MLKEM_N * k + 64 * i + 48 + j]; */

/*         c0 = b[MLKEM_N * k + 64 * i + 0 + j]; */
/*         d0 = b[MLKEM_N * k + 64 * i + 16 + j]; */
/*         c1 = b[MLKEM_N * k + 64 * i + 32 + j]; */
/*         d1 = b[MLKEM_N * k + 64 * i + 48 + j]; */

/*         d0z = b_cache[(MLKEM_N / 2) * k + 32 * i + 0 + j]; */
/*         d1z = b_cache[(MLKEM_N / 2) * k + 32 * i + 16 + j]; */

/*         l0 += (int32_t)a0 * c0; */
/*         l0 += (int32_t)b0 * d0z; */

/*         h0 += (int32_t)a0 * d0; */
/*         h0 += (int32_t)b0 * c0; */

/*         l1 += (int32_t)a1 * c1; */
/*         l1 -= (int32_t)b1 * d1z; */

/*         h1 += (int32_t)a1 * d1; */
/*         h1 += (int32_t)b1 * c1; */
/*       } */
/*       r[64 * i + 0 + j] = montgomery_reduce(l0); */
/*       r[64 * i + 16 + j] = montgomery_reduce(h0); */
/*       r[64 * i + 32 + j] = montgomery_reduce(l1); */
/*       r[64 * i + 48 + j] = montgomery_reduce(h1); */
/*     } */
/*   } */
/* } */

#else /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */

/* Dummy constant to keep compiler happy despite empty CU */

#define empty_cu_avx2_basemul MLKEM_NAMESPACE(empty_cu_avx2_basemul)
int empty_cu_avx2_basemul;

#endif /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */
