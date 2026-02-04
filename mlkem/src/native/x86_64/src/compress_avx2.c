/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [REF_AVX2]
 *   CRYSTALS-Kyber optimized AVX2 implementation
 *   Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/kyber/tree/main/avx2
 */

/*
 * This file is derived from the public domain
 * AVX2 Kyber implementation @[REF_AVX2].
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include <immintrin.h>
#include "arith_native_x86_64.h"
#include "consts.h"

/* check-magic: 20159 == round(2^26/MLKEM_Q) */
#define MLK_AVX2_V 20159

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || (MLKEM_K == 2 || MLKEM_K == 3)
void mlk_poly_compress_d4_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4],
                               const int16_t *MLK_RESTRICT a)
{
  unsigned int i;
  __m256i f0, f1, f2, f3;
  const __m256i v = _mm256_set1_epi16(MLK_AVX2_V);
  const __m256i shift1 = _mm256_set1_epi16(1 << 9);
  const __m256i mask = _mm256_set1_epi16(15);
  const __m256i shift2 = _mm256_set1_epi16((16 << 8) + 1);
  const __m256i permdidx = _mm256_set_epi32(7, 3, 6, 2, 5, 1, 4, 0);

  for (i = 0; i < MLKEM_N / 64; i++)
  {
    f0 = _mm256_load_si256((__m256i *)&a[64 * i + 16 * 0]);
    f1 = _mm256_load_si256((__m256i *)&a[64 * i + 16 * 1]);
    f2 = _mm256_load_si256((__m256i *)&a[64 * i + 16 * 2]);
    f3 = _mm256_load_si256((__m256i *)&a[64 * i + 16 * 3]);
    f0 = _mm256_mulhi_epi16(f0, v);
    f1 = _mm256_mulhi_epi16(f1, v);
    f2 = _mm256_mulhi_epi16(f2, v);
    f3 = _mm256_mulhi_epi16(f3, v);
    f0 = _mm256_mulhrs_epi16(f0, shift1);
    f1 = _mm256_mulhrs_epi16(f1, shift1);
    f2 = _mm256_mulhrs_epi16(f2, shift1);
    f3 = _mm256_mulhrs_epi16(f3, shift1);
    f0 = _mm256_and_si256(f0, mask);
    f1 = _mm256_and_si256(f1, mask);
    f2 = _mm256_and_si256(f2, mask);
    f3 = _mm256_and_si256(f3, mask);
    f0 = _mm256_packus_epi16(f0, f1);
    f2 = _mm256_packus_epi16(f2, f3);
    f0 = _mm256_maddubs_epi16(f0, shift2);
    f2 = _mm256_maddubs_epi16(f2, shift2);
    f0 = _mm256_packus_epi16(f0, f2);
    f0 = _mm256_permutevar8x32_epi32(f0, permdidx);
    _mm256_storeu_si256((__m256i *)&r[32 * i], f0);
  }
}

/* mlk_poly_decompress_d4_avx2 is now in poly_decompress_d4.S */

void mlk_poly_compress_d10_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10],
                                const int16_t *MLK_RESTRICT a)
{
  unsigned int i;
  __m256i f0, f1, f2;
  __m128i t0, t1;
  const __m256i v = _mm256_set1_epi16(MLK_AVX2_V);
  const __m256i v8 = _mm256_slli_epi16(v, 3);
  const __m256i off = _mm256_set1_epi16(15);
  const __m256i shift1 = _mm256_set1_epi16(1 << 12);
  const __m256i mask = _mm256_set1_epi16(1023);
  const __m256i shift2 =
      _mm256_set1_epi64x((1024LL << 48) + (1LL << 32) + (1024 << 16) + 1);
  const __m256i sllvdidx = _mm256_set1_epi64x(12);
  const __m256i shufbidx =
      _mm256_set_epi8(8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1, 12, 11, 10, 9,
                      -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0);

  for (i = 0; i < MLKEM_N / 16; i++)
  {
    f0 = _mm256_load_si256((__m256i *)&a[16 * i]);
    f1 = _mm256_mullo_epi16(f0, v8);
    f2 = _mm256_add_epi16(f0, off);
    f0 = _mm256_slli_epi16(f0, 3);
    f0 = _mm256_mulhi_epi16(f0, v);
    f2 = _mm256_sub_epi16(f1, f2);
    f1 = _mm256_andnot_si256(f1, f2);
    f1 = _mm256_srli_epi16(f1, 15);
    f0 = _mm256_sub_epi16(f0, f1);
    f0 = _mm256_mulhrs_epi16(f0, shift1);
    f0 = _mm256_and_si256(f0, mask);
    f0 = _mm256_madd_epi16(f0, shift2);
    f0 = _mm256_sllv_epi32(f0, sllvdidx);
    f0 = _mm256_srli_epi64(f0, 12);
    f0 = _mm256_shuffle_epi8(f0, shufbidx);
    t0 = _mm256_castsi256_si128(f0);
    t1 = _mm256_extracti128_si256(f0, 1);
    t0 = _mm_blend_epi16(t0, t1, 0xE0);
    _mm_storeu_si128((__m128i *)&r[20 * i + 0], t0);
    mlk_memcpy(&r[20 * i + 16], &t1, 4);
  }
}

/* mlk_poly_decompress_d10_avx2 is now in poly_decompress_d10.S */
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == 3 */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4
void mlk_poly_compress_d5_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5],
                               const int16_t *MLK_RESTRICT a)
{
  unsigned int i;
  __m256i f0, f1;
  __m128i t0, t1;
  const __m256i v = _mm256_set1_epi16(MLK_AVX2_V);
  const __m256i shift1 = _mm256_set1_epi16(1 << 10);
  const __m256i mask = _mm256_set1_epi16(31);
  const __m256i shift2 = _mm256_set1_epi16((32 << 8) + 1);
  const __m256i shift3 = _mm256_set1_epi32((1024 << 16) + 1);
  const __m256i sllvdidx = _mm256_set1_epi64x(12);
  const __m256i shufbidx =
      _mm256_set_epi8(8, -1, -1, -1, -1, -1, 4, 3, 2, 1, 0, -1, 12, 11, 10, 9,
                      -1, 12, 11, 10, 9, 8, -1, -1, -1, -1, -1, 4, 3, 2, 1, 0);

  for (i = 0; i < MLKEM_N / 32; i++)
  {
    f0 = _mm256_load_si256((__m256i *)&a[32 * i + 16 * 0]);
    f1 = _mm256_load_si256((__m256i *)&a[32 * i + 16 * 1]);
    f0 = _mm256_mulhi_epi16(f0, v);
    f1 = _mm256_mulhi_epi16(f1, v);
    f0 = _mm256_mulhrs_epi16(f0, shift1);
    f1 = _mm256_mulhrs_epi16(f1, shift1);
    f0 = _mm256_and_si256(f0, mask);
    f1 = _mm256_and_si256(f1, mask);
    f0 = _mm256_packus_epi16(f0, f1);
    f0 = _mm256_maddubs_epi16(
        f0, shift2); /* a0 a1 a2 a3 b0 b1 b2 b3 a4 a5 a6 a7 b4 b5 b6 b7 */
    f0 = _mm256_madd_epi16(f0, shift3); /* a0 a1 b0 b1 a2 a3 b2 b3 */
    f0 = _mm256_sllv_epi32(f0, sllvdidx);
    f0 = _mm256_srlv_epi64(f0, sllvdidx);
    f0 = _mm256_shuffle_epi8(f0, shufbidx);
    t0 = _mm256_castsi256_si128(f0);
    t1 = _mm256_extracti128_si256(f0, 1);
    t0 = _mm_blendv_epi8(t0, t1, _mm256_castsi256_si128(shufbidx));
    _mm_storeu_si128((__m128i *)&r[20 * i + 0], t0);
    mlk_memcpy(&r[20 * i + 16], &t1, 4);
  }
}

/* mlk_poly_decompress_d5_avx2 is now in poly_decompress_d5.S */

void mlk_poly_compress_d11_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11],
                                const int16_t *MLK_RESTRICT a)
{
  unsigned int i;
  __m256i f0, f1, f2;
  __m128i t0, t1;
  const __m256i v = _mm256_set1_epi16(MLK_AVX2_V);
  const __m256i v8 = _mm256_slli_epi16(v, 3);
  const __m256i off = _mm256_set1_epi16(36);
  const __m256i shift1 = _mm256_set1_epi16(1 << 13);
  const __m256i mask = _mm256_set1_epi16(2047);
  const __m256i shift2 =
      _mm256_set1_epi64x((2048LL << 48) + (1LL << 32) + (2048 << 16) + 1);
  const __m256i sllvdidx = _mm256_set1_epi64x(10);
  const __m256i srlvqidx = _mm256_set_epi64x(30, 10, 30, 10);
  const __m256i shufbidx =
      _mm256_set_epi8(4, 3, 2, 1, 0, 0, -1, -1, -1, -1, 10, 9, 8, 7, 6, 5, -1,
                      -1, -1, -1, -1, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);

  for (i = 0; i < (MLKEM_N / 16) - 1; i++)
  {
    f0 = _mm256_load_si256((__m256i *)&a[16 * i]);
    f1 = _mm256_mullo_epi16(f0, v8);
    f2 = _mm256_add_epi16(f0, off);
    f0 = _mm256_slli_epi16(f0, 3);
    f0 = _mm256_mulhi_epi16(f0, v);
    f2 = _mm256_sub_epi16(f1, f2);
    f1 = _mm256_andnot_si256(f1, f2);
    f1 = _mm256_srli_epi16(f1, 15);
    f0 = _mm256_sub_epi16(f0, f1);
    f0 = _mm256_mulhrs_epi16(f0, shift1);
    f0 = _mm256_and_si256(f0, mask);
    f0 = _mm256_madd_epi16(f0, shift2);
    f0 = _mm256_sllv_epi32(f0, sllvdidx);
    f1 = _mm256_bsrli_epi128(f0, 8);
    f0 = _mm256_srlv_epi64(f0, srlvqidx);
    f1 = _mm256_slli_epi64(f1, 34);
    f0 = _mm256_add_epi64(f0, f1);
    f0 = _mm256_shuffle_epi8(f0, shufbidx);
    t0 = _mm256_castsi256_si128(f0);
    t1 = _mm256_extracti128_si256(f0, 1);
    t0 = _mm_blendv_epi8(t0, t1, _mm256_castsi256_si128(shufbidx));
    _mm_storeu_si128((__m128i *)&r[22 * i + 0], t0);
    _mm_storel_epi64((__m128i *)&r[22 * i + 16], t1);
  }

  f0 = _mm256_load_si256((__m256i *)&a[16 * i]);
  f1 = _mm256_mullo_epi16(f0, v8);
  f2 = _mm256_add_epi16(f0, off);
  f0 = _mm256_slli_epi16(f0, 3);
  f0 = _mm256_mulhi_epi16(f0, v);
  f2 = _mm256_sub_epi16(f1, f2);
  f1 = _mm256_andnot_si256(f1, f2);
  f1 = _mm256_srli_epi16(f1, 15);
  f0 = _mm256_sub_epi16(f0, f1);
  f0 = _mm256_mulhrs_epi16(f0, shift1);
  f0 = _mm256_and_si256(f0, mask);
  f0 = _mm256_madd_epi16(f0, shift2);
  f0 = _mm256_sllv_epi32(f0, sllvdidx);
  f1 = _mm256_bsrli_epi128(f0, 8);
  f0 = _mm256_srlv_epi64(f0, srlvqidx);
  f1 = _mm256_slli_epi64(f1, 34);
  f0 = _mm256_add_epi64(f0, f1);
  f0 = _mm256_shuffle_epi8(f0, shufbidx);
  t0 = _mm256_castsi256_si128(f0);
  t1 = _mm256_extracti128_si256(f0, 1);
  t0 = _mm_blendv_epi8(t0, t1, _mm256_castsi256_si128(shufbidx));
  _mm_storeu_si128((__m128i *)&r[22 * i + 0], t0);
  /* Handle store in last iteration especially to avoid overflow */
  mlk_memcpy(&r[22 * i + 16], &t1, 6);
}

/* mlk_poly_decompress_d11_avx2 is now in poly_decompress_d11.S */

#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4 */

#else /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
       */

MLK_EMPTY_CU(avx2_poly_compress)

#endif /* !(MLK_ARITH_BACKEND_X86_64_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED) */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef MLK_AVX2_V
