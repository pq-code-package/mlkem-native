/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Implementation from Kyber reference repository
 * https://github.com/pq-crystals/kyber/blob/main/avx2 */

#include "../../../common.h"

#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)

#include <immintrin.h>
#include <stdint.h>
#include <string.h>
#include "arith_native_x86_64.h"
#include "consts.h"

#if (MLKEM_POLYVECCOMPRESSEDBYTES_DU == (MLKEM_K * 320))
static void poly_compress10(uint8_t r[320], const __m256i *RESTRICT a)
{
  unsigned int i;
  __m256i f0, f1, f2;
  __m128i t0, t1;
  const __m256i v =
      _mm256_load_si256(&qdata.vec[AVX2_BACKEND_DATA_OFFSET_16XV / 16]);
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
    f0 = _mm256_load_si256(&a[i]);
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
    memcpy(&r[20 * i + 16], &t1, 4);
  }
}

static void poly_decompress10(__m256i *RESTRICT r, const uint8_t a[320 + 12])
{
  unsigned int i;
  __m256i f;
  const __m256i q = _mm256_set1_epi32((MLKEM_Q << 16) + 4 * MLKEM_Q);
  const __m256i shufbidx =
      _mm256_set_epi8(11, 10, 10, 9, 9, 8, 8, 7, 6, 5, 5, 4, 4, 3, 3, 2, 9, 8,
                      8, 7, 7, 6, 6, 5, 4, 3, 3, 2, 2, 1, 1, 0);
  const __m256i sllvdidx = _mm256_set1_epi64x(4);
  const __m256i mask = _mm256_set1_epi32((32736 << 16) + 8184);

  for (i = 0; i < MLKEM_N / 16; i++)
  {
    f = _mm256_loadu_si256((__m256i *)&a[20 * i]);
    f = _mm256_permute4x64_epi64(f, 0x94);
    f = _mm256_shuffle_epi8(f, shufbidx);
    f = _mm256_sllv_epi32(f, sllvdidx);
    f = _mm256_srli_epi16(f, 1);
    f = _mm256_and_si256(f, mask);
    f = _mm256_mulhrs_epi16(f, q);
    _mm256_store_si256(&r[i], f);
  }
}

#elif (MLKEM_POLYVECCOMPRESSEDBYTES_DU == (MLKEM_K * 352))
static void poly_compress11(uint8_t r[352 + 2], const __m256i *RESTRICT a)
{
  unsigned int i;
  __m256i f0, f1, f2;
  __m128i t0, t1;
  const __m256i v =
      _mm256_load_si256(&qdata.vec[AVX2_BACKEND_DATA_OFFSET_16XV / 16]);
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

  for (i = 0; i < MLKEM_N / 16; i++)
  {
    f0 = _mm256_load_si256(&a[i]);
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
}

static void poly_decompress11(__m256i *RESTRICT r, const uint8_t a[352 + 10])
{
  unsigned int i;
  __m256i f;
  const __m256i q =
      _mm256_load_si256(&qdata.vec[AVX2_BACKEND_DATA_OFFSET_16XQ / 16]);
  const __m256i shufbidx =
      _mm256_set_epi8(13, 12, 12, 11, 10, 9, 9, 8, 8, 7, 6, 5, 5, 4, 4, 3, 10,
                      9, 9, 8, 7, 6, 6, 5, 5, 4, 3, 2, 2, 1, 1, 0);
  const __m256i srlvdidx = _mm256_set_epi32(0, 0, 1, 0, 0, 0, 1, 0);
  const __m256i srlvqidx = _mm256_set_epi64x(2, 0, 2, 0);
  const __m256i shift =
      _mm256_set_epi16(4, 32, 1, 8, 32, 1, 4, 32, 4, 32, 1, 8, 32, 1, 4, 32);
  const __m256i mask = _mm256_set1_epi16(32752);

  for (i = 0; i < MLKEM_N / 16; i++)
  {
    f = _mm256_loadu_si256((__m256i *)&a[22 * i]);
    f = _mm256_permute4x64_epi64(f, 0x94);
    f = _mm256_shuffle_epi8(f, shufbidx);
    f = _mm256_srlv_epi32(f, srlvdidx);
    f = _mm256_srlv_epi64(f, srlvqidx);
    f = _mm256_mullo_epi16(f, shift);
    f = _mm256_srli_epi16(f, 1);
    f = _mm256_and_si256(f, mask);
    f = _mm256_mulhrs_epi16(f, q);
    _mm256_store_si256(&r[i], f);
  }
}

#endif

/*************************************************
 * Name:        polyvec_compress
 *
 * Description: Compress and serialize vector of polynomials
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                            (needs space for MLKEM_POLYVECCOMPRESSEDBYTES)
 *              - polyvec *a: pointer to input vector of polynomials
 **************************************************/
void polyvec_compress_du_avx2(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES_DU],
                              const int16_t a[MLKEM_K * MLKEM_N])
{
  unsigned int i;
  /* TODO: can we eliminate the extra bytes?
   * pad input so we can always store full vectors */

#if (MLKEM_POLYVECCOMPRESSEDBYTES_DU == (MLKEM_K * 320))
  for (i = 0; i < MLKEM_K; i++)
    poly_compress10(&r[320 * i], (__m256i *)(a + i * MLKEM_N));
#elif (MLKEM_POLYVECCOMPRESSEDBYTES_DU == (MLKEM_K * 352))
  uint8_t rpadded[MLKEM_POLYVECCOMPRESSEDBYTES_DU + 2];
  for (i = 0; i < MLKEM_K; i++)
    poly_compress11(&rpadded[352 * i], (__m256i *)(a + i * MLKEM_N));
  memcpy(r, rpadded, MLKEM_POLYVECCOMPRESSEDBYTES_DU);
#endif
}

/*************************************************
 * Name:        polyvec_decompress
 *
 * Description: De-serialize and decompress vector of polynomials;
 *              approximate inverse of polyvec_compress
 *
 * Arguments:   - polyvec *r: pointer to output vector of polynomials
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYVECCOMPRESSEDBYTES_DU)
 **************************************************/
void polyvec_decompress_du_avx2(
    int16_t r[MLKEM_K * MLKEM_N],
    const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES_DU])
{
  unsigned int i;
  /* TODO: can we eliminate the extra bytes?
   * pad input so we can always load full vectors */

#if (MLKEM_POLYVECCOMPRESSEDBYTES_DU == (MLKEM_K * 320))
  uint8_t apadded[MLKEM_POLYVECCOMPRESSEDBYTES_DU + 12];
  memcpy(apadded, a, MLKEM_POLYVECCOMPRESSEDBYTES_DU);
  for (i = 0; i < MLKEM_K; i++)
    poly_decompress10((__m256i *)(r + i * MLKEM_N), &apadded[320 * i]);
#elif (MLKEM_POLYVECCOMPRESSEDBYTES_DU == (MLKEM_K * 352))
  uint8_t apadded[MLKEM_POLYVECCOMPRESSEDBYTES_DU + 10];
  memcpy(apadded, a, MLKEM_POLYVECCOMPRESSEDBYTES_DU);
  for (i = 0; i < MLKEM_K; i++)
    poly_decompress11((__m256i *)(r + i * MLKEM_N), &apadded[352 * i]);
#endif
}

#else /* MLKEM_USE_NATIVE_X86_64 && SYS_X86_64_AVX2 */

/* Dummy declaration for compilers disliking empty compilation units */
#define empty_cu_avx2_polyvec_compress \
  MLKEM_NAMESPACE(empty_cu_avx2_polyvec_compress)
int empty_cu_avx2_polyvec_compress;

#endif /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */
