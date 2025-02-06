/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_DEV_X86_64_SRC_ARITH_NATIVE_X86_64_H
#define MLK_DEV_X86_64_SRC_ARITH_NATIVE_X86_64_H

#include "../../../common.h"

#include <immintrin.h>
#include <stdint.h>
#include "consts.h"

#define REJ_UNIFORM_AVX_NBLOCKS 3 /* See MLKEM_GEN_MATRIX_NBLOCKS */
#define REJ_UNIFORM_AVX_BUFLEN \
  (3 * 168) /* REJ_UNIFORM_AVX_BUFLEN * SHAKE128_RATE */

#define rej_uniform_avx2 MLK_NAMESPACE(rej_uniform_avx2)
unsigned rej_uniform_avx2(int16_t *r, const uint8_t *buf);

#define rej_uniform_table MLK_NAMESPACE(rej_uniform_table)
extern const uint8_t rej_uniform_table[256][8];

#define ntt_avx2 MLK_NAMESPACE(ntt_avx2)
void ntt_avx2(__m256i *r, const __m256i *qdata);

#define invntt_avx2 MLK_NAMESPACE(invntt_avx2)
void invntt_avx2(__m256i *r, const __m256i *qdata);

#define nttpack_avx2 MLK_NAMESPACE(nttpack_avx2)
void nttpack_avx2(__m256i *r, const __m256i *qdata);

#define nttunpack_avx2 MLK_NAMESPACE(nttunpack_avx2)
void nttunpack_avx2(__m256i *r, const __m256i *qdata);

#define reduce_avx2 MLK_NAMESPACE(reduce_avx2)
void reduce_avx2(__m256i *r, const __m256i *qdata);

#define basemul_avx2 MLK_NAMESPACE(basemul_avx2)
void basemul_avx2(__m256i *r, const __m256i *a, const __m256i *b,
                  const __m256i *qdata);

#define polyvec_basemul_acc_montgomery_cached_avx2 \
  MLK_NAMESPACE(polyvec_basemul_acc_montgomery_cached_avx2)
void polyvec_basemul_acc_montgomery_cached_avx2(unsigned k, int16_t r[MLKEM_N],
                                                const int16_t *a,
                                                const int16_t *b,
                                                const int16_t *kb_cache);

#define ntttobytes_avx2 MLK_NAMESPACE(ntttobytes_avx2)
void ntttobytes_avx2(uint8_t *r, const __m256i *a, const __m256i *qdata);

#define nttfrombytes_avx2 MLK_NAMESPACE(nttfrombytes_avx2)
void nttfrombytes_avx2(__m256i *r, const uint8_t *a, const __m256i *qdata);

#define tomont_avx2 MLK_NAMESPACE(tomont_avx2)
void tomont_avx2(__m256i *r, const __m256i *qdata);

#define poly_compress_d4_avx2 MLK_NAMESPACE(poly_compress_d4_avx2)
void poly_compress_d4_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4],
                           const __m256i *MLK_RESTRICT a);
#define poly_decompress_d4_avx2 MLK_NAMESPACE(poly_decompress_d4_avx2)
void poly_decompress_d4_avx2(__m256i *MLK_RESTRICT r,
                             const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D4]);
#define poly_compress_d10_avx2 MLK_NAMESPACE(poly_compress10_avx2)
void poly_compress_d10_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10],
                            const __m256i *MLK_RESTRICT a);
#define poly_decompress_d10_avx2 MLK_NAMESPACE(poly_decompress10_avx2)
void poly_decompress_d10_avx2(__m256i *MLK_RESTRICT r,
                              const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D10]);
#define poly_compress_d5_avx2 MLK_NAMESPACE(poly_compress_d5_avx2)
void poly_compress_d5_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5],
                           const __m256i *MLK_RESTRICT a);
#define poly_decompress_d5_avx2 MLK_NAMESPACE(poly_decompress_d5_avx2)
void poly_decompress_d5_avx2(__m256i *MLK_RESTRICT r,
                             const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D5]);
#define poly_compress_d11_avx2 MLK_NAMESPACE(poly_compress11_avx2)
void poly_compress_d11_avx2(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11],
                            const __m256i *MLK_RESTRICT a);
#define poly_decompress_d11_avx2 MLK_NAMESPACE(poly_decompress11_avx2)
void poly_decompress_d11_avx2(__m256i *MLK_RESTRICT r,
                              const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D11]);

#endif /* MLK_DEV_X86_64_SRC_ARITH_NATIVE_X86_64_H */
