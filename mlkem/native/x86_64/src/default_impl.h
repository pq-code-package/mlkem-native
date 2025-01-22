/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* ML-KEM arithmetic native profile for clean assembly */

#ifdef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#error Only one MLKEM_ARITH assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_NATIVE_ARITH_PROFILE_IMPL_H

#include <string.h>

#include "../../../params.h"
#include "arith_native_x86_64.h"

#define MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER

#define MLKEM_USE_NATIVE_REJ_UNIFORM
#define MLKEM_USE_NATIVE_NTT
#define MLKEM_USE_NATIVE_INTT
#define MLKEM_USE_NATIVE_POLY_REDUCE
#define MLKEM_USE_NATIVE_POLY_TOMONT
#define MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#define MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#define MLKEM_USE_NATIVE_POLY_TOBYTES
#define MLKEM_USE_NATIVE_POLY_FROMBYTES

static INLINE void poly_permute_bitrev_to_custom(int16_t data[MLKEM_N])
{
  nttunpack_avx2((__m256i *)(data), qdata.vec);
}

static INLINE int rej_uniform_native(int16_t *r, unsigned int len,
                                     const uint8_t *buf, unsigned int buflen)
{
  /* AVX2 implementation assumes specific buffer lengths */
  if (len != MLKEM_N || buflen != REJ_UNIFORM_AVX_BUFLEN)
  {
    return -1;
  }

  return (int)rej_uniform_avx2(r, buf);
}

static INLINE void ntt_native(int16_t data[MLKEM_N])
{
  ntt_avx2((__m256i *)data, qdata.vec);
}

static INLINE void intt_native(int16_t data[MLKEM_N])
{
  invntt_avx2((__m256i *)data, qdata.vec);
}

static INLINE void poly_reduce_native(int16_t data[MLKEM_N])
{
  reduce_avx2((__m256i *)data, qdata.vec);
}

static INLINE void poly_tomont_native(int16_t data[MLKEM_N])
{
  tomont_avx2((__m256i *)data, qdata.vec);
}

static INLINE void poly_mulcache_compute_native(int16_t x[MLKEM_N / 2],
                                                const int16_t y[MLKEM_N])
{
  /* AVX2 backend does not use mulcache */
  ((void)y);
  ((void)x);
}

static INLINE void polyvec_basemul_acc_montgomery_cached_native(
    int16_t r[MLKEM_N], const int16_t a[MLKEM_K * MLKEM_N],
    const int16_t b[MLKEM_K * MLKEM_N],
    const int16_t b_cache[MLKEM_K * (MLKEM_N / 2)])
{
  polyvec_basemul_acc_montgomery_cached_avx2(r, a, b, b_cache);
}

static INLINE void poly_tobytes_native(uint8_t r[MLKEM_POLYBYTES],
                                       const int16_t a[MLKEM_N])
{
  ntttobytes_avx2(r, (const __m256i *)a, qdata.vec);
}

static INLINE void poly_frombytes_native(int16_t r[MLKEM_N],
                                         const uint8_t a[MLKEM_POLYBYTES])
{
  nttfrombytes_avx2((__m256i *)r, a, qdata.vec);
}

#endif /* MLKEM_NATIVE_ARITH_PROFILE_IMPL_H */
