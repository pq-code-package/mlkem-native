/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_NATIVE_RISCV64_META_H
#define MLK_NATIVE_RISCV64_META_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLK_ARITH_BACKEND_RISCV64

/* Set of primitives that this backend replaces */
#define MLK_USE_NATIVE_NTT
#define MLK_USE_NATIVE_INTT
#define MLK_USE_NATIVE_POLY_TOMONT
#define MLK_USE_NATIVE_REJ_UNIFORM
#define MLK_USE_NATIVE_POLY_REDUCE
#define MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE
#define MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED

#include "../../common.h"

#if !defined(__ASSEMBLER__)

#include "../api.h"
#include "src/arith_native_riscv64.h"

static MLK_INLINE int mlk_ntt_native(int16_t data[MLKEM_N])
{
  mlk_rv64v_poly_ntt(data);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_intt_native(int16_t data[MLKEM_N])
{
  mlk_rv64v_poly_invntt_tomont(data);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_poly_tomont_native(int16_t data[MLKEM_N])
{
  mlk_rv64v_poly_tomont(data);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_rej_uniform_native(int16_t *r, unsigned len,
                                             const uint8_t *buf,
                                             unsigned buflen)
{
  return mlk_rv64v_rej_uniform(r, len, buf, buflen);
}

static MLK_INLINE int mlk_poly_reduce_native(int16_t data[MLKEM_N])
{
  mlk_rv64v_poly_reduce(data);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_poly_mulcache_compute_native(
    int16_t x[MLKEM_N / 2], const int16_t y[MLKEM_N])
{
  (void)x; /*	not using the cache atm  */
  (void)y;
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_polyvec_basemul_acc_montgomery_cached_k2_native(
    int16_t r[MLKEM_N], const int16_t a[2 * MLKEM_N],
    const int16_t b[2 * MLKEM_N], const int16_t b_cache[2 * (MLKEM_N / 2)])
{
  (void)b_cache;
  mlk_rv64v_poly_basemul_mont_add_k2(r, a, b);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_polyvec_basemul_acc_montgomery_cached_k3_native(
    int16_t r[MLKEM_N], const int16_t a[3 * MLKEM_N],
    const int16_t b[3 * MLKEM_N], const int16_t b_cache[3 * (MLKEM_N / 2)])
{
  (void)b_cache;
  mlk_rv64v_poly_basemul_mont_add_k3(r, a, b);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_polyvec_basemul_acc_montgomery_cached_k4_native(
    int16_t r[MLKEM_N], const int16_t a[4 * MLKEM_N],
    const int16_t b[4 * MLKEM_N], const int16_t b_cache[4 * (MLKEM_N / 2)])
{
  (void)b_cache;
  mlk_rv64v_poly_basemul_mont_add_k4(r, a, b);
  return MLK_NATIVE_FUNC_SUCCESS;
}

#endif /* !__ASSEMBLER__ */

#endif /* !MLK_NATIVE_RISCV64_META_H */
