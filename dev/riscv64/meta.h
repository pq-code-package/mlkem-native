/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_DEV_RISCV64_META_H
#define MLK_DEV_RISCV64_META_H

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
#if !defined(CBMC)
#include <riscv_vector.h>
#endif

#include "../api.h"
#include "src/arith_native_riscv64.h"

/* Returns the vector register length VLEN in bits.
 * CBMC proofs use the contract instead of the body. */
static MLK_INLINE int mlk_rv64v_vlen(void)
__contract__(
  ensures(return_value >= 0)
)
{
#if !defined(CBMC)
  return (int)(16 * __riscv_vsetvlmax_e16m1());
#else
  return 0;
#endif
}

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_ntt_native(int16_t data[MLKEM_N])
{
  /* VLEN = 128 and VLEN = 256 only for now */
  const int vlen = mlk_rv64v_vlen();
  if (vlen == 256)
  {
    mlk_ntt_vlen256_riscv64_asm(data, mlk_rv64v_ntt256_zetas,
                                mlk_rv64v_ntt256_perms);
    return MLK_NATIVE_FUNC_SUCCESS;
  }
  if (vlen == 128)
  {
    mlk_ntt_vlen128_riscv64_asm(data, mlk_rv64v_ntt128_zetas,
                                mlk_rv64v_ntt128_perms);
    return MLK_NATIVE_FUNC_SUCCESS;
  }
  return MLK_NATIVE_FUNC_FALLBACK;
}

#if !defined(MLK_CONFIG_NO_ENCAPS_API) || !defined(MLK_CONFIG_NO_DECAPS_API)
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_intt_native(int16_t data[MLKEM_N])
{
  /* VLEN = 128 and VLEN = 256 only for now */
  const int vlen = mlk_rv64v_vlen();
  if (vlen == 256)
  {
    mlk_intt_vlen256_riscv64_asm(data, mlk_rv64v_intt256_zetas,
                                 mlk_rv64v_ntt256_perms);
    return MLK_NATIVE_FUNC_SUCCESS;
  }
  if (vlen == 128)
  {
    mlk_intt_vlen128_riscv64_asm(data, mlk_rv64v_intt128_zetas,
                                 mlk_rv64v_ntt128_perms);
    return MLK_NATIVE_FUNC_SUCCESS;
  }
  return MLK_NATIVE_FUNC_FALLBACK;
}
#endif /* !MLK_CONFIG_NO_ENCAPS_API || !MLK_CONFIG_NO_DECAPS_API */

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_poly_tomont_native(int16_t data[MLKEM_N])
{
  mlk_poly_tomont_riscv64_asm(data);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_rej_uniform_native(int16_t *r, unsigned len,
                                             const uint8_t *buf,
                                             unsigned buflen)
{
  /* mlk_rej_uniform_riscv64_asm requires buflen to be a multiple of 12 */
  if (buflen % 12 != 0)
  {
    return MLK_NATIVE_FUNC_FALLBACK;
  }
  /* The cast from unsigned to signed integer is safe
   * because the return value is <= len, which we asssume
   * to be bound by 4096 and hence <= INT_MAX. */
  return (int)mlk_rej_uniform_riscv64_asm(r, len, buf, buflen);
}

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_poly_reduce_native(int16_t data[MLKEM_N])
{
  mlk_poly_reduce_riscv64_asm(data);
  return MLK_NATIVE_FUNC_SUCCESS;
}

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_poly_mulcache_compute_native(int16_t x[MLKEM_N / 2],
                                                       const int16_t y[MLKEM_N])
{
  mlk_poly_mulcache_compute_riscv64_asm(x, y, mlk_rv64v_mulcache_zetas);
  return MLK_NATIVE_FUNC_SUCCESS;
}

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_polyvec_basemul_acc_montgomery_cached_k2_native(
    int16_t r[MLKEM_N], const int16_t a[2 * MLKEM_N],
    const int16_t b[2 * MLKEM_N], const int16_t b_cache[2 * (MLKEM_N / 2)])
{
  mlk_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm(r, a, b, b_cache);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 3
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_polyvec_basemul_acc_montgomery_cached_k3_native(
    int16_t r[MLKEM_N], const int16_t a[3 * MLKEM_N],
    const int16_t b[3 * MLKEM_N], const int16_t b_cache[3 * (MLKEM_N / 2)])
{
  mlk_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm(r, a, b, b_cache);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 3 */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_polyvec_basemul_acc_montgomery_cached_k4_native(
    int16_t r[MLKEM_N], const int16_t a[4 * MLKEM_N],
    const int16_t b[4 * MLKEM_N], const int16_t b_cache[4 * (MLKEM_N / 2)])
{
  mlk_polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm(r, a, b, b_cache);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4 */

#endif /* !__ASSEMBLER__ */

#endif /* !MLK_DEV_RISCV64_META_H */
