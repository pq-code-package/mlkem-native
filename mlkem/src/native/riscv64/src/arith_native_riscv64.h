/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_RISCV64_SRC_ARITH_NATIVE_RISCV64_H
#define MLK_NATIVE_RISCV64_SRC_ARITH_NATIVE_RISCV64_H

#include "../../../common.h"

#define mlk_rv64v_ntt256_zetas MLK_NAMESPACE(rv64v_ntt256_zetas)
#define mlk_rv64v_ntt128_zetas MLK_NAMESPACE(rv64v_ntt128_zetas)
#define mlk_rv64v_intt256_zetas MLK_NAMESPACE(rv64v_intt256_zetas)
#define mlk_rv64v_intt128_zetas MLK_NAMESPACE(rv64v_intt128_zetas)
#define mlk_rv64v_ntt256_perms MLK_NAMESPACE(rv64v_ntt256_perms)
#define mlk_rv64v_ntt128_perms MLK_NAMESPACE(rv64v_ntt128_perms)
#define mlk_rv64v_mulcache_zetas MLK_NAMESPACE(rv64v_mulcache_zetas)

MLK_INTERNAL_DATA_DECLARATION const int16_t mlk_rv64v_ntt256_zetas[800];
MLK_INTERNAL_DATA_DECLARATION const int16_t mlk_rv64v_ntt128_zetas[576];
MLK_INTERNAL_DATA_DECLARATION const int16_t mlk_rv64v_intt256_zetas[800];
MLK_INTERNAL_DATA_DECLARATION const int16_t mlk_rv64v_intt128_zetas[576];
MLK_INTERNAL_DATA_DECLARATION const uint16_t mlk_rv64v_ntt256_perms[160];
MLK_INTERNAL_DATA_DECLARATION const uint16_t mlk_rv64v_ntt128_perms[96];
MLK_INTERNAL_DATA_DECLARATION const int16_t mlk_rv64v_mulcache_zetas[256];

#define mlk_ntt_vlen256_riscv64_asm MLK_NAMESPACE(ntt_vlen256_riscv64_asm)
void mlk_ntt_vlen256_riscv64_asm(int16_t p[256], const int16_t zetas[800],
                                 const uint16_t perms[160])
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/mlkem_ntt_vlen256_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(p, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(p, 0, MLKEM_N, MLKEM_Q))
  requires(zetas == mlk_rv64v_ntt256_zetas)
  requires(perms == mlk_rv64v_ntt256_perms)
  assigns(memory_slice(p, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(p, 0, MLKEM_N, 8 * MLKEM_Q))
);

#define mlk_ntt_vlen128_riscv64_asm MLK_NAMESPACE(ntt_vlen128_riscv64_asm)
void mlk_ntt_vlen128_riscv64_asm(int16_t p[256], const int16_t zetas[576],
                                 const uint16_t perms[96])
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/mlkem_ntt_vlen128_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(p, sizeof(int16_t) * MLKEM_N))
  requires(array_abs_bound(p, 0, MLKEM_N, MLKEM_Q))
  requires(zetas == mlk_rv64v_ntt128_zetas)
  requires(perms == mlk_rv64v_ntt128_perms)
  assigns(memory_slice(p, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(p, 0, MLKEM_N, 8 * MLKEM_Q))
);

#if !defined(MLK_CONFIG_NO_ENCAPS_API) || !defined(MLK_CONFIG_NO_DECAPS_API)
#define mlk_intt_vlen256_riscv64_asm MLK_NAMESPACE(intt_vlen256_riscv64_asm)
void mlk_intt_vlen256_riscv64_asm(int16_t p[256], const int16_t zetas[800],
                                  const uint16_t perms[160])
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/mlkem_intt_vlen256_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(p, sizeof(int16_t) * MLKEM_N))
  requires(zetas == mlk_rv64v_intt256_zetas)
  requires(perms == mlk_rv64v_ntt256_perms)
  assigns(memory_slice(p, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(p, 0, MLKEM_N, 8 * MLKEM_Q))
);

#define mlk_intt_vlen128_riscv64_asm MLK_NAMESPACE(intt_vlen128_riscv64_asm)
void mlk_intt_vlen128_riscv64_asm(int16_t p[256], const int16_t zetas[576],
                                  const uint16_t perms[96])
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/mlkem_intt_vlen128_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(p, sizeof(int16_t) * MLKEM_N))
  requires(zetas == mlk_rv64v_intt128_zetas)
  requires(perms == mlk_rv64v_ntt128_perms)
  assigns(memory_slice(p, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(p, 0, MLKEM_N, 8 * MLKEM_Q))
);
#endif /* !MLK_CONFIG_NO_ENCAPS_API || !MLK_CONFIG_NO_DECAPS_API */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2
#define mlk_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm \
  MLK_NAMESPACE(polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm)
void mlk_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm(
    int16_t r[256], const int16_t a[512], const int16_t b[512],
    const int16_t b_cache[256])
/* This must be kept in sync with the HOL-Light specification in
 * proofs/hol_light/riscv64/proofs/mlkem_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm.ml.
 */
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(memory_no_alias(a, sizeof(int16_t) * 2 * MLKEM_N))
  requires(memory_no_alias(b, sizeof(int16_t) * 2 * MLKEM_N))
  requires(memory_no_alias(b_cache, sizeof(int16_t) * 2 * (MLKEM_N / 2)))
  requires(array_bound(a, 0, 2 * MLKEM_N, 0, MLKEM_UINT12_LIMIT))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
);
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 3
#define mlk_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm \
  MLK_NAMESPACE(polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm)
void mlk_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm(
    int16_t r[256], const int16_t a[768], const int16_t b[768],
    const int16_t b_cache[384])
/* This must be kept in sync with the HOL-Light specification in
 * proofs/hol_light/riscv64/proofs/mlkem_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm.ml.
 */
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(memory_no_alias(a, sizeof(int16_t) * 3 * MLKEM_N))
  requires(memory_no_alias(b, sizeof(int16_t) * 3 * MLKEM_N))
  requires(memory_no_alias(b_cache, sizeof(int16_t) * 3 * (MLKEM_N / 2)))
  requires(array_bound(a, 0, 3 * MLKEM_N, 0, MLKEM_UINT12_LIMIT))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
);
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 3 */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4
#define mlk_polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm \
  MLK_NAMESPACE(polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm)
void mlk_polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm(
    int16_t r[256], const int16_t a[1024], const int16_t b[1024],
    const int16_t b_cache[512])
/* This must be kept in sync with the HOL-Light specification in
 * proofs/hol_light/riscv64/proofs/mlkem_polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm.ml.
 */
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(memory_no_alias(a, sizeof(int16_t) * 4 * MLKEM_N))
  requires(memory_no_alias(b, sizeof(int16_t) * 4 * MLKEM_N))
  requires(memory_no_alias(b_cache, sizeof(int16_t) * 4 * (MLKEM_N / 2)))
  requires(array_bound(a, 0, 4 * MLKEM_N, 0, MLKEM_UINT12_LIMIT))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
);
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4 */

#define mlk_poly_mulcache_compute_riscv64_asm \
  MLK_NAMESPACE(poly_mulcache_compute_riscv64_asm)
void mlk_poly_mulcache_compute_riscv64_asm(int16_t cache[128],
                                           const int16_t p[256],
                                           const int16_t zetas[256])
/* This must be kept in sync with the HOL-Light specification in
 * proofs/hol_light/riscv64/proofs/mlkem_poly_mulcache_compute_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(cache, sizeof(int16_t) * (MLKEM_N / 2)))
  requires(memory_no_alias(p, sizeof(int16_t) * MLKEM_N))
  requires(zetas == mlk_rv64v_mulcache_zetas)
  assigns(memory_slice(cache, sizeof(int16_t) * (MLKEM_N / 2)))
  ensures(array_abs_bound(cache, 0, MLKEM_N / 2, MLKEM_Q))
);

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
#define mlk_poly_tomont_riscv64_asm MLK_NAMESPACE(poly_tomont_riscv64_asm)
void mlk_poly_tomont_riscv64_asm(int16_t p[256])
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/mlkem_poly_tomont_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(p, sizeof(int16_t) * MLKEM_N))
  assigns(memory_slice(p, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(p, 0, MLKEM_N, MLKEM_Q))
);
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */

#define mlk_poly_reduce_riscv64_asm MLK_NAMESPACE(poly_reduce_riscv64_asm)
void mlk_poly_reduce_riscv64_asm(int16_t p[256])
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/mlkem_poly_reduce_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(p, sizeof(int16_t) * MLKEM_N))
  assigns(memory_slice(p, sizeof(int16_t) * MLKEM_N))
  ensures(array_bound(p, 0, MLKEM_N, 0, MLKEM_Q))
);

#define mlk_rv64v_poly_add MLK_NAMESPACE(poly_add_riscv64)
void mlk_rv64v_poly_add(int16_t *r, const int16_t *a, const int16_t *b);

#define mlk_rv64v_poly_sub MLK_NAMESPACE(poly_sub_riscv64)
void mlk_rv64v_poly_sub(int16_t *r, const int16_t *a, const int16_t *b);

#define mlk_rej_uniform_riscv64_asm MLK_NAMESPACE(rej_uniform_riscv64_asm)
MLK_MUST_CHECK_RETURN_VALUE
uint64_t mlk_rej_uniform_riscv64_asm(int16_t *r, uint64_t len,
                                     const uint8_t *buf, uint64_t buflen)
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/mlkem_rej_uniform_riscv64_asm.ml */
__contract__(
  requires(len <= 4096 && buflen <= 4096 && buflen % 12 == 0)
  requires(memory_no_alias(buf, buflen))
  requires(memory_no_alias(r, sizeof(int16_t) * len))
  assigns(memory_slice(r, sizeof(int16_t) * len))
  ensures(return_value <= len)
  ensures(array_bound(r, 0, (unsigned) return_value, 0, MLKEM_Q))
);

#endif /* !MLK_NATIVE_RISCV64_SRC_ARITH_NATIVE_RISCV64_H */
