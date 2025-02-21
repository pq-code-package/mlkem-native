/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_DEV_AARCH64_OPT_SRC_ARITH_NATIVE_AARCH64_H
#define MLK_DEV_AARCH64_OPT_SRC_ARITH_NATIVE_AARCH64_H

#include <stdint.h>
#include "../../../common.h"

#define mlk_aarch64_ntt_zetas_layer12345 \
  MLK_NAMESPACE(aarch64_ntt_zetas_layer12345)
#define mlk_aarch64_ntt_zetas_layer67 MLK_NAMESPACE(aarch64_ntt_zetas_layer67)
#define aarch64_invntt_zetas_layer12345 \
  MLK_NAMESPACE(aarch64_invntt_zetas_layer12345)
#define mlk_aarch64_invntt_zetas_layer67 \
  MLK_NAMESPACE(aarch64_invntt_zetas_layer67)
#define aarch64_zetas_mulcache_native \
  MLK_NAMESPACE(aarch64_zetas_mulcache_native)
#define aarch64_zetas_mulcache_twisted_native \
  MLK_NAMESPACE(aarch64_zetas_mulcache_twisted_native)
#define mlk_rej_uniform_table MLK_NAMESPACE(rej_uniform_table)

extern const int16_t mlk_aarch64_ntt_zetas_layer12345[];
extern const int16_t mlk_aarch64_ntt_zetas_layer67[];
extern const int16_t aarch64_invntt_zetas_layer12345[];
extern const int16_t mlk_aarch64_invntt_zetas_layer67[];
extern const int16_t aarch64_zetas_mulcache_native[];
extern const int16_t aarch64_zetas_mulcache_twisted_native[];
extern const uint8_t mlk_rej_uniform_table[];

#define mlk_ntt_asm_opt MLK_NAMESPACE(ntt_asm_opt)
void mlk_ntt_asm_opt(int16_t *, const int16_t *, const int16_t *);

#define mlk_intt_asm_opt MLK_NAMESPACE(intt_asm_opt)
void mlk_intt_asm_opt(int16_t *, const int16_t *, const int16_t *);

#define mlk_poly_reduce_asm_opt MLK_NAMESPACE(poly_reduce_asm_opt)
void mlk_poly_reduce_asm_opt(int16_t *);

#define mlk_poly_tomont_asm_opt MLK_NAMESPACE(poly_tomont_asm_opt)
void mlk_poly_tomont_asm_opt(int16_t *);

#define poly_mulcache_compute_asm_opt \
  MLK_NAMESPACE(poly_mulcache_compute_asm_opt)
void poly_mulcache_compute_asm_opt(int16_t *, const int16_t *, const int16_t *,
                                   const int16_t *);

#define mlk_poly_tobytes_asm_opt MLK_NAMESPACE(poly_tobytes_asm_opt)
void mlk_poly_tobytes_asm_opt(uint8_t *r, const int16_t *a);

#define polyvec_basemul_acc_montgomery_cached_asm_k2_opt \
  MLK_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k2_opt)
void polyvec_basemul_acc_montgomery_cached_asm_k2_opt(int16_t *r,
                                                      const int16_t *a,
                                                      const int16_t *b,
                                                      const int16_t *b_cache);

#define polyvec_basemul_acc_montgomery_cached_asm_k3_opt \
  MLK_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k3_opt)
void polyvec_basemul_acc_montgomery_cached_asm_k3_opt(int16_t *r,
                                                      const int16_t *a,
                                                      const int16_t *b,
                                                      const int16_t *b_cache);

#define polyvec_basemul_acc_montgomery_cached_asm_k4_opt \
  MLK_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k4_opt)
void polyvec_basemul_acc_montgomery_cached_asm_k4_opt(int16_t *r,
                                                      const int16_t *a,
                                                      const int16_t *b,
                                                      const int16_t *b_cache);

#define mlk_rej_uniform_asm_clean MLK_NAMESPACE(rej_uniform_asm_clean)
unsigned mlk_rej_uniform_asm_clean(int16_t *r, const uint8_t *buf,
                                   unsigned buflen, const uint8_t *table);

#endif /* MLK_DEV_AARCH64_OPT_SRC_ARITH_NATIVE_AARCH64_H */
