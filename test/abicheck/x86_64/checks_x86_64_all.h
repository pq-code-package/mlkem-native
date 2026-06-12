/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef MLK_TEST_ABICHECK_CHECKS_X86_64_ALL_H
#define MLK_TEST_ABICHECK_CHECKS_X86_64_ALL_H

#include <stddef.h>
#include "../abicheck_common.h"

#if defined(MLK_SYS_X86_64)

#if defined(MLK_SYSV_ABI_SUPPORTED)
#if defined(__AVX2__)
int check_invntt_avx2_asm(void);
int check_keccak_f1600_x4_avx2_asm(void);
int check_ntt_avx2_asm(void);
int check_nttfrombytes_avx2_asm(void);
int check_ntttobytes_avx2_asm(void);
int check_nttunpack_avx2_asm(void);
int check_poly_compress_d10_avx2_asm(void);
int check_poly_compress_d11_avx2_asm(void);
int check_poly_compress_d4_avx2_asm(void);
int check_poly_compress_d5_avx2_asm(void);
int check_poly_decompress_d10_avx2_asm(void);
int check_poly_decompress_d11_avx2_asm(void);
int check_poly_decompress_d4_avx2_asm(void);
int check_poly_decompress_d5_avx2_asm(void);
int check_poly_mulcache_compute_avx2_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k2_avx2_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k3_avx2_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k4_avx2_asm(void);
int check_reduce_avx2_asm(void);
int check_rej_uniform_avx2_asm(void);
int check_tomont_avx2_asm(void);
#endif /* __AVX2__ */
#endif /* MLK_SYSV_ABI_SUPPORTED */

static const abicheck_entry_t all_checks[] = {
#if defined(MLK_SYSV_ABI_SUPPORTED)
#if defined(__AVX2__)
    {"invntt_avx2_asm", check_invntt_avx2_asm},
    {"keccak_f1600_x4_avx2_asm", check_keccak_f1600_x4_avx2_asm},
    {"ntt_avx2_asm", check_ntt_avx2_asm},
    {"nttfrombytes_avx2_asm", check_nttfrombytes_avx2_asm},
    {"ntttobytes_avx2_asm", check_ntttobytes_avx2_asm},
    {"nttunpack_avx2_asm", check_nttunpack_avx2_asm},
    {"poly_compress_d10_avx2_asm", check_poly_compress_d10_avx2_asm},
    {"poly_compress_d11_avx2_asm", check_poly_compress_d11_avx2_asm},
    {"poly_compress_d4_avx2_asm", check_poly_compress_d4_avx2_asm},
    {"poly_compress_d5_avx2_asm", check_poly_compress_d5_avx2_asm},
    {"poly_decompress_d10_avx2_asm", check_poly_decompress_d10_avx2_asm},
    {"poly_decompress_d11_avx2_asm", check_poly_decompress_d11_avx2_asm},
    {"poly_decompress_d4_avx2_asm", check_poly_decompress_d4_avx2_asm},
    {"poly_decompress_d5_avx2_asm", check_poly_decompress_d5_avx2_asm},
    {"poly_mulcache_compute_avx2_asm", check_poly_mulcache_compute_avx2_asm},
    {"polyvec_basemul_acc_montgomery_cached_k2_avx2_asm",
     check_polyvec_basemul_acc_montgomery_cached_k2_avx2_asm},
    {"polyvec_basemul_acc_montgomery_cached_k3_avx2_asm",
     check_polyvec_basemul_acc_montgomery_cached_k3_avx2_asm},
    {"polyvec_basemul_acc_montgomery_cached_k4_avx2_asm",
     check_polyvec_basemul_acc_montgomery_cached_k4_avx2_asm},
    {"reduce_avx2_asm", check_reduce_avx2_asm},
    {"rej_uniform_avx2_asm", check_rej_uniform_avx2_asm},
    {"tomont_avx2_asm", check_tomont_avx2_asm},
#endif           /* __AVX2__ */
#endif           /* MLK_SYSV_ABI_SUPPORTED */
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_X86_64 */

#endif /* !MLK_TEST_ABICHECK_CHECKS_X86_64_ALL_H */
