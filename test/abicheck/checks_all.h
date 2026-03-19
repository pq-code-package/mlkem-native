/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef CHECKS_ALL_H
#define CHECKS_ALL_H

#include <stddef.h>
#include "../../mlkem/src/sys.h"

/* Array of all check functions */
typedef struct
{
  const char *name;
  int (*check_func)(void);
} abicheck_entry_t;

int check_intt_aarch64_asm_aarch64(void);
int check_keccak_f1600_x1_scalar_aarch64_asm_aarch64(void);
int check_keccak_f1600_x1_v84a_aarch64_asm_aarch64(void);
int check_keccak_f1600_x2_v84a_aarch64_asm_aarch64(void);
int check_keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm_aarch64(void);
int check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm_aarch64(void);
int check_ntt_aarch64_asm_aarch64(void);
int check_poly_mulcache_compute_aarch64_asm_aarch64(void);
int check_poly_reduce_aarch64_asm_aarch64(void);
int check_poly_tobytes_aarch64_asm_aarch64(void);
int check_poly_tomont_aarch64_asm_aarch64(void);
int check_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm_aarch64(void);
int check_polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm_aarch64(void);
int check_polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm_aarch64(void);
int check_rej_uniform_aarch64_asm_aarch64(void);
int check_invntt_avx2_asm_x86_64(void);
int check_keccak_f1600_x4_avx2_asm_x86_64(void);
int check_ntt_avx2_asm_x86_64(void);
int check_nttfrombytes_avx2_asm_x86_64(void);
int check_ntttobytes_avx2_asm_x86_64(void);
int check_nttunpack_avx2_asm_x86_64(void);
int check_poly_compress_d10_avx2_asm_x86_64(void);
int check_poly_compress_d11_avx2_asm_x86_64(void);
int check_poly_compress_d4_avx2_asm_x86_64(void);
int check_poly_compress_d5_avx2_asm_x86_64(void);
int check_poly_decompress_d10_avx2_asm_x86_64(void);
int check_poly_decompress_d11_avx2_asm_x86_64(void);
int check_poly_decompress_d4_avx2_asm_x86_64(void);
int check_poly_decompress_d5_avx2_asm_x86_64(void);
int check_poly_mulcache_compute_avx2_asm_x86_64(void);
int check_polyvec_basemul_acc_montgomery_cached_k2_avx2_asm_x86_64(void);
int check_polyvec_basemul_acc_montgomery_cached_k3_avx2_asm_x86_64(void);
int check_polyvec_basemul_acc_montgomery_cached_k4_avx2_asm_x86_64(void);
int check_reduce_avx2_asm_x86_64(void);
int check_rej_uniform_avx2_asm_x86_64(void);
int check_tomont_avx2_asm_x86_64(void);

#if defined(MLK_SYS_AARCH64)

static const abicheck_entry_t all_checks[] = {
    {"intt_aarch64_asm_aarch64", check_intt_aarch64_asm_aarch64},
    {"keccak_f1600_x1_scalar_aarch64_asm_aarch64",
     check_keccak_f1600_x1_scalar_aarch64_asm_aarch64},
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x1_v84a_aarch64_asm_aarch64",
     check_keccak_f1600_x1_v84a_aarch64_asm_aarch64},
#endif
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x2_v84a_aarch64_asm_aarch64",
     check_keccak_f1600_x2_v84a_aarch64_asm_aarch64},
#endif
    {"keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm_aarch64",
     check_keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm_aarch64},
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm_aarch64",
     check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm_aarch64},
#endif
    {"ntt_aarch64_asm_aarch64", check_ntt_aarch64_asm_aarch64},
    {"poly_mulcache_compute_aarch64_asm_aarch64",
     check_poly_mulcache_compute_aarch64_asm_aarch64},
    {"poly_reduce_aarch64_asm_aarch64", check_poly_reduce_aarch64_asm_aarch64},
    {"poly_tobytes_aarch64_asm_aarch64",
     check_poly_tobytes_aarch64_asm_aarch64},
    {"poly_tomont_aarch64_asm_aarch64", check_poly_tomont_aarch64_asm_aarch64},
    {"polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm_aarch64",
     check_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm_aarch64},
    {"polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm_aarch64",
     check_polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm_aarch64},
    {"polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm_aarch64",
     check_polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm_aarch64},
    {"rej_uniform_aarch64_asm_aarch64", check_rej_uniform_aarch64_asm_aarch64},
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_AARCH64 */

#if defined(MLK_SYS_X86_64)

static const abicheck_entry_t all_checks[] = {
    {"invntt_avx2_asm_x86_64", check_invntt_avx2_asm_x86_64},
    {"keccak_f1600_x4_avx2_asm_x86_64", check_keccak_f1600_x4_avx2_asm_x86_64},
    {"ntt_avx2_asm_x86_64", check_ntt_avx2_asm_x86_64},
    {"nttfrombytes_avx2_asm_x86_64", check_nttfrombytes_avx2_asm_x86_64},
    {"ntttobytes_avx2_asm_x86_64", check_ntttobytes_avx2_asm_x86_64},
    {"nttunpack_avx2_asm_x86_64", check_nttunpack_avx2_asm_x86_64},
    {"poly_compress_d10_avx2_asm_x86_64",
     check_poly_compress_d10_avx2_asm_x86_64},
    {"poly_compress_d11_avx2_asm_x86_64",
     check_poly_compress_d11_avx2_asm_x86_64},
    {"poly_compress_d4_avx2_asm_x86_64",
     check_poly_compress_d4_avx2_asm_x86_64},
    {"poly_compress_d5_avx2_asm_x86_64",
     check_poly_compress_d5_avx2_asm_x86_64},
    {"poly_decompress_d10_avx2_asm_x86_64",
     check_poly_decompress_d10_avx2_asm_x86_64},
    {"poly_decompress_d11_avx2_asm_x86_64",
     check_poly_decompress_d11_avx2_asm_x86_64},
    {"poly_decompress_d4_avx2_asm_x86_64",
     check_poly_decompress_d4_avx2_asm_x86_64},
    {"poly_decompress_d5_avx2_asm_x86_64",
     check_poly_decompress_d5_avx2_asm_x86_64},
    {"poly_mulcache_compute_avx2_asm_x86_64",
     check_poly_mulcache_compute_avx2_asm_x86_64},
    {"polyvec_basemul_acc_montgomery_cached_k2_avx2_asm_x86_64",
     check_polyvec_basemul_acc_montgomery_cached_k2_avx2_asm_x86_64},
    {"polyvec_basemul_acc_montgomery_cached_k3_avx2_asm_x86_64",
     check_polyvec_basemul_acc_montgomery_cached_k3_avx2_asm_x86_64},
    {"polyvec_basemul_acc_montgomery_cached_k4_avx2_asm_x86_64",
     check_polyvec_basemul_acc_montgomery_cached_k4_avx2_asm_x86_64},
    {"reduce_avx2_asm_x86_64", check_reduce_avx2_asm_x86_64},
    {"rej_uniform_avx2_asm_x86_64", check_rej_uniform_avx2_asm_x86_64},
    {"tomont_avx2_asm_x86_64", check_tomont_avx2_asm_x86_64},
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_X86_64 */

#if !defined(MLK_SYS_AARCH64) && !defined(MLK_SYS_X86_64)
static const abicheck_entry_t all_checks[] = {
    {NULL, NULL} /* Sentinel */
};
#endif

#endif /* !CHECKS_ALL_H */
