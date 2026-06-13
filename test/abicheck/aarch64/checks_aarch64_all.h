/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef CHECKS_AARCH64_ALL_H
#define CHECKS_AARCH64_ALL_H

#include <stddef.h>
#define MLK_BUILD_INTERNAL
#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "../../../mlkem/mlkem_native_config.h"
#endif
#include "../../../mlkem/src/sys.h"

#include "../abicheckutil.h"

#if defined(MLK_SYS_AARCH64)

int check_intt_aarch64_asm(void);
int check_keccak_f1600_x1_scalar_aarch64_asm(void);
int check_keccak_f1600_x1_v84a_aarch64_asm(void);
int check_keccak_f1600_x2_v84a_aarch64_asm(void);
int check_keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm(void);
int check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm(void);
int check_ntt_aarch64_asm(void);
int check_poly_mulcache_compute_aarch64_asm(void);
int check_poly_reduce_aarch64_asm(void);
int check_poly_tobytes_aarch64_asm(void);
int check_poly_tomont_aarch64_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm(void);
int check_rej_uniform_aarch64_asm(void);

static const abicheck_entry_t all_checks[] = {
    {"intt_aarch64_asm", check_intt_aarch64_asm},
    {"keccak_f1600_x1_scalar_aarch64_asm",
     check_keccak_f1600_x1_scalar_aarch64_asm},
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x1_v84a_aarch64_asm",
     check_keccak_f1600_x1_v84a_aarch64_asm},
#endif
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x2_v84a_aarch64_asm",
     check_keccak_f1600_x2_v84a_aarch64_asm},
#endif
    {"keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm",
     check_keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm},
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm",
     check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm},
#endif
    {"ntt_aarch64_asm", check_ntt_aarch64_asm},
    {"poly_mulcache_compute_aarch64_asm",
     check_poly_mulcache_compute_aarch64_asm},
    {"poly_reduce_aarch64_asm", check_poly_reduce_aarch64_asm},
    {"poly_tobytes_aarch64_asm", check_poly_tobytes_aarch64_asm},
    {"poly_tomont_aarch64_asm", check_poly_tomont_aarch64_asm},
    {"polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm",
     check_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm},
    {"polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm",
     check_polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm},
    {"polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm",
     check_polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm},
    {"rej_uniform_aarch64_asm", check_rej_uniform_aarch64_asm},
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_AARCH64 */

#endif /* !CHECKS_AARCH64_ALL_H */
