/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef MLK_TEST_ABICHECK_CHECKS_AARCH64_ALL_H
#define MLK_TEST_ABICHECK_CHECKS_AARCH64_ALL_H

#include <stddef.h>
#include "../abicheck_prologue.h"
#include "../abicheckutil.h"

#if defined(MLK_SYS_AARCH64)

int check_intt_aarch64_asm(void);
int check_keccak_f1600_x1_scalar_aarch64_asm(void);
#if defined(__ARM_FEATURE_SHA3)
int check_keccak_f1600_x1_v84a_aarch64_asm(void);
#endif
#if defined(__ARM_FEATURE_SHA3)
int check_keccak_f1600_x2_v84a_aarch64_asm(void);
#endif
int check_keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm(void);
#if defined(__ARM_FEATURE_SHA3)
int check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm(void);
#endif
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

#endif /* defined(MLK_SYS_AARCH64) */

#endif /* !MLK_TEST_ABICHECK_CHECKS_AARCH64_ALL_H */
