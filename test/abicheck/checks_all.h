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

#if defined(MLK_SYS_AARCH64)

/* Function prototypes for all ABI checks (only on AArch64) */
int check_keccak_f1600_x1_scalar_asm(void);
#if defined(__ARM_FEATURE_SHA3)
int check_keccak_f1600_x1_v84a_asm(void);
#endif
#if defined(__ARM_FEATURE_SHA3)
int check_keccak_f1600_x2_v84a_asm(void);
#endif
int check_keccak_f1600_x4_v8a_scalar_hybrid_asm(void);
#if defined(__ARM_FEATURE_SHA3)
int check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm(void);
#endif
int check_intt_asm(void);
int check_ntt_asm(void);
int check_poly_mulcache_compute_asm(void);
int check_poly_reduce_asm(void);
int check_poly_tobytes_asm(void);
int check_poly_tomont_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_asm_k2(void);
int check_polyvec_basemul_acc_montgomery_cached_asm_k3(void);
int check_polyvec_basemul_acc_montgomery_cached_asm_k4(void);
int check_rej_uniform_asm(void);

static const abicheck_entry_t all_checks[] = {
    {"keccak_f1600_x1_scalar_asm", check_keccak_f1600_x1_scalar_asm},
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x1_v84a_asm", check_keccak_f1600_x1_v84a_asm},
#endif
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x2_v84a_asm", check_keccak_f1600_x2_v84a_asm},
#endif
    {"keccak_f1600_x4_v8a_scalar_hybrid_asm",
     check_keccak_f1600_x4_v8a_scalar_hybrid_asm},
#if defined(__ARM_FEATURE_SHA3)
    {"keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm",
     check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm},
#endif
    {"intt_asm", check_intt_asm},
    {"ntt_asm", check_ntt_asm},
    {"poly_mulcache_compute_asm", check_poly_mulcache_compute_asm},
    {"poly_reduce_asm", check_poly_reduce_asm},
    {"poly_tobytes_asm", check_poly_tobytes_asm},
    {"poly_tomont_asm", check_poly_tomont_asm},
    {"polyvec_basemul_acc_montgomery_cached_asm_k2",
     check_polyvec_basemul_acc_montgomery_cached_asm_k2},
    {"polyvec_basemul_acc_montgomery_cached_asm_k3",
     check_polyvec_basemul_acc_montgomery_cached_asm_k3},
    {"polyvec_basemul_acc_montgomery_cached_asm_k4",
     check_polyvec_basemul_acc_montgomery_cached_asm_k4},
    {"rej_uniform_asm", check_rej_uniform_asm},
    {NULL, NULL} /* Sentinel */
};

#else /* MLK_SYS_AARCH64 */

/* Empty array for non-AArch64 platforms */
static const abicheck_entry_t all_checks[] = {
    {NULL, NULL} /* Sentinel */
};

#endif /* !MLK_SYS_AARCH64 */

#endif /* !CHECKS_ALL_H */
