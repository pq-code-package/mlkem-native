/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef MLK_TEST_ABICHECK_CHECKS_RISCV64_ALL_H
#define MLK_TEST_ABICHECK_CHECKS_RISCV64_ALL_H

#include <stddef.h>
#include "../abicheck_common.h"

#if defined(MLK_SYS_RISCV64)

#if defined(__riscv_zbb)
int check_keccak_f1600_x1_zbb_riscv64_asm(void);
#endif
#if defined(MLK_SYS_RISCV64_RVV)
int check_intt_vlen128_riscv64_asm(void);
int check_intt_vlen256_riscv64_asm(void);
int check_ntt_vlen128_riscv64_asm(void);
int check_ntt_vlen256_riscv64_asm(void);
int check_poly_mulcache_compute_riscv64_asm(void);
int check_poly_reduce_riscv64_asm(void);
int check_poly_tomont_riscv64_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm(void);
int check_polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm(void);
int check_rej_uniform_riscv64_asm(void);
#endif /* MLK_SYS_RISCV64_RVV */

static const abicheck_entry_t all_checks[] = {
#if defined(__riscv_zbb)
    {"keccak_f1600_x1_zbb_riscv64_asm", check_keccak_f1600_x1_zbb_riscv64_asm},
#endif
#if defined(MLK_SYS_RISCV64_RVV)
    {"intt_vlen128_riscv64_asm", check_intt_vlen128_riscv64_asm},
    {"intt_vlen256_riscv64_asm", check_intt_vlen256_riscv64_asm},
    {"ntt_vlen128_riscv64_asm", check_ntt_vlen128_riscv64_asm},
    {"ntt_vlen256_riscv64_asm", check_ntt_vlen256_riscv64_asm},
    {"poly_mulcache_compute_riscv64_asm",
     check_poly_mulcache_compute_riscv64_asm},
    {"poly_reduce_riscv64_asm", check_poly_reduce_riscv64_asm},
    {"poly_tomont_riscv64_asm", check_poly_tomont_riscv64_asm},
    {"polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm",
     check_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm},
    {"polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm",
     check_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm},
    {"polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm",
     check_polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm},
    {"rej_uniform_riscv64_asm", check_rej_uniform_riscv64_asm},
#endif           /* MLK_SYS_RISCV64_RVV */
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_RISCV64 */

#endif /* !MLK_TEST_ABICHECK_CHECKS_RISCV64_ALL_H */
