/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_FIPS202_NATIVE_ARMV81M_SRC_FIPS202_NATIVE_ARMV81M_H
#define MLK_FIPS202_NATIVE_ARMV81M_SRC_FIPS202_NATIVE_ARMV81M_H

#include "../../../../common.h"

/* Keccak round constants in bit-interleaved form */
#define mlk_keccakf1600_round_constants \
  MLK_NAMESPACE(keccakf1600_round_constants)
extern const uint32_t mlk_keccakf1600_round_constants[48];

#define mlk_keccak_f1600_x4_mve_asm MLK_NAMESPACE(keccak_f1600_x4_mve_asm)
void mlk_keccak_f1600_x4_mve_asm(uint64_t state[100], uint64_t tmpstate[100],
                                 const uint32_t rc[48]);

#endif /* !MLK_FIPS202_NATIVE_ARMV81M_SRC_FIPS202_NATIVE_ARMV81M_H */
