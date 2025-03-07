/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_FIPS202_NATIVE_AARCH64_X1_SCALAR_H
#define MLK_FIPS202_NATIVE_AARCH64_X1_SCALAR_H

/* Part of backend API */
#define MLK_USE_FIPS202_X1_NATIVE
/* Guard for assembly file */
#define MLK_FIPS202_AARCH64_NEED_X1_SCALAR

#if !defined(__ASSEMBLER__)
#include "src/fips202_native_aarch64.h"
static MLK_INLINE void mlk_keccak_f1600_x1_native(uint64_t *state)
{
  mlk_keccak_f1600_x1_scalar_asm(state, mlk_keccakf1600_round_constants);
}
#endif /* !__ASSEMBLER__ */

#endif /* MLK_FIPS202_NATIVE_AARCH64_X1_SCALAR_H */
