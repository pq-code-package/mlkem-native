/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_DEV_FIPS202_AARCH64_X4_V8A_SCALAR_H
#define MLK_DEV_FIPS202_AARCH64_X4_V8A_SCALAR_H

/* Part of backend API */
#define MLK_USE_FIPS202_X4_NATIVE
/* Guard for assembly file */
#define MLK_FIPS202_AARCH64_NEED_X4_V8A_SCALAR_HYBRID

#if !defined(__ASSEMBLER__)
#include "src/fips202_native_aarch64.h"
static MLK_INLINE void mlk_keccak_f1600_x4_native(uint64_t *state)
{
  mlk_keccak_f1600_x4_scalar_v8a_asm_hybrid(state,
                                            mlk_keccakf1600_round_constants);
}
#endif /* !__ASSEMBLER__ */

#endif /* !MLK_DEV_FIPS202_AARCH64_X4_V8A_SCALAR_H */
