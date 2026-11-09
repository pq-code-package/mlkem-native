/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_RISCV64_X1_ZBB_H
#define MLK_FIPS202_NATIVE_RISCV64_X1_ZBB_H

/* Part of backend API */
#define MLK_USE_NATIVE_FIPS202_X1
/* Guard for assembly file */
#define MLK_FIPS202_RISCV64_NEED_X1_ZBB

#if !defined(__ASSEMBLER__)
#include "../api.h"
#include "src/fips202_native_riscv64.h"
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_keccak_f1600_x1_native(uint64_t *state)
{
  mlk_keccak_f1600_x1_zbb_riscv64_asm(state, mlk_keccakf1600_round_constants);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* !__ASSEMBLER__ */

#endif /* !MLK_FIPS202_NATIVE_RISCV64_X1_ZBB_H */
