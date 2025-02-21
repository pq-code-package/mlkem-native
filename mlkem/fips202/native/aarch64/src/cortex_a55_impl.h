/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_FIPS202_NATIVE_AARCH64_SRC_CORTEX_A55_IMPL_H
#define MLK_FIPS202_NATIVE_AARCH64_SRC_CORTEX_A55_IMPL_H
/* FIPS202 assembly profile targeting Cortex-A55 */

#ifdef MLK_FIPS202_NATIVE_PROFILE_IMPL_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLK_FIPS202_NATIVE_PROFILE_IMPL_H

#include "fips202_native_aarch64.h"

/*
 * On Cortex-A55, we use lazy rotation assembly for Keccak-x1,
 * but no batched assembly implementation.
 */
#define MLK_USE_FIPS202_X1_NATIVE
static MLK_INLINE void keccak_f1600_x1_native(uint64_t *state)
{
  keccak_f1600_x1_scalar_asm_opt(state, mlk_keccakf1600_round_constants);
}

#endif /* MLK_FIPS202_NATIVE_PROFILE_IMPL_H */

#endif /* MLK_FIPS202_NATIVE_AARCH64_SRC_CORTEX_A55_IMPL_H */
