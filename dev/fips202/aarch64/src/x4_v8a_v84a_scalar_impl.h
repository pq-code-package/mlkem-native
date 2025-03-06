/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_DEV_FIPS202_AARCH64_SRC_X4_V8A_V84A_SCALAR_IMPL_H
#define MLK_DEV_FIPS202_AARCH64_SRC_X4_V8A_V84A_SCALAR_IMPL_H

#ifdef MLK_FIPS202_NATIVE_PROFILE_IMPL_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLK_FIPS202_NATIVE_PROFILE_IMPL_H

#if !defined(__ARM_FEATURE_SHA3)
#error This backend can only be used if SHA3 extensions are available.
#endif /* __ARM_FEATURE_SHA3 */

#include "fips202_native_aarch64.h"

#define MLK_USE_FIPS202_X4_NATIVE
static MLK_INLINE void mlk_keccak_f1600_x4_native(uint64_t *state)
{
  mlk_keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm(
      state, mlk_keccakf1600_round_constants);
}

#endif /* MLK_FIPS202_NATIVE_PROFILE_IMPL_H */

#endif /* MLK_DEV_FIPS202_AARCH64_SRC_X4_V8A_V84A_SCALAR_IMPL_H */
