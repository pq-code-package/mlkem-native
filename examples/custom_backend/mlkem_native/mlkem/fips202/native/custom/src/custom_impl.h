/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef MLK_FIPS202_NATIVE_PROFILE_IMPL_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLK_FIPS202_NATIVE_PROFILE_IMPL_H

#include "sha3.h"

/* Replace (single) Keccak-F1600 by tiny-SHA3's */
#define MLK_USE_FIPS202_X1_NATIVE
static MLK_INLINE void mlk_keccak_f1600_x1_native(uint64_t *state)
{
  tiny_sha3_keccakf(state);
}

#endif /* MLK_FIPS202_NATIVE_PROFILE_H */
