/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef FIPS202_NATIVE_PROFILE_IMPL_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define FIPS202_NATIVE_PROFILE_IMPL_H

#include "sha3.h"

/* Replace (single) Keccak-F1600 by tiny-SHA3's */
#define MLKEM_USE_FIPS202_X1_NATIVE
static INLINE void keccak_f1600_x1_native(uint64_t *state)
{
  sha3_keccakf(state);
}

#endif /* FIPS202_NATIVE_PROFILE_H */
