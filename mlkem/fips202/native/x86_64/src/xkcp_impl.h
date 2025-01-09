/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H

#include <string.h>
#include "KeccakP-1600-times4-SnP.h"

#define MLKEM_USE_FIPS202_X4_NATIVE
static INLINE void keccak_f1600_x4_native(uint64_t *state)
{
  KeccakP1600times4_PermuteAll_24rounds(state);
}

#define MLKEM_USE_FIPS202_X1_NATIVE
static INLINE void keccak_f1600_x1_native(uint64_t *state)
{
  uint64_t s[4*25];
  memcpy(s, state, sizeof(uint64_t)*25);
  KeccakP1600times4_PermuteAll_24rounds(s);
  memcpy(state, s, sizeof(uint64_t)*25);
}


#endif /* MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H */
