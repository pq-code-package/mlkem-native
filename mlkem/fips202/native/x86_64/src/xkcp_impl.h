/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H

#include "../../../../common.h"

#define KeccakP1600times4_PermuteAll_24rounds \
  FIPS202_NAMESPACE(KeccakP1600times4_PermuteAll_24rounds)
void KeccakP1600times4_PermuteAll_24rounds(void *states);

#define MLKEM_USE_FIPS202_X4_NATIVE
static INLINE void keccak_f1600_x4_native(uint64_t *state)
{
  KeccakP1600times4_PermuteAll_24rounds(state);
}

#endif /* MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H */
