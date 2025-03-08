/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#if !defined(MLK_FIPS202_CUSTOM_TINY_SHA3_H)
#define MLK_FIPS202_CUSTOM_TINY_SHA3_H

#if !defined(__ASSEMBLER__)
#include "src/sha3.h"
/* Replace (single) Keccak-F1600 by tiny-SHA3's */
#define MLK_USE_FIPS202_X1_NATIVE
static MLK_INLINE void mlk_keccak_f1600_x1_native(uint64_t *state)
{
  tiny_sha3_keccakf(state);
}
#endif /* !__ASSEMBLER__ */

#endif /* MLK_FIPS202_CUSTOM_TINY_SHA3_H */
