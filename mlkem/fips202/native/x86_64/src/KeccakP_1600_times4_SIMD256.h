/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_FIPS202_NATIVE_X86_64_SRC_KECCAKP_1600_TIMES4_SIMD256_H
#define MLK_FIPS202_NATIVE_X86_64_SRC_KECCAKP_1600_TIMES4_SIMD256_H

#include "../../../../common.h"

#define mlk_keccakf1600x4_permute24 \
  MLK_NAMESPACE(KeccakP1600times4_PermuteAll_24rounds)
void mlk_keccakf1600x4_permute24(void *states);

#endif /* !MLK_FIPS202_NATIVE_X86_64_SRC_KECCAKP_1600_TIMES4_SIMD256_H */
