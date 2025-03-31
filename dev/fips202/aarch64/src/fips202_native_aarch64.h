/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H
#define MLK_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H

#include <stdint.h>
#include "../../../../common.h"

#define mlk_keccak_f1600_x1_scalar_asm MLK_NAMESPACE(keccak_f1600_x1_scalar_asm)
void mlk_keccak_f1600_x1_scalar_asm(uint64_t *state, uint64_t const *rc);

#define mlk_keccak_f1600_x1_v84a_asm MLK_NAMESPACE(keccak_f1600_x1_v84a_asm)
void mlk_keccak_f1600_x1_v84a_asm(uint64_t *state, uint64_t const *rc);

#define mlk_keccak_f1600_x2_v84a_asm MLK_NAMESPACE(keccak_f1600_x2_v84a_asm)
void mlk_keccak_f1600_x2_v84a_asm(uint64_t *state, uint64_t const *rc);

#define mlk_keccak_f1600_x2_v8a_v84a_asm_hybrid \
  MLK_NAMESPACE(keccak_f1600_x2_v8a_v84a_asm_hybrid)
void mlk_keccak_f1600_x2_v8a_v84a_asm_hybrid(uint64_t *state,
                                             uint64_t const *rc);

#define mlk_keccak_f1600_x4_scalar_v8a_asm_hybrid \
  MLK_NAMESPACE(keccak_f1600_x4_scalar_v8a_asm_hybrid)
void mlk_keccak_f1600_x4_scalar_v8a_asm_hybrid(uint64_t *state,
                                               uint64_t const *rc);

#define mlk_keccak_f1600_x4_scalar_v84a_asm_hybrid \
  MLK_NAMESPACE(keccak_f1600_x4_scalar_v84a_asm_hybrid)
void mlk_keccak_f1600_x4_scalar_v84a_asm_hybrid(uint64_t *state,
                                                uint64_t const *rc);

#define mlk_keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm \
  MLK_NAMESPACE(keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm)
void mlk_keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm(uint64_t *state,
                                                    uint64_t const *rc);

#define mlk_keccakf1600_round_constants \
  MLK_NAMESPACE(keccakf1600_round_constants)
extern const uint64_t mlk_keccakf1600_round_constants[];

#endif /* !MLK_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H */
