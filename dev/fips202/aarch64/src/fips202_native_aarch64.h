/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLKEM_NATIVE_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H
#define MLKEM_NATIVE_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H

#include <stdint.h>
#include "../../../../common.h"

#define keccak_f1600_x1_scalar_asm_opt \
  MLKEM_NAMESPACE(keccak_f1600_x1_scalar_asm_opt)
void keccak_f1600_x1_scalar_asm_opt(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x1_v84a_asm_clean \
  MLKEM_NAMESPACE(keccak_f1600_x1_v84a_asm_clean)
void keccak_f1600_x1_v84a_asm_clean(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x2_v84a_asm_clean \
  MLKEM_NAMESPACE(keccak_f1600_x2_v84a_asm_clean)
void keccak_f1600_x2_v84a_asm_clean(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x2_v8a_v84a_asm_hybrid \
  MLKEM_NAMESPACE(keccak_f1600_x2_v8a_v84a_asm_hybrid)
void keccak_f1600_x2_v8a_v84a_asm_hybrid(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x4_scalar_v8a_asm_hybrid_opt \
  MLKEM_NAMESPACE(keccak_f1600_x4_scalar_v8a_asm_hybrid_opt)
void keccak_f1600_x4_scalar_v8a_asm_hybrid_opt(uint64_t *state,
                                               uint64_t const *rc);

#define keccak_f1600_x4_scalar_v84a_asm_hybrid_opt \
  MLKEM_NAMESPACE(keccak_f1600_x4_scalar_v84a_asm_hybrid_opt)
void keccak_f1600_x4_scalar_v84a_asm_hybrid_opt(uint64_t *state,
                                                uint64_t const *rc);

#define keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt \
  MLKEM_NAMESPACE(keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt)
void keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt(uint64_t *state,
                                                    uint64_t const *rc);

#define keccakf1600_round_constants MLKEM_NAMESPACE(keccakf1600_round_constants)
extern const uint64_t keccakf1600_round_constants[];

#endif /* MLKEM_NATIVE_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H */
