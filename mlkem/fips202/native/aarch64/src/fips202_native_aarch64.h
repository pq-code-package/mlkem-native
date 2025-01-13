/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef FIPS202_AARCH64_NATIVE_H
#define FIPS202_AARCH64_NATIVE_H

#include <stdint.h>
#include "../../../../common.h"

#define keccak_f1600_x1_scalar_asm_opt \
  FIPS202_NAMESPACE(keccak_f1600_x1_scalar_asm_opt)
void keccak_f1600_x1_scalar_asm_opt(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x1_v84a_asm_clean \
  FIPS202_NAMESPACE(keccak_f1600_x1_v84a_asm_clean)
void keccak_f1600_x1_v84a_asm_clean(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x2_v84a_asm_clean \
  FIPS202_NAMESPACE(keccak_f1600_x2_v84a_asm_clean)
void keccak_f1600_x2_v84a_asm_clean(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x2_v8a_v84a_asm_hybrid \
  FIPS202_NAMESPACE(keccak_f1600_x2_v8a_v84a_asm_hybrid)
void keccak_f1600_x2_v8a_v84a_asm_hybrid(uint64_t *state, uint64_t const *rc);

#define keccak_f1600_x4_scalar_v8a_asm_hybrid_opt \
  FIPS202_NAMESPACE(keccak_f1600_x4_scalar_v8a_asm_hybrid_opt)
void keccak_f1600_x4_scalar_v8a_asm_hybrid_opt(uint64_t *state,
                                               uint64_t const *rc);

#define keccak_f1600_x4_scalar_v84a_asm_hybrid_opt \
  FIPS202_NAMESPACE(keccak_f1600_x4_scalar_v84a_asm_hybrid_opt)
void keccak_f1600_x4_scalar_v84a_asm_hybrid_opt(uint64_t *state,
                                                uint64_t const *rc);

#define keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt \
  FIPS202_NAMESPACE(keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt)
void keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt(uint64_t *state,
                                                    uint64_t const *rc);

#define keccakf1600_round_constants \
  FIPS202_NAMESPACE(keccakf1600_round_constants)
extern const uint64_t keccakf1600_round_constants[];

#endif /* FIPS202_AARCH64_NATIVE_H */
