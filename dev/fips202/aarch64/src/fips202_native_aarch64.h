/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H
#define MLK_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H

#include <stdint.h>
#include "../../../../cbmc.h"
#include "../../../../common.h"


#define mlk_keccakf1600_round_constants \
  MLK_NAMESPACE(keccakf1600_round_constants)
extern const uint64_t mlk_keccakf1600_round_constants[];

#define mlk_keccak_f1600_x1_scalar_asm MLK_NAMESPACE(keccak_f1600_x1_scalar_asm)
void mlk_keccak_f1600_x1_scalar_asm(uint64_t state[25], const uint64_t rc[24])
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 1))
  requires(rc == mlk_keccakf1600_round_constants)
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 1))
);

#define mlk_keccak_f1600_x1_scalar_no_lazy_asm \
  MLK_NAMESPACE(keccak_f1600_x1_scalar_no_lazy_asm)
void mlk_keccak_f1600_x1_scalar_no_lazy_asm(uint64_t state[25],
                                            const uint64_t rc[24])
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 1))
  requires(rc == mlk_keccakf1600_round_constants)
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 1))
);

#define mlk_keccak_f1600_x1_v84a_asm MLK_NAMESPACE(keccak_f1600_x1_v84a_asm)
void mlk_keccak_f1600_x1_v84a_asm(uint64_t state[25], const uint64_t rc[24])
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 1))
  requires(rc == mlk_keccakf1600_round_constants)
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 1))
);

#define mlk_keccak_f1600_x2_v84a_asm MLK_NAMESPACE(keccak_f1600_x2_v84a_asm)
void mlk_keccak_f1600_x2_v84a_asm(uint64_t state[50], const uint64_t rc[24])
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 2))
  requires(rc == mlk_keccakf1600_round_constants)
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 2))
);

#define mlk_keccak_f1600_x4_v8a_scalar_hybrid_asm \
  MLK_NAMESPACE(keccak_f1600_x4_v8a_scalar_hybrid_asm)
void mlk_keccak_f1600_x4_v8a_scalar_hybrid_asm(uint64_t state[100],
                                               const uint64_t rc[24])
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 4))
  requires(rc == mlk_keccakf1600_round_constants)
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 4))
);

#define mlk_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm \
  MLK_NAMESPACE(keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm)
void mlk_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm(uint64_t state[100],
                                                    const uint64_t rc[24])
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 4))
  requires(rc == mlk_keccakf1600_round_constants)
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 4))
);

#endif /* !MLK_DEV_FIPS202_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H */
