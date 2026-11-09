/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_FIPS202_NATIVE_RISCV64_SRC_FIPS202_NATIVE_RISCV64_H
#define MLK_FIPS202_NATIVE_RISCV64_SRC_FIPS202_NATIVE_RISCV64_H

#include "../../../../cbmc.h"
#include "../../../../common.h"

#define mlk_keccakf1600_round_constants \
  MLK_NAMESPACE(keccakf1600_round_constants)
MLK_INTERNAL_DATA_DECLARATION const uint64_t
    mlk_keccakf1600_round_constants[24];

#define mlk_keccak_f1600_x1_zbb_riscv64_asm \
  MLK_NAMESPACE(keccak_f1600_x1_zbb_riscv64_asm)
void mlk_keccak_f1600_x1_zbb_riscv64_asm(uint64_t state[25],
                                         const uint64_t rc[24])
/* This must be kept in sync with the HOL-Light specification
 * in proofs/hol_light/riscv64/proofs/keccak_f1600_x1_zbb_riscv64_asm.ml */
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 1))
  requires(rc == mlk_keccakf1600_round_constants)
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 1))
);

#endif /* !MLK_FIPS202_NATIVE_RISCV64_SRC_FIPS202_NATIVE_RISCV64_H */
