/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_TEST_ABICHECK_RISCV64_ABICHECK_RISCV64_H
#define MLK_TEST_ABICHECK_RISCV64_ABICHECK_RISCV64_H

#include "../abicheck_common.h"

#if defined(MLK_SYS_RISCV64)

struct riscv64_register_state
{
  uint64_t gpr[32]; /* x0-x31 */
  uint64_t fpr[32]; /* f0-f31 (64-bit, only used with the LP64D ABI) */
};

/* quiet: MLK_ABICHECK_VERBOSE or MLK_ABICHECK_QUIET (see abicheck_common.h). */
int check_riscv64_lp64d_compliance(struct riscv64_register_state *before,
                                   struct riscv64_register_state *after,
                                   int quiet);
void init_riscv64_register_state(struct riscv64_register_state *state);

extern void asm_call_stub_riscv64(struct riscv64_register_state *input,
                                  struct riscv64_register_state *output,
                                  void (*function_ptr)(void));

#endif /* MLK_SYS_RISCV64 */

#endif /* !MLK_TEST_ABICHECK_RISCV64_ABICHECK_RISCV64_H */
