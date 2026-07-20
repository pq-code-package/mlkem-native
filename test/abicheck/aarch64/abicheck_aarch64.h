/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_TEST_ABICHECK_ABICHECK_AARCH64_H
#define MLK_TEST_ABICHECK_ABICHECK_AARCH64_H

#include "../abicheck_common.h"

#if defined(MLK_SYS_AARCH64)

/* MLK_ALIGN-aligned so the stub's 128-bit ldp/stp q on neon[] are aligned. */
struct MLK_ALIGN aarch64_register_state
{
  uint64_t gpr[32];     /* x0-x30 */
  uint64_t neon[32][2]; /* q0-q31 (full 128-bit NEON registers as two 64-bit
                           values) */
};

/* quiet: MLK_ABICHECK_VERBOSE or MLK_ABICHECK_QUIET (see abicheck_common.h). */
int check_aarch64_aapcs_compliance(struct aarch64_register_state *before,
                                   struct aarch64_register_state *after,
                                   int quiet);
void init_aarch64_register_state(struct aarch64_register_state *state);

extern void asm_call_stub_aarch64(struct aarch64_register_state *input,
                                  struct aarch64_register_state *output,
                                  void (*function_ptr)(void), int use_neon);

static MLK_INLINE void call_stub_aarch64(struct aarch64_register_state *input,
                                         struct aarch64_register_state *output,
                                         void (*function_ptr)(void))
{
  int use_neon = mlk_sys_check_capability(MLK_SYS_CAP_NEON) != 0;
  asm_call_stub_aarch64(input, output, function_ptr, use_neon);
}

#endif /* MLK_SYS_AARCH64 */

#endif /* !MLK_TEST_ABICHECK_ABICHECK_AARCH64_H */
