/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef ABICHECKUTIL_H
#define ABICHECKUTIL_H

#include <stdint.h>
#include "../../mlkem/src/sys.h"

struct register_state
{
  uint64_t gpr[32];     /* x0-x30 */
  uint64_t neon[32][2]; /* q0-q31 (full 128-bit NEON registers as two 64-bit
                           values) */
};

/* ABI compliance checking */
int check_aarch64_aapcs_compliance(struct register_state *before,
                                   struct register_state *after);

/* Utility functions */
void init_random_register_state(struct register_state *state);

/* Assembly stub function */
#ifdef MLK_SYS_AARCH64
extern void asm_call_stub(struct register_state *input,
                          struct register_state *output,
                          void (*function_ptr)(void));
#else
/* Stub implementation for non-AArch64 platforms */
static MLK_INLINE void asm_call_stub(struct register_state *input,
                                     struct register_state *output,
                                     void (*function_ptr)(void))
{
  (void)input;
  (void)output;
  (void)function_ptr;
  /* This should never be called on non-AArch64 platforms */
  /* The main abicheck program checks architecture before running tests */
}
#endif /* !MLK_SYS_AARCH64 */

#endif /* !ABICHECKUTIL_H */
