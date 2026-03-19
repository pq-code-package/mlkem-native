/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef ABICHECKUTIL_H
#define ABICHECKUTIL_H

#include <stdint.h>
#include "../../mlkem/src/sys.h"

#if defined(MLK_SYS_AARCH64)

struct register_state
{
  uint64_t gpr[32];     /* x0-x30 */
  uint64_t neon[32][2]; /* q0-q31 (full 128-bit NEON registers as two 64-bit
                           values) */
};

int check_aarch64_aapcs_compliance(struct register_state *before,
                                   struct register_state *after);
void init_register_state(struct register_state *state);

extern void asm_call_stub(struct register_state *input,
                          struct register_state *output,
                          void (*function_ptr)(void));

#elif defined(MLK_SYS_X86_64)

/* x86_64 System V ABI register state
 * Layout must match x86_64_callstub.S */
struct x86_64_register_state
{
  uint64_t rdi; /*   0 */
  uint64_t rsi; /*   8 */
  uint64_t rdx; /*  16 */
  uint64_t rcx; /*  24 */
  uint64_t r8;  /*  32 */
  uint64_t r9;  /*  40 */
  uint64_t rax; /*  48 */
  uint64_t rbx; /*  56 */
  uint64_t rbp; /*  64 */
  uint64_t r12; /*  72 */
  uint64_t r13; /*  80 */
  uint64_t r14; /*  88 */
  uint64_t r15; /*  96 */
  uint64_t r10; /* 104 */
};

int check_x86_64_sysv_compliance(struct x86_64_register_state *before,
                                 struct x86_64_register_state *after);
void init_x86_64_register_state(struct x86_64_register_state *state);

extern void asm_call_stub_x86_64(struct x86_64_register_state *input,
                                 struct x86_64_register_state *output,
                                 void (*function_ptr)(void));

#endif /* !MLK_SYS_AARCH64 && MLK_SYS_X86_64 */

#endif /* !ABICHECKUTIL_H */
