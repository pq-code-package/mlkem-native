/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_TEST_ABICHECK_ABICHECK_X86_64_H
#define MLK_TEST_ABICHECK_ABICHECK_X86_64_H

#include "../abicheck_common.h"

#if defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)

/* x86_64 System V ABI register state
 * Layout must match callstub_x86_64.S */
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
                                 struct x86_64_register_state *after,
                                 int quiet);
void init_x86_64_register_state(struct x86_64_register_state *state);

extern MLK_SYSV_ABI
void asm_call_stub_x86_64_sysv(
    struct x86_64_register_state *input, struct x86_64_register_state *output,
                               MLK_SYSV_ABI
    void (*function_ptr)(void));

#endif /* MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED */

#endif /* !MLK_TEST_ABICHECK_ABICHECK_X86_64_H */
