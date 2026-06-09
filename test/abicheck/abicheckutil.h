/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef ABICHECKUTIL_H
#define ABICHECKUTIL_H

#include <stdint.h>
#include "../../mlkem/src/sys.h"

#if defined(MLK_SYS_AARCH64)

/* Aligned (MLK_ALIGN >= 16 bytes) so that the 128-bit ldp/stp q used by
 * asm_call_stub to load and store the neon members are well-aligned. */
struct MLK_ALIGN register_state
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

#elif defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)

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

extern MLK_SYSV_ABI
void asm_call_stub_x86_64(struct x86_64_register_state *input,
                          struct x86_64_register_state *output,
                          void (*function_ptr)(void));

#elif defined(MLK_SYS_PPC64LE)

/* PowerPC64 ELF v2 ABI register state.
 *
 * Layout must match ppc64le_callstub.S. Covers the full set of callee-saved
 * (non-volatile) registers the ABI requires a function to preserve:
 *   - GPRs r14-r31
 *   - FPRs f14-f31
 *   - VRs  v20-v31 (128-bit each)
 *   - condition register fields CR2, CR3, CR4
 * plus the volatile argument registers r3-r10 used to set up the call.
 *
 * Aligned so the stub's 128-bit vector loads/stores (lvx/stvx) are aligned. */
struct MLK_ALIGN ppc64le_register_state
{
  uint64_t gpr_arg[8]; /* r3-r10 (argument/volatile, for call setup) */
  uint64_t gpr_nv[18]; /* r14-r31 (non-volatile) */
  uint64_t fpr[18];    /* f14-f31 (non-volatile, low 64 bits) */
  uint64_t vr[12][2];  /* v20-v31 (non-volatile, full 128-bit) */
  uint64_t cr;         /* condition register (CR2-CR4 fields checked) */
};

int check_ppc64le_elfv2_compliance(struct ppc64le_register_state *before,
                                   struct ppc64le_register_state *after);
void init_ppc64le_register_state(struct ppc64le_register_state *state);

extern void asm_call_stub_ppc64le(struct ppc64le_register_state *input,
                                  struct ppc64le_register_state *output,
                                  void (*function_ptr)(void));

#endif /* !MLK_SYS_AARCH64 && !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) && \
          MLK_SYS_PPC64LE */

#endif /* !ABICHECKUTIL_H */
