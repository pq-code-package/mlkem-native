/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_TEST_ABICHECK_ABICHECK_PPC64LE_H
#define MLK_TEST_ABICHECK_ABICHECK_PPC64LE_H

#include "../abicheck_common.h"

#if defined(MLK_SYS_PPC64LE)

/* PowerPC64 ELF v2 ABI register state.
 *
 * Layout must match callstub_ppc64le.S. Covers the full set of callee-saved
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
  uint32_t cr;         /* condition register (CR2-CR4 fields checked).
                          Sized to match the stub's `stw` width: the upper 4
                          bytes would otherwise be uninitialized. */
};

int check_ppc64le_elfv2_compliance(struct ppc64le_register_state *before,
                                   struct ppc64le_register_state *after,
                                   int quiet);
void init_ppc64le_register_state(struct ppc64le_register_state *state);

extern void asm_call_stub_ppc64le(struct ppc64le_register_state *input,
                                  struct ppc64le_register_state *output,
                                  void (*function_ptr)(void));

#endif /* MLK_SYS_PPC64LE */

#endif /* !MLK_TEST_ABICHECK_ABICHECK_PPC64LE_H */
