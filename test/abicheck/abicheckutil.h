/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef ABICHECKUTIL_H
#define ABICHECKUTIL_H

#include <stdint.h>
#define MLK_BUILD_INTERNAL
#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "../../mlkem/mlkem_native_config.h"
#endif
#include "../../mlkem/src/sys.h"

/* Return codes for check_<kernel>(), shared with abicheck.c. */
#define MLK_ABICHECK_PASSED 0  /* No violation in any iteration. */
#define MLK_ABICHECK_SKIPPED 1 /* Host lacks the required ISA capability. */
#define MLK_ABICHECK_FAILED                        \
  (-1) /* Violation observed, or arch unsupported. \
        */

/* Randomized trials per kernel; each trial reseeds the register state and
 * pointer-arg buffers. */
#define MLK_ABICHECK_NUM_TESTS 3

/* Quiet suppresses the per-violation diagnostic (used by the selftest, whose
 * corrupters always fire). */
#define MLK_ABICHECK_VERBOSE 0
#define MLK_ABICHECK_QUIET 1

/* Registry entry shared by all per-arch checks_{arch}_all.h headers and
 * consumed by abicheck.c. */
typedef struct
{
  const char *name;
  int (*check_func)(void);
} abicheck_entry_t;

#if defined(MLK_SYS_AARCH64)

/* MLK_ALIGN-aligned so the stub's 128-bit ldp/stp q on neon[] are aligned. */
struct MLK_ALIGN register_state
{
  uint64_t gpr[32];     /* x0-x30 */
  uint64_t neon[32][2]; /* q0-q31 (full 128-bit NEON registers as two 64-bit
                           values) */
};

/* quiet: MLK_ABICHECK_VERBOSE or MLK_ABICHECK_QUIET (see top of file). */
int check_aarch64_aapcs_compliance(struct register_state *before,
                                   struct register_state *after, int quiet);
void init_register_state(struct register_state *state);

extern void asm_call_stub_aarch64(struct register_state *input,
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
                                 struct x86_64_register_state *after,
                                 int quiet);
void init_x86_64_register_state(struct x86_64_register_state *state);

extern MLK_SYSV_ABI
void asm_call_stub_x86_64_sysv(
    struct x86_64_register_state *input, struct x86_64_register_state *output,
                               MLK_SYSV_ABI
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

#elif defined(MLK_SYS_ARMV81M_MVE)

/* Armv8.1-M (Thumb-2, AAPCS32) register state.
 *
 * Layout must match armv81m_callstub.S. Covers the full GPR set r0-r12 (so
 * the stub can seed every available register with random data) plus all
 * eight 128-bit MVE Q-registers q0-q7 (= d0-d15 on the floating-point side).
 * AAPCS32 callee-saved set: r4-r11 plus q4-q7 (= d8-d15).
 *
 * gpr is sized to 16 entries so mve[] (which follows) is 16-byte aligned;
 * slots 13..15 are unused. The struct is MLK_ALIGN-aligned so the stub's
 * 128-bit vldrw.u32 / vstrw.32 are aligned. */
struct MLK_ALIGN armv81m_register_state
{
  uint32_t gpr[16];   /* r0-r12 in slots 0..12; slots 13..15 are padding */
  uint32_t mve[8][4]; /* q0-q7 (full 128-bit MVE registers as four 32-bit
                         lanes each) */
};

int check_armv81m_aapcs32_compliance(struct armv81m_register_state *before,
                                     struct armv81m_register_state *after,
                                     int quiet);
void init_armv81m_register_state(struct armv81m_register_state *state);

extern void asm_call_stub_armv81m(struct armv81m_register_state *input,
                                  struct armv81m_register_state *output,
                                  void (*function_ptr)(void));

#endif /* !MLK_SYS_AARCH64 && !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) && \
          !MLK_SYS_PPC64LE && MLK_SYS_ARMV81M_MVE */

#endif /* !ABICHECKUTIL_H */
