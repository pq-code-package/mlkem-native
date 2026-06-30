/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Meta-test for the ABI checker.
 *
 * For each supported architecture, this file iterates over a registry of
 * "corrupter" functions. Each corrupter is a tiny hand-written assembly
 * stub that violates the platform calling convention by clobbering exactly
 * one callee-saved register (without restoring it). We call each through
 * the architecture's call stub, run the matching check_*_compliance, and
 * assert the checker reports the expected violation count - that proves
 * the checker actually fires.
 *
 * The corrupter sources live in selftest_<arch>.S; the registry below maps
 * each one to a human-readable name. We do not assert *which* register was
 * flagged (that would require parsing stderr); strict-equal-count plus a
 * known-good no-op is sufficient to validate the checker's polarity, basic
 * plumbing, and that it doesn't over-count.
 *
 * If any selftest fails, abicheck.c bails before running the kernel
 * registry, on the principle that a broken checker's verdicts cannot be
 * trusted.
 */

#include <stdio.h>

#include "abicheck_common.h"
#include "selftest.h"

/* Per-arch register-state structs + declarations; each is guarded on its arch
 * macro, so only the active arch's definitions materialize. selftest.c
 * dispatches across all arches, so it pulls in every arch's header. */
#include "aarch64/abicheck_aarch64.h"
#include "armv81m/abicheck_armv81m.h"
#include "ppc64le/abicheck_ppc64le.h"
#include "x86_64/abicheck_x86_64.h"

/* Shared registry shape: per-arch tables of (name, fn-ptr, expected count).
 * On x86_64 Windows-MinGW the corrupter symbols are MLK_SYSV_ABI; we store
 * them as plain void(*)(void) here and re-qualify with a cast at the call
 * site below, matching the per-kernel check_*.c pattern. */
typedef struct
{
  const char *name;
  void (*fn)(void);
  int expected_violations; /* 0 for noop, >=1 for corrupters */
} selftest_entry_t;

/* Run a per-arch selftest pass: iterate `entries`, for each call the stub
 * with a freshly-initialised input state, run the compliance check, and
 * count cases where the violation count doesn't match expectations
 * (catches both polarity flips and over-counting). */
#define SELFTEST_RUN_ARCH(arch_label, state_t, init_fn, stub_fn, check_fn,    \
                          entries, fn_cast)                                   \
  do                                                                          \
  {                                                                           \
    state_t input_state, output_state;                                        \
    const selftest_entry_t *e;                                                \
    for (e = (entries); e->name != NULL; e++)                                 \
    {                                                                         \
      int violations;                                                         \
      init_fn(&input_state);                                                  \
      stub_fn(&input_state, &output_state, fn_cast e->fn);                    \
      violations = check_fn(&input_state, &output_state, MLK_ABICHECK_QUIET); \
      if (violations != e->expected_violations)                               \
      {                                                                       \
        fprintf(stderr,                                                       \
                "selftest FAIL: " arch_label                                  \
                " %s: expected %d violations, got %d\n",                      \
                e->name, e->expected_violations, violations);                 \
        failures++;                                                           \
      }                                                                       \
    }                                                                         \
  } while (0)

#if defined(MLK_SYS_AARCH64)

/* Corrupter declarations. Defined in selftest_aarch64.S. */
extern void selftest_aarch64_noop(void);
/* x18 is the AArch64 platform register (Darwin-reserved, ELF-unused);
 * the call stub does not seed it on Apple, but we still verify that
 * kernels leave it alone. The corrupter is registered only on
 * non-Apple builds because on Darwin user code must not touch x18. */
#if !defined(__APPLE__)
extern void selftest_aarch64_corrupt_x18(void);
#endif
/* GPRs: callee-saved set is x19-x29. */
extern void selftest_aarch64_corrupt_x19(void);
extern void selftest_aarch64_corrupt_x20(void);
extern void selftest_aarch64_corrupt_x21(void);
extern void selftest_aarch64_corrupt_x22(void);
extern void selftest_aarch64_corrupt_x23(void);
extern void selftest_aarch64_corrupt_x24(void);
extern void selftest_aarch64_corrupt_x25(void);
extern void selftest_aarch64_corrupt_x26(void);
extern void selftest_aarch64_corrupt_x27(void);
extern void selftest_aarch64_corrupt_x28(void);
extern void selftest_aarch64_corrupt_x29(void);
/* SIMD: lower 64 bits of d8-d15 are callee-saved. */
extern void selftest_aarch64_corrupt_d8(void);
extern void selftest_aarch64_corrupt_d9(void);
extern void selftest_aarch64_corrupt_d10(void);
extern void selftest_aarch64_corrupt_d11(void);
extern void selftest_aarch64_corrupt_d12(void);
extern void selftest_aarch64_corrupt_d13(void);
extern void selftest_aarch64_corrupt_d14(void);
extern void selftest_aarch64_corrupt_d15(void);

static const selftest_entry_t aarch64_gpr_entries[] = {
    {"noop", selftest_aarch64_noop, 0},
#if !defined(__APPLE__)
    {"corrupt_x18", selftest_aarch64_corrupt_x18, 1},
#endif
    {"corrupt_x19", selftest_aarch64_corrupt_x19, 1},
    {"corrupt_x20", selftest_aarch64_corrupt_x20, 1},
    {"corrupt_x21", selftest_aarch64_corrupt_x21, 1},
    {"corrupt_x22", selftest_aarch64_corrupt_x22, 1},
    {"corrupt_x23", selftest_aarch64_corrupt_x23, 1},
    {"corrupt_x24", selftest_aarch64_corrupt_x24, 1},
    {"corrupt_x25", selftest_aarch64_corrupt_x25, 1},
    {"corrupt_x26", selftest_aarch64_corrupt_x26, 1},
    {"corrupt_x27", selftest_aarch64_corrupt_x27, 1},
    {"corrupt_x28", selftest_aarch64_corrupt_x28, 1},
    {"corrupt_x29", selftest_aarch64_corrupt_x29, 1},
    {NULL, NULL, 0},
};

static const selftest_entry_t aarch64_neon_entries[] = {
    {"corrupt_d8", selftest_aarch64_corrupt_d8, 1},
    {"corrupt_d9", selftest_aarch64_corrupt_d9, 1},
    {"corrupt_d10", selftest_aarch64_corrupt_d10, 1},
    {"corrupt_d11", selftest_aarch64_corrupt_d11, 1},
    {"corrupt_d12", selftest_aarch64_corrupt_d12, 1},
    {"corrupt_d13", selftest_aarch64_corrupt_d13, 1},
    {"corrupt_d14", selftest_aarch64_corrupt_d14, 1},
    {"corrupt_d15", selftest_aarch64_corrupt_d15, 1},
    {NULL, NULL, 0},
};

#elif defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)

/* Defined in selftest_x86_64.S. The .S symbols are MLK_SYSV_ABI-qualified;
 * we store them as plain void(*)(void) and re-qualify the cast at the call
 * site (see SELFTEST_RUN_ARCH below). */
extern MLK_SYSV_ABI
void selftest_x86_64_noop(void);
extern MLK_SYSV_ABI
void selftest_x86_64_corrupt_rbx(void);
extern MLK_SYSV_ABI
void selftest_x86_64_corrupt_rbp(void);
extern MLK_SYSV_ABI
void selftest_x86_64_corrupt_r12(void);
extern MLK_SYSV_ABI
void selftest_x86_64_corrupt_r13(void);
extern MLK_SYSV_ABI
void selftest_x86_64_corrupt_r14(void);
extern MLK_SYSV_ABI
void selftest_x86_64_corrupt_r15(void);

static const selftest_entry_t x86_64_entries[] = {
    {"noop", (void (*)(void))selftest_x86_64_noop, 0},
    {"corrupt_rbx", (void (*)(void))selftest_x86_64_corrupt_rbx, 1},
    {"corrupt_rbp", (void (*)(void))selftest_x86_64_corrupt_rbp, 1},
    {"corrupt_r12", (void (*)(void))selftest_x86_64_corrupt_r12, 1},
    {"corrupt_r13", (void (*)(void))selftest_x86_64_corrupt_r13, 1},
    {"corrupt_r14", (void (*)(void))selftest_x86_64_corrupt_r14, 1},
    {"corrupt_r15", (void (*)(void))selftest_x86_64_corrupt_r15, 1},
    {NULL, NULL, 0},
};

#elif defined(MLK_SYS_PPC64LE)

extern void selftest_ppc64le_noop(void);
/* GPRs r14..r31 (18) */
extern void selftest_ppc64le_corrupt_r14(void);
extern void selftest_ppc64le_corrupt_r15(void);
extern void selftest_ppc64le_corrupt_r16(void);
extern void selftest_ppc64le_corrupt_r17(void);
extern void selftest_ppc64le_corrupt_r18(void);
extern void selftest_ppc64le_corrupt_r19(void);
extern void selftest_ppc64le_corrupt_r20(void);
extern void selftest_ppc64le_corrupt_r21(void);
extern void selftest_ppc64le_corrupt_r22(void);
extern void selftest_ppc64le_corrupt_r23(void);
extern void selftest_ppc64le_corrupt_r24(void);
extern void selftest_ppc64le_corrupt_r25(void);
extern void selftest_ppc64le_corrupt_r26(void);
extern void selftest_ppc64le_corrupt_r27(void);
extern void selftest_ppc64le_corrupt_r28(void);
extern void selftest_ppc64le_corrupt_r29(void);
extern void selftest_ppc64le_corrupt_r30(void);
extern void selftest_ppc64le_corrupt_r31(void);
/* FPRs f14..f31 (18) */
extern void selftest_ppc64le_corrupt_f14(void);
extern void selftest_ppc64le_corrupt_f15(void);
extern void selftest_ppc64le_corrupt_f16(void);
extern void selftest_ppc64le_corrupt_f17(void);
extern void selftest_ppc64le_corrupt_f18(void);
extern void selftest_ppc64le_corrupt_f19(void);
extern void selftest_ppc64le_corrupt_f20(void);
extern void selftest_ppc64le_corrupt_f21(void);
extern void selftest_ppc64le_corrupt_f22(void);
extern void selftest_ppc64le_corrupt_f23(void);
extern void selftest_ppc64le_corrupt_f24(void);
extern void selftest_ppc64le_corrupt_f25(void);
extern void selftest_ppc64le_corrupt_f26(void);
extern void selftest_ppc64le_corrupt_f27(void);
extern void selftest_ppc64le_corrupt_f28(void);
extern void selftest_ppc64le_corrupt_f29(void);
extern void selftest_ppc64le_corrupt_f30(void);
extern void selftest_ppc64le_corrupt_f31(void);
/* VRs v20..v31 (12) */
extern void selftest_ppc64le_corrupt_v20(void);
extern void selftest_ppc64le_corrupt_v21(void);
extern void selftest_ppc64le_corrupt_v22(void);
extern void selftest_ppc64le_corrupt_v23(void);
extern void selftest_ppc64le_corrupt_v24(void);
extern void selftest_ppc64le_corrupt_v25(void);
extern void selftest_ppc64le_corrupt_v26(void);
extern void selftest_ppc64le_corrupt_v27(void);
extern void selftest_ppc64le_corrupt_v28(void);
extern void selftest_ppc64le_corrupt_v29(void);
extern void selftest_ppc64le_corrupt_v30(void);
extern void selftest_ppc64le_corrupt_v31(void);
/* CR2/CR3/CR4 corrupters - one per non-volatile CR field so the full
 * MLK_PPC_CR_NV_MASK is exercised, not just CR2's nibble. */
extern void selftest_ppc64le_corrupt_cr2(void);
extern void selftest_ppc64le_corrupt_cr3(void);
extern void selftest_ppc64le_corrupt_cr4(void);

static const selftest_entry_t ppc64le_entries[] = {
    {"noop", selftest_ppc64le_noop, 0},
    {"corrupt_r14", selftest_ppc64le_corrupt_r14, 1},
    {"corrupt_r15", selftest_ppc64le_corrupt_r15, 1},
    {"corrupt_r16", selftest_ppc64le_corrupt_r16, 1},
    {"corrupt_r17", selftest_ppc64le_corrupt_r17, 1},
    {"corrupt_r18", selftest_ppc64le_corrupt_r18, 1},
    {"corrupt_r19", selftest_ppc64le_corrupt_r19, 1},
    {"corrupt_r20", selftest_ppc64le_corrupt_r20, 1},
    {"corrupt_r21", selftest_ppc64le_corrupt_r21, 1},
    {"corrupt_r22", selftest_ppc64le_corrupt_r22, 1},
    {"corrupt_r23", selftest_ppc64le_corrupt_r23, 1},
    {"corrupt_r24", selftest_ppc64le_corrupt_r24, 1},
    {"corrupt_r25", selftest_ppc64le_corrupt_r25, 1},
    {"corrupt_r26", selftest_ppc64le_corrupt_r26, 1},
    {"corrupt_r27", selftest_ppc64le_corrupt_r27, 1},
    {"corrupt_r28", selftest_ppc64le_corrupt_r28, 1},
    {"corrupt_r29", selftest_ppc64le_corrupt_r29, 1},
    {"corrupt_r30", selftest_ppc64le_corrupt_r30, 1},
    {"corrupt_r31", selftest_ppc64le_corrupt_r31, 1},
    {"corrupt_f14", selftest_ppc64le_corrupt_f14, 1},
    {"corrupt_f15", selftest_ppc64le_corrupt_f15, 1},
    {"corrupt_f16", selftest_ppc64le_corrupt_f16, 1},
    {"corrupt_f17", selftest_ppc64le_corrupt_f17, 1},
    {"corrupt_f18", selftest_ppc64le_corrupt_f18, 1},
    {"corrupt_f19", selftest_ppc64le_corrupt_f19, 1},
    {"corrupt_f20", selftest_ppc64le_corrupt_f20, 1},
    {"corrupt_f21", selftest_ppc64le_corrupt_f21, 1},
    {"corrupt_f22", selftest_ppc64le_corrupt_f22, 1},
    {"corrupt_f23", selftest_ppc64le_corrupt_f23, 1},
    {"corrupt_f24", selftest_ppc64le_corrupt_f24, 1},
    {"corrupt_f25", selftest_ppc64le_corrupt_f25, 1},
    {"corrupt_f26", selftest_ppc64le_corrupt_f26, 1},
    {"corrupt_f27", selftest_ppc64le_corrupt_f27, 1},
    {"corrupt_f28", selftest_ppc64le_corrupt_f28, 1},
    {"corrupt_f29", selftest_ppc64le_corrupt_f29, 1},
    {"corrupt_f30", selftest_ppc64le_corrupt_f30, 1},
    {"corrupt_f31", selftest_ppc64le_corrupt_f31, 1},
    {"corrupt_v20", selftest_ppc64le_corrupt_v20, 1},
    {"corrupt_v21", selftest_ppc64le_corrupt_v21, 1},
    {"corrupt_v22", selftest_ppc64le_corrupt_v22, 1},
    {"corrupt_v23", selftest_ppc64le_corrupt_v23, 1},
    {"corrupt_v24", selftest_ppc64le_corrupt_v24, 1},
    {"corrupt_v25", selftest_ppc64le_corrupt_v25, 1},
    {"corrupt_v26", selftest_ppc64le_corrupt_v26, 1},
    {"corrupt_v27", selftest_ppc64le_corrupt_v27, 1},
    {"corrupt_v28", selftest_ppc64le_corrupt_v28, 1},
    {"corrupt_v29", selftest_ppc64le_corrupt_v29, 1},
    {"corrupt_v30", selftest_ppc64le_corrupt_v30, 1},
    {"corrupt_v31", selftest_ppc64le_corrupt_v31, 1},
    {"corrupt_cr2", selftest_ppc64le_corrupt_cr2, 1},
    {"corrupt_cr3", selftest_ppc64le_corrupt_cr3, 1},
    {"corrupt_cr4", selftest_ppc64le_corrupt_cr4, 1},
    {NULL, NULL, 0},
};

#elif defined(MLK_SYS_ARMV81M_MVE)

extern void selftest_armv81m_noop(void);
extern void selftest_armv81m_corrupt_r4(void);
extern void selftest_armv81m_corrupt_r5(void);
extern void selftest_armv81m_corrupt_r6(void);
extern void selftest_armv81m_corrupt_r7(void);
extern void selftest_armv81m_corrupt_r8(void);
extern void selftest_armv81m_corrupt_r9(void);
extern void selftest_armv81m_corrupt_r10(void);
extern void selftest_armv81m_corrupt_r11(void);
extern void selftest_armv81m_corrupt_q4(void);
extern void selftest_armv81m_corrupt_q5(void);
extern void selftest_armv81m_corrupt_q6(void);
extern void selftest_armv81m_corrupt_q7(void);

static const selftest_entry_t armv81m_entries[] = {
    {"noop", selftest_armv81m_noop, 0},
    {"corrupt_r4", selftest_armv81m_corrupt_r4, 1},
    {"corrupt_r5", selftest_armv81m_corrupt_r5, 1},
    {"corrupt_r6", selftest_armv81m_corrupt_r6, 1},
    {"corrupt_r7", selftest_armv81m_corrupt_r7, 1},
    {"corrupt_r8", selftest_armv81m_corrupt_r8, 1},
    {"corrupt_r9", selftest_armv81m_corrupt_r9, 1},
    {"corrupt_r10", selftest_armv81m_corrupt_r10, 1},
    {"corrupt_r11", selftest_armv81m_corrupt_r11, 1},
    {"corrupt_q4", selftest_armv81m_corrupt_q4, 1},
    {"corrupt_q5", selftest_armv81m_corrupt_q5, 1},
    {"corrupt_q6", selftest_armv81m_corrupt_q6, 1},
    {"corrupt_q7", selftest_armv81m_corrupt_q7, 1},
    {NULL, NULL, 0},
};

#endif /* !MLK_SYS_AARCH64 && !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) && \
          !MLK_SYS_PPC64LE && MLK_SYS_ARMV81M_MVE */

int abicheck_selftest(void)
{
  int failures = 0;

#if defined(MLK_SYS_AARCH64)
  SELFTEST_RUN_ARCH("aarch64", struct aarch64_register_state,
                    init_aarch64_register_state, call_stub_aarch64,
                    check_aarch64_aapcs_compliance, aarch64_gpr_entries,
                    (void (*)(void)));

  /* The NEON corrupters execute vector instructions, so running them on a
   * host without NEON would fault instead of testing the ABI checker. */
  if (mlk_sys_check_capability(MLK_SYS_CAP_AARCH64_NEON))
  {
    SELFTEST_RUN_ARCH("aarch64", struct aarch64_register_state,
                      init_aarch64_register_state, call_stub_aarch64,
                      check_aarch64_aapcs_compliance, aarch64_neon_entries,
                      (void (*)(void)));
  }
#elif defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)
  SELFTEST_RUN_ARCH(
      "x86_64", struct x86_64_register_state, init_x86_64_register_state,
      asm_call_stub_x86_64_sysv, check_x86_64_sysv_compliance, x86_64_entries,
      (MLK_SYSV_ABI
       void (*)(void)));
#elif defined(MLK_SYS_PPC64LE)
  SELFTEST_RUN_ARCH("ppc64le", struct ppc64le_register_state,
                    init_ppc64le_register_state, asm_call_stub_ppc64le,
                    check_ppc64le_elfv2_compliance, ppc64le_entries,
                    (void (*)(void)));
#elif defined(MLK_SYS_ARMV81M_MVE)
  SELFTEST_RUN_ARCH("armv81m", struct armv81m_register_state,
                    init_armv81m_register_state, asm_call_stub_armv81m,
                    check_armv81m_aapcs32_compliance, armv81m_entries,
                    (void (*)(void)));
#else  /* !MLK_SYS_AARCH64 && !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) && \
          !MLK_SYS_PPC64LE && MLK_SYS_ARMV81M_MVE */
  /* No abicheck support on this architecture. */
#endif /* !MLK_SYS_AARCH64 && !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) && \
          !MLK_SYS_PPC64LE && !MLK_SYS_ARMV81M_MVE */

  return failures;
}
