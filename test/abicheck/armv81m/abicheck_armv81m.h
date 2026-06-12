/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_TEST_ABICHECK_ABICHECK_ARMV81M_H
#define MLK_TEST_ABICHECK_ABICHECK_ARMV81M_H

#include "../abicheck_common.h"

#if defined(MLK_SYS_ARMV81M_MVE)

/* Armv8.1-M (Thumb-2, AAPCS32) register state.
 *
 * Layout must match callstub_armv81m.S. Covers the full GPR set r0-r12 (so
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

#endif /* MLK_SYS_ARMV81M_MVE */

#endif /* !MLK_TEST_ABICHECK_ABICHECK_ARMV81M_H */
