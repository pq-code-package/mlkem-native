/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Armv8.1-M (Thumb-2, AAPCS32+MVE) selftest stubs.
 *
 * Each function clobbers exactly one callee-saved register and returns.
 * GPR corrupters use `mvn rN, rN` and Q-register corrupters use
 * `vmvn qN, qN`: both are bitwise NOT, always differ from input,
 * and need no scratch register.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

.text
.balign 4
.thumb
.syntax unified

/* The ELF Thumb linker needs `.type sym, %function` for every external
 * Thumb symbol so it can set the LSB of branch relocations from C
 * callers. Apple has no Armv8.1-M platform, so we emit the ELF form
 * unconditionally. */

.global selftest_armv81m_noop
.type selftest_armv81m_noop, %function
selftest_armv81m_noop:
        bx      lr

.macro define_corrupter name, body
.global \name
.type \name, %function
\name:
        \body
        bx      lr
.endm

define_corrupter selftest_armv81m_corrupt_r4,  "mvn r4,  r4"
define_corrupter selftest_armv81m_corrupt_r5,  "mvn r5,  r5"
define_corrupter selftest_armv81m_corrupt_r6,  "mvn r6,  r6"
define_corrupter selftest_armv81m_corrupt_r7,  "mvn r7,  r7"
define_corrupter selftest_armv81m_corrupt_r8,  "mvn r8,  r8"
define_corrupter selftest_armv81m_corrupt_r9,  "mvn r9,  r9"
define_corrupter selftest_armv81m_corrupt_r10, "mvn r10, r10"
define_corrupter selftest_armv81m_corrupt_r11, "mvn r11, r11"

/* Q-register corrupters. */
.macro corrupt_q name, qreg
.global \name
.type \name, %function
\name:
        vmvn    \qreg, \qreg
        bx      lr
.endm

corrupt_q selftest_armv81m_corrupt_q4, q4
corrupt_q selftest_armv81m_corrupt_q5, q5
corrupt_q selftest_armv81m_corrupt_q6, q6
corrupt_q selftest_armv81m_corrupt_q7, q7
