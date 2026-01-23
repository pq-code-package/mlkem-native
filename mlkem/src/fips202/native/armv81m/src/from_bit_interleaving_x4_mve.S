/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) 2025 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X4) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/armv81m/src/from_bit_interleaving_x4_mve.S using scripts/simpasm. Do not modify it directly.
 */

.thumb
.syntax unified

.text
.balign 4
.global MLK_ASM_NAMESPACE(from_bit_interleaving_4x)
MLK_ASM_FN_SYMBOL(from_bit_interleaving_4x)

        push.w	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
        vpush	{d8, d9, d10, d11, d12, d13, d14, d15}

from_bit_interleaving_4x_start:
        vshr.u32	q2, q0, #0x10
        mov.w	r6, #0x55
        vsli.32	q0, q0, #0x8
        vshr.u32	q6, q1, #0x10
        vsli.32	q1, q1, #0x8
        vsli.32	q2, q2, #0x8
        vsli.16	q0, q0, #0x4
        vsli.32	q6, q6, #0x8
        vsli.16	q1, q1, #0x4
        vsli.16	q2, q2, #0x4
        vshr.u8	q5, q0, #0x3
        vsli.8	q0, q5, #0x4
        vsli.16	q6, q6, #0x4
        vshr.u8	q7, q1, #0x3
        vsli.8	q1, q7, #0x4
        vshr.u8	q5, q2, #0x3
        vsli.8	q2, q5, #0x4
        vshr.u8	q4, q0, #0x2
        vsli.8	q0, q4, #0x3
        vshr.u8	q3, q6, #0x3
        vsli.8	q6, q3, #0x4
        vshr.u8	q7, q1, #0x2
        vsli.8	q1, q7, #0x3
        vshr.u8	q4, q2, #0x2
        vsli.8	q2, q4, #0x3
        vshr.u8	q5, q0, #0x1
        vsli.8	q0, q5, #0x2
        vshr.u8	q7, q6, #0x2
        vsli.8	q6, q7, #0x3
        vshr.u8	q5, q1, #0x1
        vsli.8	q1, q5, #0x2
        vshr.u8	q4, q2, #0x1
        vsli.8	q2, q4, #0x2
        vdup.8	q4, r6
        vand	q7, q0, q4
        vshr.u8	q3, q6, #0x1
        vsli.8	q6, q3, #0x2
        vand	q1, q1, q4
        vand	q3, q2, q4
        vand	q6, q6, q4
        vshl.i32	q2, q1, #0x1
        vorr	q0, q7, q2
        vshl.i32	q2, q6, #0x1
        vorr	q1, q3, q2

from_bit_interleaving_4x_exit:
        vpop	{d8, d9, d10, d11, d12, d13, d14, d15}
        pop.w	{r4, r5, r6, r7, r8, r9, r10, r11, pc}

#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
