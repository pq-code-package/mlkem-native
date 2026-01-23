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
 *   dev/fips202/armv81m/src/load_bytes_in_lane_x4_mve.S using scripts/simpasm. Do not modify it directly.
 */

.thumb
.syntax unified

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_load_bytes_in_lane)
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_load_bytes_in_lane)

        push.w	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
        vpush	{d8, d9, d10, d11}
        mov.w	r2, #0x0
        vidup.u8	q1, r2, #0x1
        mov.w	r3, #0x1
        lsl.w	r3, r3, r0
        sub.w	r3, r3, #0x1
        lsl.w	r3, r3, r1
        vmsr	p0, r3
        vsub.i32	q0, q0, r1
        vmov	r4, r6, q0[2], q0[0]
        vmov	r5, r7, q0[3], q0[1]
        vpstttt	
        vldrbt.u8	q2, [r4, q1]
        vldrbt.u8	q3, [r5, q1]
        vldrbt.u8	q4, [r6, q1]
        vldrbt.u8	q5, [r7, q1]
        vmov	r8, r9, d4
        vmov	r10, r11, d8
        vmov	q0[2], q0[0], r8, r10
        vmov	q1[2], q1[0], r9, r11
        vmov	r8, r9, d6
        vmov	r10, r11, d10
        vmov	q0[3], q0[1], r8, r10
        vmov	q1[3], q1[1], r9, r11
        vpop	{d8, d9, d10, d11}
        pop.w	{r4, r5, r6, r7, r8, r9, r10, r11, pc}

#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
