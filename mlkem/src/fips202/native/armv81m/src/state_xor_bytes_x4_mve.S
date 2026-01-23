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
 *   dev/fips202/armv81m/src/state_xor_bytes_x4_mve.S using scripts/simpasm. Do not modify it directly.
 */

.thumb
.syntax unified

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_state_xor_bytes_aligned)
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_state_xor_bytes_aligned)

        push	{r4, lr}
        vpush	{d8, d9, d10, d11, d12, d13, d14, d15}
        add.w	r2, r1, #0x190
        mov.w	r3, #0x4
        vsub.i32	q4, q0, r3
        wls	lr, r0, keccak_f1600_x4_state_xor_bytes_aligned_loop_end @ imm = #0x2c

keccak_f1600_x4_state_xor_bytes_aligned_loop_start:
        vldrw.u32	q0, [q4, #4]!
        vldrw.u32	q1, [q4, #4]!
        mov	r4, lr
        bl	keccak_f1600_x4_state_xor_bytes_aligned_to_bit_interleaving @ imm = #0x28
        mov	lr, r4
        vldrw.u32	q2, [r1, #16]
        vldrw.u32	q3, [r2, #16]
        veor	q2, q2, q0
        veor	q3, q3, q1
        vstrw.32	q2, [r1, #16]!
        vstrw.32	q3, [r2, #16]!
        le	lr, keccak_f1600_x4_state_xor_bytes_aligned_loop_start @ imm = #-0x2c

keccak_f1600_x4_state_xor_bytes_aligned_loop_end:
        vadd.i32	q0, q4, r3
        vpop	{d8, d9, d10, d11, d12, d13, d14, d15}
        pop	{r4, pc}

keccak_f1600_x4_state_xor_bytes_aligned_to_bit_interleaving:
        vpush	{d8, d9}
        vshl.i32	q7, q0, #0x0
        vshl.i32	q2, q0, #0x0
        vshl.i32	q6, q1, #0x0
        vshl.i32	q0, q1, #0x0
        vshl.i8	q3, q7, #0x2
        vsri.8	q7, q3, #0x1
        vshr.u8	q1, q2, #0x2
        vsli.8	q2, q1, #0x1
        vshl.i8	q5, q6, #0x2
        vsri.8	q6, q5, #0x1
        vshr.u8	q4, q0, #0x2
        vsli.8	q0, q4, #0x1
        vshl.i8	q5, q7, #0x3
        vsri.8	q7, q5, #0x2
        vshr.u8	q1, q2, #0x3
        vsli.8	q2, q1, #0x2
        vshl.i8	q3, q6, #0x3
        vsri.8	q6, q3, #0x2
        vshr.u8	q5, q0, #0x3
        vsli.8	q0, q5, #0x2
        vshl.i8	q1, q7, #0x4
        vsri.8	q7, q1, #0x3
        vshr.u8	q5, q2, #0x4
        vsli.8	q2, q5, #0x3
        vshl.i8	q5, q6, #0x4
        vsri.8	q6, q5, #0x3
        vshr.u8	q5, q0, #0x4
        vsli.8	q0, q5, #0x3
        vshl.i16	q4, q7, #0x8
        vsri.8	q7, q4, #0x4
        vshr.u16	q3, q2, #0x8
        vsli.8	q2, q3, #0x4
        vshl.i16	q1, q6, #0x8
        vsri.8	q6, q1, #0x4
        vshr.u16	q3, q0, #0x8
        vsli.8	q0, q3, #0x4
        vshl.i32	q3, q7, #0x10
        vsri.16	q7, q3, #0x8
        vshr.u32	q4, q2, #0x10
        vsli.16	q2, q4, #0x8
        vshl.i32	q3, q6, #0x10
        vsri.16	q6, q3, #0x8
        vshr.u32	q4, q0, #0x10
        vsli.16	q0, q4, #0x8
        vsri.32	q6, q7, #0x10
        vsli.32	q2, q0, #0x10
        vshl.i32	q1, q6, #0x0
        vshl.i32	q0, q2, #0x0
        vpop	{d8, d9}
        bx	lr
        nop

#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
