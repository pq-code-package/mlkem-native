/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) 2026 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

// -----------------------------------------------------------------------------
// Overview and data layout
// -----------------------------------------------------------------------------

#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X1) && \
    defined(MLK_USE_FIPS202_X1_EXTRACT_BYTES_NATIVE) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/armv81m/src/state_extract_bytes_x1_mve_asm.S using scripts/simpasm. Do not modify it directly.
 */

.thumb
.syntax unified

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_state_extract_bytes_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_state_extract_bytes_asm)

        push.w	{r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
        mov.w	r6, #0x4
        mov.w	r7, #0x10
        cmp	r3, #0x0
        beq.w	keccak_f1600_x1_state_extract_bytes_asm_exit @ imm = #0x1b0
        and	r5, r2, #0xf
        bic	r9, r2, #0xf
        add	r0, r9
        cmp	r5, #0x0
        beq	keccak_f1600_x1_state_extract_bytes_asm_pre_main @ imm = #0x9c
        subs	r1, r1, r5
        rsb.w	lr, r5, #0x10
        cmp	r3, lr
        it	ls
        movls	lr, r3
        subs.w	r3, r3, lr
        vldrw.u32	q0, [r0], #16
        movw	r4, #0xf0f
        vmsr	p0, r4
        vrev32.16	q1, q0
        vrev64.32	q2, q1
        vrev64.32	q3, q0
        vpsel	q0, q0, q2
        vpsel	q1, q3, q1
        vsli.32	q0, q0, #0x8
        vsli.16	q0, q0, #0x4
        vsli.8	q0, q0, #0x1
        vqdmulh.s8	q2, q0, r7
        vsli.8	q0, q2, #0x4
        vqdmulh.s8	q2, q0, r6
        vsli.8	q0, q2, #0x6
        vsli.32	q1, q1, #0x8
        vsli.16	q1, q1, #0x4
        vsli.8	q1, q1, #0x1
        vqdmulh.s8	q2, q1, r7
        vsli.8	q1, q2, #0x4
        vqdmulh.s8	q2, q1, r6
        vsli.8	q1, q2, #0x6
        mov.w	r4, #0x55
        vdup.8	q2, r4
        vand	q0, q0, q2
        vand	q1, q1, q2
        vshl.i32	q1, q1, #0x1
        vorr	q0, q1, q0
        vctp.8	lr
        vmrs	r11, p0
        lsl.w	r11, r11, r5
        vmsr	p0, r11
        vpst	
        vstrbt.8	q0, [r1], #16
        cmp	r3, #0x0
        beq.w	keccak_f1600_x1_state_extract_bytes_asm_exit @ imm = #0x104

keccak_f1600_x1_state_extract_bytes_asm_pre_main:
        lsr.w	lr, r3, #0x4
        wls	lr, lr, keccak_f1600_x1_state_extract_bytes_asm_main_loop_end @ imm = #0x78

keccak_f1600_x1_state_extract_bytes_asm_main_loop_start:
        vldrw.u32	q0, [r0], #16
        movw	r4, #0xf0f
        vmsr	p0, r4
        vrev32.16	q1, q0
        vrev64.32	q2, q1
        vrev64.32	q3, q0
        vpsel	q0, q0, q2
        vpsel	q1, q3, q1
        vsli.32	q0, q0, #0x8
        vsli.16	q0, q0, #0x4
        vsli.8	q0, q0, #0x1
        vqdmulh.s8	q2, q0, r7
        vsli.8	q0, q2, #0x4
        vqdmulh.s8	q2, q0, r6
        vsli.8	q0, q2, #0x6
        vsli.32	q1, q1, #0x8
        vsli.16	q1, q1, #0x4
        vsli.8	q1, q1, #0x1
        vqdmulh.s8	q2, q1, r7
        vsli.8	q1, q2, #0x4
        vqdmulh.s8	q2, q1, r6
        vsli.8	q1, q2, #0x6
        mov.w	r4, #0x55
        vdup.8	q2, r4
        vand	q0, q0, q2
        vand	q1, q1, q2
        vshl.i32	q1, q1, #0x1
        vorr	q0, q1, q0
        vstrw.32	q0, [r1], #16
        le	lr, keccak_f1600_x1_state_extract_bytes_asm_main_loop_start @ imm = #-0x78

keccak_f1600_x1_state_extract_bytes_asm_main_loop_end:
        ands	r3, r3, #0xf
        cmp	r3, #0x0
        beq	keccak_f1600_x1_state_extract_bytes_asm_exit @ imm = #0x7a
        vldrw.u32	q0, [r0], #16
        movw	r4, #0xf0f
        vmsr	p0, r4
        vrev32.16	q1, q0
        vrev64.32	q2, q1
        vrev64.32	q3, q0
        vpsel	q0, q0, q2
        vpsel	q1, q3, q1
        vsli.32	q0, q0, #0x8
        vsli.16	q0, q0, #0x4
        vsli.8	q0, q0, #0x1
        vqdmulh.s8	q2, q0, r7
        vsli.8	q0, q2, #0x4
        vqdmulh.s8	q2, q0, r6
        vsli.8	q0, q2, #0x6
        vsli.32	q1, q1, #0x8
        vsli.16	q1, q1, #0x4
        vsli.8	q1, q1, #0x1
        vqdmulh.s8	q2, q1, r7
        vsli.8	q1, q2, #0x4
        vqdmulh.s8	q2, q1, r6
        vsli.8	q1, q2, #0x6
        mov.w	r4, #0x55
        vdup.8	q2, r4
        vand	q0, q0, q2
        vand	q1, q1, q2
        vshl.i32	q1, q1, #0x1
        vorr	q0, q1, q0
        vctp.8	r3
        vpst	
        vstrbt.8	q0, [r1], #16

keccak_f1600_x1_state_extract_bytes_asm_exit:
        pop.w	{r4, r5, r6, r7, r8, r9, r10, r11, r12, pc}
        nop

MLK_ASM_FN_SIZE(keccak_f1600_x1_state_extract_bytes_asm)

#endif /* MLK_FIPS202_ARMV81M_NEED_X1 && \
          MLK_USE_FIPS202_X1_EXTRACT_BYTES_NATIVE && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
