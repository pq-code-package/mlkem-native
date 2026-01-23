/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) 2026 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

// -----------------------------------------------------------------------------
// Overview and data layout
// -----------------------------------------------------------------------------
// This file provides the MVE/Helium implementation that bit‑interleaves four
// parallel byte streams and XORs them into the Keccak state in the
// (even/odd)-bit‑sliced representation used by the 4x permutation.
//
// KeccakF1600x4_StateXORBytes(state, d0, d1, d2, d3, offset, length)
//   - Inputs: four byte streams d0..d3 and a byte count 'length'.
//   - Operation: starting at a notional byte 'offset' into the state, consume
//     'length' bytes from each stream and XOR them into 'state' after splitting
//     every input byte into its even and odd bit planes. For stream i, the even
//     plane is denoted e[i] and the odd plane o[i]. The function XORs e[i] into
//     the E region and o[i] into the O region.
//
// State memory layout (bit‑interleaved, 4 streams):
//   state + 000: E[0](0-3), E[1](0-3), E[2](0-3), E[3](0-3)
//   state + 016: E[0](4-7), E[1](4-7), E[2](4-7), E[3](4-7)
//   ...
//   state + 384: E[0](196-199), E[1](196-199), E[2](196-199), E[3](196-199)
//   state + 400:  O[0](0-3),  O[1](0-3),  O[2](0-3),  O[3](0-3)
//   state + 416:  O[0](4-7),  O[1](4-7),  O[2](4-7),  O[3](4-7)
//   ...
//   state + 784:  O[0](196-199), O[1](196-199), O[2](196-199), O[3](196-199)
//
// Notes on the layout:
//   - The state stores even (E) and odd (O) bit planes in two contiguous blocks.
//     E occupies 25 lanes × 16 bytes = 400 bytes, followed by O at +400.
//   - Each 8 input bytes per stream (bytes [0..7], then [8..15], ...) map to one
//     16‑byte E lane and one 16‑byte O lane. Within each 16‑byte lane the four
//     u32 words correspond to streams 0..3 respectively: E[0],E[1],E[2],E[3].
//   - For each u32, the lower 16 bits hold the bit‑plane for bytes [0..3] of the
//     current 8‑byte chunk; the upper 16 bits hold the bit‑plane for bytes [4..7].
//
// High‑level behaviour of KeccakF1600x4_StateXORBytes:
//   - Computes rSE = state + 2 * floor(offset/8) * 8 and rSO = rSE + 400, so
//     every 8 input bytes advance the E/O pointers by 16 bytes in memory.
//   - Prologue: if offset is not 8‑byte aligned, predicated byte‑gathers absorb
//     min(length, 8‑(offset mod 8)) bytes at the correct intra‑lane position.
//   - Main: processes as many full 8‑byte groups as possible via vector gathers,
//     bit‑interleaving to produce e[i]/o[i], then veor into E/O and post‑increment
//     rSE/rSO by 16.
//   - Tail: if remaining (<8) bytes exist, another predicated gather absorbs
//     them at intra‑lane offset 0.
//
// Bit‑interleaving details:
//   - interleave_evens/interleave_odds split even/odd bits within each u32 lane
//     using a standard sequence of shifts/masks. The helper
//     _internal_to_bit_interleaving_4x packs results so that, per‑lane, the low
//     16 bits represent bytes [0..3] and high 16 bits represent bytes [4..7].
//


#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X4) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/armv81m/src/state_extract_bytes_x4_mve.S using scripts/simpasm. Do not modify it directly.
 */

.thumb
.syntax unified

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_state_extract_bytes_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_state_extract_bytes_asm)

        push.w	{r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
        vpush	{d8, d9, d10, d11, d12, d13, d14, d15}
        ldr	r4, [sp, #0x68]
        ldr.w	r10, [sp, #0x6c]
        ldr	r6, [sp, #0x70]
        cmp	r6, #0x0
        beq.w	keccak_f1600_x4_state_extract_bytes_asm_exit @ imm = #0x118
        and	r5, r10, #0x7
        bic	r9, r10, #0x7
        add.w	r8, r0, r9, lsl #1
        add.w	r7, r8, #0x190
        cmp	r5, #0x0
        beq	keccak_f1600_x4_state_extract_bytes_asm_pre_main @ imm = #0x72
        vldrw.u32	q0, [r8], #16
        vldrw.u32	q1, [r7], #16
        bl	keccak_f1600_x4_state_extract_bytes_from_bit_interleaving_4x_start @ imm = #0x102
        vrev64.32	q2, q0
        vrev64.32	q3, q1
        movw	r0, #0xf0f
        vmsr	p0, r0
        vpsel	q0, q0, q3
        vpsel	q1, q2, q1
        vmov.f64	d4, d1
        vmov.f64	d6, d3
        rsb.w	lr, r5, #0x8
        cmp	r6, lr
        it	ls
        movls	lr, r6
        vctp.8	lr
        vmrs	r11, p0
        lsl.w	r11, r11, r5
        vmsr	p0, r11
        subs	r1, r1, r5
        subs	r2, r2, r5
        subs	r3, r3, r5
        subs	r4, r4, r5
        vpstttt	
        vstrbt.8	q0, [r1], #4
        vstrbt.8	q1, [r2], #4
        vstrbt.8	q2, [r3], #4
        vstrbt.8	q3, [r4], #4
        subs.w	r6, r6, lr
        cmp	r6, #0x0
        beq	keccak_f1600_x4_state_extract_bytes_asm_exit @ imm = #0x98
        vmov	q7[2], q7[0], r1, r3
        vmov	q7[3], q7[1], r2, r4
        b	keccak_f1600_x4_state_extract_bytes_asm_main_body @ imm = #0xe

keccak_f1600_x4_state_extract_bytes_asm_pre_main:
        vmov	q7[2], q7[0], r1, r3
        vmov	q7[3], q7[1], r2, r4
        mov.w	r12, #0x4
        vsub.i32	q7, q7, r12

keccak_f1600_x4_state_extract_bytes_asm_main_body:
        lsr.w	lr, r6, #0x3
        wls	lr, lr, keccak_f1600_x4_state_extract_bytes_asm_main_loop_end @ imm = #0x1c

keccak_f1600_x4_state_extract_bytes_asm_main_loop_start:
        vldrw.u32	q0, [r8], #16
        vldrw.u32	q1, [r7], #16
        mov	r12, lr
        bl	keccak_f1600_x4_state_extract_bytes_from_bit_interleaving_4x_start @ imm = #0x74
        mov	lr, r12
        vstrw.32	q0, [q7, #4]!
        vstrw.32	q1, [q7, #4]!
        le	lr, keccak_f1600_x4_state_extract_bytes_asm_main_loop_start @ imm = #-0x1c

keccak_f1600_x4_state_extract_bytes_asm_main_loop_end:
        ands	r6, r6, #0x7
        cmp	r6, #0x0
        beq	keccak_f1600_x4_state_extract_bytes_asm_exit @ imm = #0x52
        mov.w	r12, #0x4
        vadd.i32	q7, q7, r12
        vmov	r1, r3, q7[2], q7[0]
        vmov	r2, r4, q7[3], q7[1]
        vldrw.u32	q0, [r8], #16
        vldrw.u32	q1, [r7], #16
        bl	keccak_f1600_x4_state_extract_bytes_from_bit_interleaving_4x_start @ imm = #0x42
        vrev64.32	q2, q0
        vrev64.32	q3, q1
        movw	r0, #0xf0f
        vmsr	p0, r0
        vpsel	q0, q0, q3
        vpsel	q1, q2, q1
        vmov.f64	d4, d1
        vmov.f64	d6, d3
        vctp.8	r6
        vpstttt	
        vstrbt.8	q0, [r1], #4
        vstrbt.8	q1, [r2], #4
        vstrbt.8	q2, [r3], #4
        vstrbt.8	q3, [r4], #4

keccak_f1600_x4_state_extract_bytes_asm_exit:
        vpop	{d8, d9, d10, d11, d12, d13, d14, d15}
        pop.w	{r4, r5, r6, r7, r8, r9, r10, r11, r12, pc}
        nop

keccak_f1600_x4_state_extract_bytes_from_bit_interleaving_4x_start:
        vrev32.16	q2, q0
        vrev32.16	q3, q1
        vsli.32	q0, q0, #0x8
        vsli.16	q0, q0, #0x4
        vsli.8	q0, q0, #0x1
        vshr.u8	q4, q0, #0x3
        vsli.8	q0, q4, #0x4
        vshr.u8	q4, q0, #0x5
        vsli.8	q0, q4, #0x6
        vsli.32	q1, q1, #0x8
        vsli.16	q1, q1, #0x4
        vsli.8	q1, q1, #0x1
        vshr.u8	q4, q1, #0x3
        vsli.8	q1, q4, #0x4
        vshr.u8	q4, q1, #0x5
        vsli.8	q1, q4, #0x6
        mov.w	r0, #0x55
        vdup.8	q4, r0
        vand	q0, q0, q4
        vand	q1, q1, q4
        vshl.i32	q1, q1, #0x1
        vorr	q0, q0, q1
        vsli.32	q2, q2, #0x8
        vsli.16	q2, q2, #0x4
        vsli.8	q2, q2, #0x1
        vshr.u8	q1, q2, #0x3
        vsli.8	q2, q1, #0x4
        vshr.u8	q1, q2, #0x5
        vsli.8	q2, q1, #0x6
        vsli.32	q3, q3, #0x8
        vsli.16	q3, q3, #0x4
        vsli.8	q3, q3, #0x1
        vshr.u8	q1, q3, #0x3
        vsli.8	q3, q1, #0x4
        vshr.u8	q1, q3, #0x5
        vsli.8	q3, q1, #0x6
        vand	q1, q2, q4
        vand	q3, q3, q4
        vshl.i32	q3, q3, #0x1
        vorr	q1, q1, q3

keccak_f1600_x4_state_extract_bytes_from_bit_interleaving_4x_exit:
        bx	lr
        nop

#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
