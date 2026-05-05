/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) 2026 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

// ---------------------------------------------------------------------------
// Overview
// ---------------------------------------------------------------------------
// MVE/Helium implementation of KeccakF1600x4_StateXORBytes.
//
// void KeccakF1600x4_StateXORBytes(state, d0, d1, d2, d3, offset, length)
//
// Reads 'length' plain bytes from each of four input buffers (d0..d3),
// splits every byte into its even and odd bits (bit-interleaving), and
// XORs the result into the Keccak state starting at byte 'offset'.
//
// ---------------------------------------------------------------------------
// Bit-interleaving background
// ---------------------------------------------------------------------------
// Each 64-bit Keccak lane is stored as two 32-bit words:
//   even half -- bits 0, 2, 4, ..., 62 of the lane
//   odd half  -- bits 1, 3, 5, ..., 63 of the lane
// This representation allows 64-bit lane rotations (used in the Keccak
// round function) to be implemented as pairs of 32-bit rotations.
//
// Batched (x4) processing:
//   Four Keccak instances are processed as a batch.  Their states are
//   stored interleaved in a single 800-byte buffer: first the even
//   halves of all 25 lanes (400 bytes), then the odd halves (400 bytes).
//   Within each 16-byte row, the four u32 words correspond to
//   instances 0..3 of the same lane, enabling SIMD-parallel operations
//   across all four instances.
//
// State memory layout (25 lanes x 4 instances x 2 halves):
//   S[i][l]_even/odd = even/odd half of lane l, instance i  (u32)
//   Each row is 16 bytes (one Q-register).
//   Offset  Contents
//     0     S[0][ 0]_even, S[1][ 0]_even, S[2][ 0]_even, S[3][ 0]_even
//    16     S[0][ 1]_even, S[1][ 1]_even, S[2][ 1]_even, S[3][ 1]_even
//    ...
//   384     S[0][24]_even, S[1][24]_even, S[2][24]_even, S[3][24]_even
//   400     S[0][ 0]_odd,  S[1][ 0]_odd,  S[2][ 0]_odd,  S[3][ 0]_odd
//   416     S[0][ 1]_odd,  S[1][ 1]_odd,  S[2][ 1]_odd,  S[3][ 1]_odd
//    ...
//   784     S[0][24]_odd,  S[1][24]_odd,  S[2][24]_odd,  S[3][24]_odd
//
// ---------------------------------------------------------------------------
// Three-phase structure
// ---------------------------------------------------------------------------
//   Prologue -- if offset is not 8-byte aligned, absorb
//               min(length, 8-(offset%8)) bytes via predicated byte loads.
//   Main     -- process full 8-byte groups via word-level gather loads,
//               bit-interleave, then VEOR into even/odd state halves.
//   Tail     -- absorb remaining <8 bytes via predicated byte loads.

#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X4) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

.thumb
.syntax unified
.text

// ---------------------------------------------------------------------------
// Interleave macros
// ---------------------------------------------------------------------------

// interleave_odds: in-place SWAR bit permutation that compacts odd-numbered
// bits of each byte/halfword/word in \t toward the upper half, preparing the
// odd half of the bit-interleaved representation.
// Inputs:  \t (data)
// Outputs: \t (odd bits compacted; per 32b lane: lo16=bytes 0..3, hi16=4..7)
// Clobbers: \u
.macro interleave_odds t, u
    vshl.u8     \u, \t, #2       // u = t[5..0],00
    vsri.u8     \t, \u, #1       // t = t[7],u[6..0]  => t = t[7],t[5..0],0
    vshl.u8     \u, \t, #3       // stage 2 across nibbles
    vsri.u8     \t, \u, #2
    vshl.u8     \u, \t, #4       // stage 3 across bytes
    vsri.u8     \t, \u, #3
    vshl.u16    \u, \t, #8       // widen within halfwords
    vsri.u8     \t, \u, #4
    vshl.u32    \u, \t, #16      // widen within words
    vsri.u16    \t, \u, #8
.endm

// interleave_evens: in-place SWAR bit permutation that compacts even-numbered
// bits of each byte/halfword/word in \t toward the lower half, preparing the
// even half of the bit-interleaved representation.
// Inputs:  \t (data)
// Outputs: \t (even bits compacted; per 32b lane: lo16=bytes 0..3, hi16=4..7)
// Clobbers: \u
.macro interleave_evens t, u
    vshr.u8     \u, \t, #2       // stage 1 within bytes
    vsli.u8     \t, \u, #1       // t = ((t >> 1) & 0x7E7E7E7E) | (t & 0x01010101)
    vshr.u8     \u, \t, #3       // stage 2 within nibbles
    vsli.u8     \t, \u, #2       // t = ((t >> 2) & 0x1C1C1C1C) | (t & 0x03030303)
    vshr.u8     \u, \t, #4       // stage 3 across bytes
    vsli.u8     \t, \u, #3       // t = ((t >> 3) & 0x08080808) | (t & 0x07070707)
    vshr.u16    \u, \t, #8       // widen within halfwords
    vsli.u8     \t, \u, #4       // t = ((t >> 4) & 0x00F000F0) | (t & 0x000F000F)
    vshr.u32    \u, \t, #16      // widen within words
    vsli.u16    \t, \u, #8       // t = ((t >> 8) & 0x0000FF00) | (t & 0x000000FF)
.endm

// ---------------------------------------------------------------------------
// to_bit_interleaving_4x: split \qe/\qo (low/high 4 bytes per instance)
// into even and odd halves packed as:
//   \qe = even half (lo16: bytes 0..3, hi16: bytes 4..7)
//   \qo = odd half  (lo16: bytes 0..3, hi16: bytes 4..7)
// Inputs:  \qe = [d0l, d1l, d2l, d3l], \qo = [d0h, d1h, d2h, d3h]
// Outputs: \qe (even half), \qo (odd half)
// Clobbers: \qt0, \qt1, \qt2
// ---------------------------------------------------------------------------
.macro to_bit_interleaving_4x qe, qo, qt0, qt1, qt2
    vmov \qt0, \qe
    vmov \qt1, \qo
    interleave_evens \qe, \qt2        // pack even bits in qe (low 16: d?l, high 16: d?h)
    interleave_evens \qt1, \qt2       // pack even bits from the high-half vector
    vsli.32          \qe, \qt1, #16   // merge: qe = [even(lo16), even(hi16)]
    interleave_odds  \qt0, \qt2       // pack odd bits from original qe
    interleave_odds  \qo, \qt2        // pack odd bits from original qo
    vsri.32          \qo, \qt0, #16   // merge: qo = [odd(lo16), odd(hi16)]
.endm

// ---------------------------------------------------------------------------
// transpose_streams_to_lanes: rearrange four per-instance vectors (q0..q3,
// each holding 8 bytes in its low 64 bits) into two vectors:
//   q0 = [d0l, d1l, d2l, d3l]  (low  4 bytes of each instance)
//   q1 = [d0h, d1h, d2h, d3h]  (high 4 bytes of each instance)
// Clobbers: q2, q3, p0, r0
//
// Vectors:             ||           q0          ||           q1          ||           q2          ||           q3          ||
// Elements:            || d0l | d0h |  0  |  0  || d1l | d1h |  0  |  0  || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
// ---------------------------------------------------------------------------
.macro transpose_streams_to_lanes
    vmov d1, d4          // || d0l | d0h | d2l | d2h || d1l | d1h |  0  |  0  || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vmov d3, d6          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vrev64.u32 q2, q0    // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d0h | d0l | d2h | d2l || d3l | d3h |  0  |  0  ||
    vrev64.u32 q3, q1    // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d0h | d0l | d2h | d2l || d1h | d1l | d3h | d3l ||
    mov r0, #0x0F0F      // predicate: select lower 4 bytes within each 64b half
    vmsr p0, r0
    vpsel q0, q0, q3     // q0 = [d0l, d1l, d2l, d3l]
    vpsel q1, q2, q1     // q1 = [d0h, d1h, d2h, d3h]
.endm

// ---------------------------------------------------------------------------
// xor_lane_and_store_postinc: XOR one lane into state with post-increment.
// rSE / rSO are current pointers to the even / odd state halves.
// ---------------------------------------------------------------------------
.macro xor_lane_and_store_postinc qE, qO, qS0, qS1, rSE, rSO
    vldrw.u32   \qS0, [\rSE]         // load 16B from even half
    vldrw.u32   \qS1, [\rSO]         // load 16B from odd half
    veor.u32    \qS0, \qS0, \qE
    veor.u32    \qS1, \qS1, \qO
    vstrw.u32   \qS0, [\rSE], #16    // post-inc by 16 bytes
    vstrw.u32   \qS1, [\rSO], #16
.endm


// ---------------------------------------------------------------------------
// void keccak_f1600_x4_state_xor_bytes_asm(void *state,
//                                          const unsigned char *data0,
//                                          const unsigned char *data1,
//                                          const unsigned char *data2,
//                                          const unsigned char *data3,
//                                          unsigned offset, unsigned length)
//
// AAPCS: r0=state, r1=d0, r2=d1, r3=d2, stack: d3, offset, length
// ---------------------------------------------------------------------------

.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_state_xor_bytes_asm)
.type MLK_ASM_NAMESPACE(keccak_f1600_x4_state_xor_bytes_asm), %function
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_state_xor_bytes_asm)
    .equ stack_offset, ((12-4+2)*4+(15-8+1)*8)
    push    {r4-r12, lr}
    vpush   {d8-d15}

    state               .req r0
    dp0                 .req r1
    dp1                 .req r2
    dp2                 .req r3
    dp3                 .req r4
    off                 .req r5
    length              .req r6
    rSO                 .req r7
    rSE                 .req r8
    lane_offset_bytes   .req r9
    off_full            .req r10
    mask                .req r11
    tmp                 .req r0
    nB                  .req lr

    qP                  .req q7

    qd0                 .req q0
    qd1                 .req q1
    qd2                 .req q2
    qd3                 .req q3

    qS0                 .req q4
    qS1                 .req q5

    ldr     dp3,      [sp, #stack_offset+0]
    ldr     off_full, [sp, #stack_offset+4]
    ldr     length,   [sp, #stack_offset+8]

    cmp     length,  #0
    beq     keccak_f1600_x4_state_xor_bytes_asm_exit

    and     off, off_full, #7
    bic     lane_offset_bytes, off_full, #7

    add     rSE, state, lane_offset_bytes, lsl #1
    add     rSO, rSE, #400

    // -----------------------------------------------------------------------
    // PROLOGUE: absorb min(len, 8-offset%8) bytes at the unaligned position
    // -----------------------------------------------------------------------
    cmp     off, #0
    beq     keccak_f1600_x4_state_xor_bytes_asm_pre_main

    // Subtract offset from data pointers so predicate window aligns
    subs dp0, dp0, off
    subs dp1, dp1, off
    subs dp2, dp2, off
    subs dp3, dp3, off

    // nB = min(length, 8 - off)
    rsb     nB, off, #8
    cmp     length, nB
    it      ls
    movls   nB, length
    subs    length, length, nB

    // Build predicate: nB active bytes shifted left by 'off'
    vctp.8 nB
    vmrs mask, p0
    lsl mask, mask, off
    vmsr p0, mask

    // Predicated byte loads (4 bytes per instance, post-increment by 4)
    vpstttt
    vldrbt.u8 qd0, [dp0], #4
    vldrbt.u8 qd1, [dp1], #4
    vldrbt.u8 qd2, [dp2], #4
    vldrbt.u8 qd3, [dp3], #4

    // Transpose from per-instance layout to per-lane layout
    transpose_streams_to_lanes

    // Bit-interleave (clobbers q2, q3, q4)
    to_bit_interleaving_4x q0, q1, q2, q3, q4

    // XOR into state (post-increments rSE/rSO by 16)
    xor_lane_and_store_postinc q0, q1, qS0, qS1, rSE, rSO

    // Build qP = {d0,d1,d2,d3} as u32 lanes for gather loads
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    cmp     length, #0
    beq     keccak_f1600_x4_state_xor_bytes_asm_exit
    b       keccak_f1600_x4_state_xor_bytes_asm_main_body

keccak_f1600_x4_state_xor_bytes_asm_pre_main:
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    mov     tmp, #4
    vsub.u32    qP, qP, tmp        // pre-bias so first [qP,#4]! lands at original ptr

keccak_f1600_x4_state_xor_bytes_asm_main_body:
    // -----------------------------------------------------------------------
    // MAIN: process full 8-byte lanes
    // -----------------------------------------------------------------------
    lsr     lr, length, #3
    wls     lr, lr, keccak_f1600_x4_state_xor_bytes_asm_main_loop_end
keccak_f1600_x4_state_xor_bytes_asm_main_loop_start:
    // Gather 8 bytes per instance (two u32 loads with post-increment)
    vldrw.u32 qd0, [qP, #4]!
    vldrw.u32 qd1, [qP, #4]!

    // Bit-interleave (clobbers q2, q3, q4)
    to_bit_interleaving_4x q0, q1, q2, q3, q4

    // XOR into state (post-increments rSE/rSO by 16)
    xor_lane_and_store_postinc q0, q1, qS0, qS1, rSE, rSO

    le      lr, keccak_f1600_x4_state_xor_bytes_asm_main_loop_start
keccak_f1600_x4_state_xor_bytes_asm_main_loop_end:

    // -----------------------------------------------------------------------
    // TAIL: absorb <8 remaining bytes at lane offset 0
    // -----------------------------------------------------------------------
    ands    length, length, #7
    beq     keccak_f1600_x4_state_xor_bytes_asm_exit

    // Recover scalar pointers from qP
    mov     tmp, #4
    vadd.u32    qP, qP, tmp
    vmov    dp0, dp2, qP[2], qP[0]
    vmov    dp1, dp3, qP[3], qP[1]

    vctp.8  length
    vpstttt
    vldrbt.u8   qd0, [dp0]
    vldrbt.u8   qd1, [dp1]
    vldrbt.u8   qd2, [dp2]
    vldrbt.u8   qd3, [dp3]

    // Transpose from per-instance layout to per-lane layout
    transpose_streams_to_lanes

    // Bit-interleave (clobbers q2, q3, q4)
    to_bit_interleaving_4x q0, q1, q2, q3, q4

    // XOR into state (post-increments rSE/rSO by 16)
    xor_lane_and_store_postinc qd0, qd1, qS0, qS1, rSE, rSO

keccak_f1600_x4_state_xor_bytes_asm_exit:
    vpop    {d8-d15}
    pop     {r4-r12, pc}
    .unreq state
    .unreq dp0
    .unreq dp1
    .unreq dp2
    .unreq dp3
    .unreq off
    .unreq length
    .unreq rSO
    .unreq rSE
    .unreq lane_offset_bytes
    .unreq off_full
    .unreq mask
    .unreq tmp
    .unreq nB
    .unreq qP
    .unreq qd0
    .unreq qd1
    .unreq qd2
    .unreq qd3
    .unreq qS0
    .unreq qS1

/* simpasm: footer-start */
#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
