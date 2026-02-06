/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) 2026 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

// ---------------------------------------------------------------------------
// Overview
// ---------------------------------------------------------------------------
// MVE/Helium implementation: de-interleave the bit-sliced Keccak state back
// into four parallel byte streams (inverse of state_xor_bytes_x4_mve.S).
//
// void KeccakF1600x4_StateExtractBytes(state, d0, d1, d2, d3, offset, length)
//
// Three-phase structure:
//   Prologue -- extract min(length, 8-(offset%8)) bytes from the unaligned
//               tail of the first lane via predicated byte stores.
//   Main     -- process full 8-byte groups: load E/O lanes, de-interleave,
//               scatter-store via qP.
//   Tail     -- extract <8 remaining bytes at lane offset 0 via predicated
//               byte stores.
//
// State memory layout (bit-interleaved, 4 streams):
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
//   - E occupies 25 lanes x 16 bytes = 400 bytes, followed by O at +400.
//   - Each 8 input bytes per stream map to one 16-byte E lane and one 16-byte
//     O lane.  Within each lane the four u32 words are streams 0..3.
//   - Per u32: lo16 = bit-plane for bytes [0..3], hi16 = bytes [4..7].

#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X4) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

.thumb
.syntax unified
.text

// ---------------------------------------------------------------------------
// deinterleave_even: inverse of the even-bit compaction.  Inflates the even
// bit-plane stored in \e back into byte positions.
// Inputs:  \e (compacted even bits)
// Outputs: \e (even bits expanded to byte positions, odd bits are garbage)
// Clobbers: \tmp
// ---------------------------------------------------------------------------
.macro deinterleave_even e, tmp
    // Inflate e                              +------+-----------+-----------+-----------+
    // Single-element annotation follows.  e: |   X  |     X     | l[0],l[1] | l[2],l[3] |
    vsli.u32    \e, \e, #8              // e: |   X  | l[0],l[1] | l[2],l[3] | l[2],l[3] |
    vsli.u16    \e, \e, #4              // e: | l[0] | l[1],l[1] | l[3],l[2] | l[3],l[3] |
    //                                        +------+-----------+-----------+-----------+
    // Now, expand the lower bits  e: | XXXX3210 | tmp: | XXXXXXXX |
    vsli.u8     \e, \e, #1    //   e: | XXX32100 | tmp: | XXXXXXXX |  (start re-packing low bits)
    vshr.u8     \tmp, \e, #3  //   e: | XXX32100 | tmp: | XXXXXX32 |
    vsli.u8     \e, \tmp, #4  //   e: | XX322100 | tmp: | XXXXXX32 |  (assemble nibbles)
    vshr.u8     \tmp, \e, #5  //   e: | XX322100 | tmp: | XXXXXXX3 |
    vsli.u8     \e, \tmp, #6  //   e: | X3322100 | tmp: | XXXXXXX3 |  (finalize byte compaction)
.endm

// ---------------------------------------------------------------------------
// from_bit_interleaving_4x: reconstruct byte vectors from bit-interleaved
// even/odd planes.
// Inputs:  q0 = Even plane, q1 = Odd plane
//          (per 32b lane: lo16 = bytes 0..3, hi16 = bytes 4..7)
// Outputs: q0 = [d0l, d1l, d2l, d3l] (low  4 bytes per stream)
//          q1 = [d0h, d1h, d2h, d3h] (high 4 bytes per stream)
// Clobbers: r0, q2, q3, q4
// ---------------------------------------------------------------------------
.macro from_bit_interleaving_4x
    //     +-----+-----+-----+-----+-----+-----+-----+-----+
    // q0: | E0l | E0u | E1l | E1u | E2l | E2u | E3l | E3u |
    // q1: | O0l | O0u | O1l | O1u | O2l | O2u | O3l | O3u |
    //     +-----+-----+-----+-----+-----+-----+-----+-----+
    // Clone and byte-swap to get upper halves into position
    vrev32.u16     q2, q0
    vrev32.u16     q3, q1
    // De-interleave lower evens / lower odds
    deinterleave_even q0, q4
    deinterleave_even q1, q4
    // q0 and q1 now hold valid even-position bits but garbage in odd positions.
    // Build mask 0x55..55 (01010101b) to isolate even-bit positions, then
    // shift the odd plane left by 1 and OR to reconstruct the original bytes.
    mov          r0, #0x55
    vdup.u8      q4, r0
    vand.u32     q0, q0, q4
    vand.u32     q1, q1, q4
    vshl.u32     q1, q1, #1
    vorr         q0, q0, q1       // q0 = low bytes reconstructed
    // De-interleave upper evens / upper odds
    deinterleave_even q2, q1
    deinterleave_even q3, q1
    vand.u32     q1, q2, q4       // reuse mask still in q4
    vand.u32     q3, q3, q4
    vshl.u32     q3, q3, #1
    vorr         q1, q1, q3       // q1 = high bytes reconstructed
.endm

// ---------------------------------------------------------------------------
// transpose_lanes_to_streams: rearrange two lane-ordered vectors into four
// per-stream vectors (inverse of transpose_streams_to_lanes).
//   q0 = [d0l, d1l, d2l, d3l]  ->  q0 = [d0l, d0h, ?, ?]
//   q1 = [d0h, d1h, d2h, d3h]  ->  q1 = [d1l, d1h, ?, ?]
//                                   q2 = [d2l, d2h, ?, ?]
//                                   q3 = [d3l, d3h, ?, ?]
// Clobbers: q2, q3, p0, r0
//
// Vectors:             ||           q0          ||           q1          ||           q2          ||           q3          ||
// Elements:            || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h ||                       ||                       ||
// ---------------------------------------------------------------------------
.macro transpose_lanes_to_streams
    vrev64.u32 q2, q0    // || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l ||                       ||
    vrev64.u32 q3, q1    // || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    mov r0, #0x0F0F
    vmsr p0, r0
    vpsel q0, q0, q3     // || d0l | d0h | d2l | d2h || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    vpsel q1, q2, q1     // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    vmov d4, d1          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h | d3l | d2l || d1h | d0h | d3h | d2h ||
    vmov d6, d3          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h | d3l | d2l || d3l | d3h | d3h | d2h ||
.endm


// ---------------------------------------------------------------------------
// void keccak_f1600_x4_state_extract_bytes_asm(void *state,
//                                              unsigned char *data0,
//                                              unsigned char *data1,
//                                              unsigned char *data2,
//                                              unsigned char *data3,
//                                              unsigned offset,
//                                              unsigned length)
//
// AAPCS: r0=state, r1=d0, r2=d1, r3=d2, stack: d3, offset, length
// ---------------------------------------------------------------------------
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_state_extract_bytes_asm)
.type MLK_ASM_NAMESPACE(keccak_f1600_x4_state_extract_bytes_asm), %function
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_state_extract_bytes_asm)
    .equ stack_offset, ((12-4+2)*4+(15-8+1)*8)
    push    {r4-r12, lr}
    vpush   {d8-d15}

    state             .req r0
    dp0               .req r1
    dp1               .req r2
    dp2               .req r3
    dp3               .req r4
    off               .req r5
    length            .req r6
    rSO               .req r7
    rSE               .req r8
    lane_offset_bytes .req r9
    off_full          .req r10
    mask              .req r11
    tmp               .req r12
    nB                .req lr

    qP                .req q7
    qd0               .req q0
    qd1               .req q1
    qd2               .req q2
    qd3               .req q3

    ldr     dp3,      [sp, #stack_offset+0]
    ldr     off_full, [sp, #stack_offset+4]
    ldr     length,   [sp, #stack_offset+8]

    cmp     length,  #0
    beq     keccak_f1600_x4_state_extract_bytes_asm_exit

    and     off, off_full, #7
    bic     lane_offset_bytes, off_full, #7

    add     rSE, state, lane_offset_bytes, lsl #1
    add     rSO, rSE, #400

    // -----------------------------------------------------------------------
    // PROLOGUE: extract min(len, 8-offset%8) bytes from the unaligned lane
    // -----------------------------------------------------------------------
    cmp     off, #0
    beq     keccak_f1600_x4_state_extract_bytes_asm_pre_main

    // Load one E/O lane pair from state (post-increment rSE/rSO by 16)
    vldrw.u32 qd0, [rSE], #16
    vldrw.u32 qd1, [rSO], #16

    // De-interleave (clobbers r0, q2, q3, q4)
    from_bit_interleaving_4x

    // Transpose from per-lane to per-stream layout
    transpose_lanes_to_streams

    // nB = min(length, 8 - off)
    rsb     nB, off, #8
    cmp     length, nB
    it      ls
    movls   nB, length

    // Build predicate: nB active bytes shifted left by 'off'
    vctp.8 nB
    vmrs mask, p0
    lsl mask, mask, off
    vmsr p0, mask

    // Subtract offset from data pointers so predicate window aligns
    subs dp0, dp0, off
    subs dp1, dp1, off
    subs dp2, dp2, off
    subs dp3, dp3, off

    // Predicated byte stores (post-increment by 4)
    vpstttt
    vstrbt.u8 qd0, [dp0], #4
    vstrbt.u8 qd1, [dp1], #4
    vstrbt.u8 qd2, [dp2], #4
    vstrbt.u8 qd3, [dp3], #4

    subs    length, length, nB
    cmp     length, #0
    beq     keccak_f1600_x4_state_extract_bytes_asm_exit

    // Build qP from updated scalar pointers
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    b       keccak_f1600_x4_state_extract_bytes_asm_main_body

keccak_f1600_x4_state_extract_bytes_asm_pre_main:
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    mov     tmp, #4
    vsub.u32    qP, qP, tmp

    // -----------------------------------------------------------------------
    // MAIN: process full 8-byte lanes
    // -----------------------------------------------------------------------
keccak_f1600_x4_state_extract_bytes_asm_main_body:
    lsr     lr, length, #3
    wls     lr, lr, keccak_f1600_x4_state_extract_bytes_asm_main_loop_end
keccak_f1600_x4_state_extract_bytes_asm_main_loop_start:
    vldrw.u32 qd0, [rSE], #16
    vldrw.u32 qd1, [rSO], #16

    // De-interleave (clobbers r0, q2, q3, q4)
    from_bit_interleaving_4x

    // Scatter-store 8 bytes per stream (two u32 stores with post-increment)
    vstrw.u32   qd0, [qP, #4]!
    vstrw.u32   qd1, [qP, #4]!

    le      lr, keccak_f1600_x4_state_extract_bytes_asm_main_loop_start
keccak_f1600_x4_state_extract_bytes_asm_main_loop_end:

    // -----------------------------------------------------------------------
    // TAIL: extract <8 remaining bytes at lane offset 0
    // -----------------------------------------------------------------------
    ands    length, length, #7
    beq     keccak_f1600_x4_state_extract_bytes_asm_exit

    // Recover scalar pointers from qP
    mov     tmp, #4
    vadd.u32    qP, qP, tmp
    vmov    dp0, dp2, qP[2], qP[0]
    vmov    dp1, dp3, qP[3], qP[1]

    vldrw.u32 qd0, [rSE], #16
    vldrw.u32 qd1, [rSO], #16

    // De-interleave (clobbers r0, q2, q3, q4)
    from_bit_interleaving_4x

    // Transpose from per-lane to per-stream layout
    transpose_lanes_to_streams

    // Predicated byte stores for remaining bytes
    vctp.8 length
    vpstttt
    vstrbt.u8 qd0, [dp0], #4
    vstrbt.u8 qd1, [dp1], #4
    vstrbt.u8 qd2, [dp2], #4
    vstrbt.u8 qd3, [dp3], #4

keccak_f1600_x4_state_extract_bytes_asm_exit:
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

/* simpasm: footer-start */
#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
