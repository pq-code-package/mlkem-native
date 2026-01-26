.syntax unified
.thumb
.text
/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
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

// -----------------------------------------------------------------------------
// Interleave macros
// -----------------------------------------------------------------------------
.macro interleave_odds t, u
    vshl.u8     \u, \t, #2     // 
    vsri.u8     \t, \u, #1
    vshl.u8     \u, \t, #3
    vsri.u8     \t, \u, #2
    vshl.u8     \u, \t, #4
    vsri.u8     \t, \u, #3
    vshl.u16    \u, \t, #8
    vsri.u8     \t, \u, #4
    vshl.u32    \u, \t, #16
    vsri.u16    \t, \u, #8

.endm

.macro interleave_evens t, u
    vshr.u8     \u, \t, #2       // 
    vsli.u8     \t, \u, #1       // t = ((t >> 1) & 0x7E7E7E7E) | (t & 0x01010101)
    vshr.u8     \u, \t, #3       // 
    vsli.u8     \t, \u, #2       // t = ((t >> 2) & 0x1C1C1C1C) | (t & 0x03030303)
    vshr.u8     \u, \t, #4       //
    vsli.u8     \t, \u, #3       // t = ((t >> 3) & 0x08080808) | (t & 0x07070707)
    vshr.u16    \u, \t, #8       //
    vsli.u8     \t, \u, #4       // t = ((t >> 4) & 0x00F000F0) | (t & 0x000F000F)
    vshr.u32    \u, \t, #16      //
    vsli.u16    \t, \u, #8       // t = ((t >> 16) & 0x0000FF00) | (t & 0x000000FF)
.endm

.align 8
.type _internal_to_bit_interleaving_4x, %function
_internal_to_bit_interleaving_4x:
    // NOTE: this function is internal only because it does not
    // preserve q4. Caller beware!
    // vpush   {d8 - d9}
to_bit_interleaving_4x_start:
    vshl.u32 q2, q0, #0
    vshl.u32 q3, q1, #0
    interleave_evens q0, q4
    interleave_evens q3, q4
    vsli.32          q0, q3, #16
    interleave_odds  q2, q4
    interleave_odds  q1, q4
    vsri.32          q1, q2, #16
to_bit_interleaving_4x_exit:
    // vpop {d8 - d9}
    bx lr

// -----------------------------------------------------------------------------
// XOR one lane into state, using post-increment on stores (no explicit add).
// rSE / rSO are current pointers to stateE/stateO (interleaved layout).
// -----------------------------------------------------------------------------
.macro XOR_LANE_AND_STORE_POSTINC qE, qO, qS0, qS1, rSE, rSO
    vldrw.u32   \qS0, [\rSE]
    vldrw.u32   \qS1, [\rSO]
    veor.u32    \qS0, \qS0, \qE
    veor.u32    \qS1, \qS1, \qO
    vstrw.u32   \qS0, [\rSE], #16     // post-inc by 16 bytes
    vstrw.u32   \qS1, [\rSO], #16
.endm

// -----------------------------------------------------------------------------
// void KeccakF1600x4_StateXORBytes(void *state,
//                                 const uint8_t *d0, *d1, *d2, *d3,
//                                 uint32_t offset, uint32_t length)
//
// AAPCS-ish assumption:
//   r0=state, r1=d0, r2=d1, r3=d2, stack: d3, offset, length
// -----------------------------------------------------------------------------
.global KeccakF1600x4_StateXORBytes
.type   KeccakF1600x4_StateXORBytes,%function
KeccakF1600x4_StateXORBytes:
    .equ stack_offset, ((12-4+2)*4+(15-8+1)*8)
    push    {r4-r12, lr}
    vpush   {d8-d15}

    state               .req r0
    dp0                 .req r1
    dp1                 .req r2
    dp2                 .req r3
    dp3                 .req r4
    off_full            .req r10
    length              .req r6
    rSO                 .req r7
    rSE                 .req r8
    nB                  .req lr
    lane_offset_bytes   .req r9
    off                 .req r5
    mask                .req r11
    tmp                 .req r0

    // ---- Vector naming ----
    qIdx                .req q6        // vidup.u8 result (0..15)
    qP                  .req q7        // vector of 4 data pointers

    qd0                 .req q0        // general data regs
    qd1                 .req q1
    qd2                 .req q2
    qd3                 .req q3

    qS0                 .req q4        // state temp (even)
    qS1                 .req q5        // state temp (odd) OR scratch; be consistent



    ldr     dp3,       [sp, #stack_offset+0]
    ldr     off_full, [sp, #stack_offset+4]
    ldr     length,   [sp, #stack_offset+8]

    cmp     length,  #0             // if len==0 done
    beq     9f

    and     off, off_full, #7
    bic     lane_offset_bytes, off_full, #7

    add     rSE, state, lane_offset_bytes, lsl #1
    add     rSO, rSE, #400

    // -------------------------------------------------------------------------
    // PROLOGUE: if (offset_in_lane != 0) absorb min(len, 8-offset) into one lane
    // -------------------------------------------------------------------------
    cmp     off, #0                 // if off==0 skip
    beq     1f
    // subtract the offset from the addresses to match the predicate
    subs dp0, dp0, off
    subs dp1, dp1, off
    subs dp2, dp2, off
    subs dp3, dp3, off

    // r0 = n = min(length, 8-off)
    rsb     nB, off, #8
    cmp     length, nB
    it      ls
    movls   nB, length

    // calculate the predicates
    // mask = (1 << length) - 1
    vctp.8 nB
    vmrs mask, p0
    // mask << offset
    lsl mask, mask, off
    vmsr p0, mask
    // now load the partial lanes
    vpstttt
    vldrbt.u8 qd0, [dp0], #4
    vldrbt.u8 qd1, [dp1], #4
    vldrbt.u8 qd2, [dp2], #4
    vldrbt.u8 qd3, [dp3], #4
    // vector transpose
    subs sp, sp, #64
    vst40.32 {qd0, qd1, qd2, qd3}, [sp]
    vst41.32 {qd0, qd1, qd2, qd3}, [sp]
    vst42.32 {qd0, qd1, qd2, qd3}, [sp]
    vst43.32 {qd0, qd1, qd2, qd3}, [sp]
    vldrw.u32 qd0, [sp, #0]
    vldrw.u32 qd1, [sp, #16]
    adds sp, sp, #64

    // Bit interleave
    // NOTE: q2,q3,q4 are dead here and not preserved.
    // preserve link register
    mov tmp, lr
    bl _internal_to_bit_interleaving_4x
    mov lr, tmp

    // XOR into state (stores post-increment rSE/rSO by 16)
                            // qE, qO, qS0, qS1, rSE, rSO
    XOR_LANE_AND_STORE_POSTINC q0, q1, qS0, qS1, rSE, rSO

    // length -= n
    subs    length, length, nB

    // Build qP = {d0,d1,d2,d3} as u32 lanes (vector of base addresses)    
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    cmp     length, #0
    beq     9f
    b       2f

1:
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    mov     tmp, #4
    vsub.u32    qP, qP, tmp
2:
    // -------------------------------------------------------------------------
    // MAIN BODY: process full 8-byte lanes while len >= 8 and within frame
    // -------------------------------------------------------------------------
    // Calculate the number of lanes to process
    lsr     lr, length, #3
    // Low-overhead loop
    wls     lr, lr, 5f
3:
    // Gather two u32 vectors from the 4 bases in q5, then bump pointers
    vldrw.u32 qd0, [qP, #4]!
    vldrw.u32 qd1, [qP, #4]!

    // Bit interleave
    // NOTE: q2,q3,q4 are dead here and not preserved.
    // preserve link register
    mov tmp, lr
    bl _internal_to_bit_interleaving_4x
    mov lr, tmp

    // XOR into state (stores post-increment rSE/rSO by 16)
                            // qE, qO, qS0, qS1, rSE, rSO
    XOR_LANE_AND_STORE_POSTINC q0, q1, qS0, qS1, rSE, rSO

    le      lr, 3b
5:
    // -------------------------------------------------------------------------
    // TAIL: if length remaining <8, absorb it at offset_in_lane=0
    // -------------------------------------------------------------------------

    // length &= 7
    // Placeholder: if r6 == 0, done.
    ands    length, length, #7
    cbz     length, 9f

    // Tail via predicated byte loads like prologue, but off=0 (no base adjust)
    mov     tmp, #4
    vadd.u32    qP, qP, tmp
    vmov    dp0, dp2, qP[2], qP[0]
    vmov    dp1, dp3, qP[3], qP[1]

    // Build qIdx = [0..15] for byte indexed loads

    vctp.8  length
    vpstttt
    vldrbt.u8   qd0, [dp0]
    vldrbt.u8   qd1, [dp1]
    vldrbt.u8   qd2, [dp2]
    vldrbt.u8   qd3, [dp3]

    // Scalar repack (tail is rare)
    subs sp, sp, #64
    vst40.32 {qd0, qd1, qd2, qd3}, [sp]
    vst41.32 {qd0, qd1, qd2, qd3}, [sp]
    vst42.32 {qd0, qd1, qd2, qd3}, [sp]
    vst43.32 {qd0, qd1, qd2, qd3}, [sp]
    vldrw.u32 qd0, [sp, #0]
    vldrw.u32 qd1, [sp, #16]
    adds sp, sp, #64

    // Bit interleave
    // NOTE: q2,q3,q4 are dead here and not preserved.
    mov tmp, lr
    bl _internal_to_bit_interleaving_4x
    mov lr, tmp

    // XOR into state (stores post-increment rSE/rSO by 16)
                            // qE, qO, qS0, qS1, rSE, rSO
    XOR_LANE_AND_STORE_POSTINC qd0, qd1, qS0, qS1, rSE, rSO

9:
    vpop    {d8-d15}
    pop     {r4-r12, pc}

.size KeccakF1600x4_StateXORBytes, .-KeccakF1600x4_StateXORBytes
