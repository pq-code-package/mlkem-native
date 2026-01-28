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
// interleave_odds: in-place SWAR bit permutation that compacts odd-numbered
// bits of each byte/halfword/word in \t toward the upper half, preparing the
// odd bit-plane. Uses vshl + vsri insertion per the semantics above.
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
    vsri.u16    \t, \u, #8       // odd bits compacted; per 32b lane: lo16=bytes0..3, hi16=4..7
.endm

// interleave_evens: in-place SWAR bit permutation that compacts even-numbered
// bits of each byte/halfword/word in \t toward the lower half, preparing the
// even bit-plane. Comments show the equivalent masks after each stage.
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

.align 8
.type _internal_to_bit_interleaving_4x, %function
_internal_to_bit_interleaving_4x:
    // NOTE: this function is internal only because it does not
    // preserve q4. Caller beware!
    // vpush   {d8 - d9}
to_bit_interleaving_4x_start:
    // Inputs on entry:
    //   q0 = [d0l, d1l, d2l, d3l] (bytes 0..3 of each stream, one per 32b lane)
    //   q1 = [d0h, d1h, d2h, d3h] (bytes 4..7 of each stream)
    // Output on return:
    //   q0 = Even bit-plane packed (lo16: bytes 0..3, hi16: bytes 4..7)
    //   q1 = Odd  bit-plane packed (lo16: bytes 0..3, hi16: bytes 4..7)
    // Clobbers: q2, q3, q4
    vshl.u32 q2, q0, #0
    vshl.u32 q3, q1, #0
    interleave_evens q0, q4           // pack even bits in q0 (low 16: d?l, high 16: d?h)
    interleave_evens q3, q4           // pack even bits from the high-half vector
    vsli.32          q0, q3, #16      // merge: q0 = [even(lo16), even(hi16)]
    interleave_odds  q2, q4           // pack odd bits from original q0
    interleave_odds  q1, q4           // pack odd bits from original q1
    vsri.32          q1, q2, #16      // merge: q1 = [odd(lo16), odd(hi16)]
to_bit_interleaving_4x_exit:
    // vpop {d8 - d9}
    bx lr

// -----------------------------------------------------------------------------
// XOR one lane into state, using post-increment on stores (no explicit add).
// rSE / rSO are current pointers to stateE/stateO (interleaved layout).
// -----------------------------------------------------------------------------
.macro XOR_LANE_AND_STORE_POSTINC qE, qO, qS0, qS1, rSE, rSO
    vldrw.u32   \qS0, [\rSE]         // load 16B from Even region
    vldrw.u32   \qS1, [\rSO]         // load 16B from Odd  region
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
// AAPCS assumption:
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



    ldr     dp3,      [sp, #stack_offset+0]
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
    // mask = (1 << nB) - 1 over 8-bit lanes, then shift by 'off'.
    // vctp.8 sets p0[0..nB-1]=1 (others 0). We read it as an integer mask,
    // left-shift to align the active bytes within the 8-byte lane, and write
    // it back to p0 to predicate the subsequent byte gathers.
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
    // Read as bytes and form two vectors with low/high halves for the 4 streams
    // There are 4 streams to read => partial vector transpose
    // Vectors:             ||           q0          ||           q1          ||           q2          ||           q3          ||
    // Elements:            || d0l | d0h |  0  |  0  || d1l | d1h |  0  |  0  || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vmov d1, d4          // || d0l | d0h | d2l | d2h || d1l | d1h |  0  |  0  || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vmov d3, d6          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vrev64.u32 q2, q0    // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d0h | d0l | d2h | d2l || d3l | d3h |  0  |  0  ||
    vrev64.u32 q3, q1    // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d0h | d0l | d2h | d2l || d1h | d1l | d3h | d3l ||
    mov r0, #0x0F0F      // predicate: select lower 4 bytes within each half
    vmsr p0, r0          // used by vpsel to stitch lanes from q{0,1,2,3}
    vpsel q0, q0, q3     // q0 = [d0l,d1l,d2l,d3l]
    vpsel q1, q2, q1     // q1 = [d0h,d1h,d2h,d3h]

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
    // qP is then consumed by gather loads with post-increment per-lane.
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    cmp     length, #0
    beq     9f
    b       2f

1:
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    mov     tmp, #4
    vsub.u32    qP, qP, tmp        // pre-bias so first [qP,#4]! lands at original ptr
2:
    // -------------------------------------------------------------------------
    // MAIN BODY: process full 8-byte lanes while len >= 8 and within frame
    // -------------------------------------------------------------------------
    // Calculate the number of full 8-byte lanes to process
    lsr     lr, length, #3
    // Low-overhead loop: wls/le use LR as the hardware loop counter
    wls     lr, lr, 5f
3:
    // Gather two u32 vectors (8B per stream) and bump per-stream pointers by 4
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

    le      lr, 3b                  // loop end, branch to 3b while LR>0
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

    vctp.8  length
    vpstttt
    vldrbt.u8   qd0, [dp0]
    vldrbt.u8   qd1, [dp1]
    vldrbt.u8   qd2, [dp2]
    vldrbt.u8   qd3, [dp3]

    // Read as bytes and form two vectors with low/high halves for the 4 streams
    // There are 4 streams to read => partial vector transpose
    // Vectors:             ||           q0          ||           q1          ||           q2          ||           q3          ||
    // Elements:            || d0l | d0h |  0  |  0  || d1l | d1h |  0  |  0  || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vmov d1, d4          // || d0l | d0h | d2l | d2h || d1l | d1h |  0  |  0  || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vmov d3, d6          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h |  0  |  0  || d3l | d3h |  0  |  0  ||
    vrev64.u32 q2, q0    // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d0h | d0l | d2h | d2l || d3l | d3h |  0  |  0  ||
    vrev64.u32 q3, q1    // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d0h | d0l | d2h | d2l || d1h | d1l | d3h | d3l ||
    mov r0, #0x0F0F      // predicate selects lower 4 bytes per 8B half
    vmsr p0, r0
    vpsel q0, q0, q3     // q0 = [d0l,d1l,d2l,d3l]
    vpsel q1, q2, q1     // q1 = [d0h,d1h,d2h,d3h]

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
    .unreq state
    .unreq dp0
    .unreq dp1
    .unreq dp2
    .unreq dp3
    .unreq off_full
    .unreq length
    .unreq rSO
    .unreq rSE
    .unreq nB
    .unreq lane_offset_bytes
    .unreq off
    .unreq mask
    .unreq tmp
    .unreq qIdx
    .unreq qP
    .unreq qd0
    .unreq qd1
    .unreq qd2
    .unreq qd3
    .unreq qS0
    .unreq qS1
.size KeccakF1600x4_StateXORBytes, .-KeccakF1600x4_StateXORBytes


.macro deinterleave_even e, tmp 
    // De-interleave even bits back into byte order (inverse of interleave_evens)
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

.align 8
.type _internal_from_bit_interleaving_4x, %function
_internal_from_bit_interleaving_4x:
_internal_from_bit_interleaving_4x_start:
    // Inputs on entry:
    //   q0 = Even plane (lo16: bytes 0..3, hi16: bytes 4..7) for streams 0..3
    //   q1 = Odd  plane (lo16: bytes 0..3, hi16: bytes 4..7) for streams 0..3
    // Output on return:
    //   q0..q3 contain 8 de-interleaved bytes per stream (see call sites)
    // Clobbers: r0, q2, q3, q4
    r    .req r0
    El   .req q0
    Ol   .req q1
    Eu   .req q2
    Ou   .req q3
    tmp  .req q4
    //     +-----+-----+-----+-----+-----+-----+-----+-----+
    // El: | E0l | E0u | E1l | E1u | E2l | E2u | E3l | E3u |
    // q1: | O0l | O0u | O1l | O1u | O2l | O2u | O3l | O3u |
    //     +-----+-----+-----+-----+-----+-----+-----+-----+
    // clone q0 into temp register and swap
    vrev32.u16     Eu, El
    // clone q1 into temp register and swap
    vrev32.u16     Ou, Ol
    // deinterleave lower evens into El
    deinterleave_even El, tmp
    // deinterleave lower odds into Ol
    deinterleave_even Ol, tmp
    .unreq tmp
    mask .req q4
    // El and Ol need to merge, but they are full of garbage in the odd bits
    // Build mask 0x55..55 (01010101b) to isolate even-bit positions, then
    // shift left the odd plane and OR to reconstruct the original bytes.
    mov          r, #0x55
    vdup.u8      mask, r
    vand.u32     El, El, mask
    vand.u32     Ol, Ol, mask
    vshl.u32     Ol, Ol, #1
    vorr         El, El, Ol
    .unreq Ol
    tmp .req q1
    // deinterleave upper evens into Eu
    deinterleave_even Eu, tmp
    // deinterleave lower evens into Ou
    deinterleave_even Ou, tmp
    .unreq tmp
    U .req q1
    vand.u32     U, Eu, mask       // reconstruct high bytes (even|odd<<1)
    vand.u32     Ou, Ou, mask
    vshl.u32     Ou, Ou, #1
    vorr         U, U, Ou
from_bit_interleaving_4x_exit:
    .unreq r
    .unreq U
    .unreq El
    .unreq Eu
    .unreq Ou
    .unreq mask
    bx           lr



// -----------------------------------------------------------------------------
// mlk_keccak_f1600_x4_state_extract_bytes(void *state, unsigned char *data0,
//                                              unsigned char *data1,
//                                              unsigned char *data2,
//                                              unsigned char *data3,
//                                              unsigned offset, unsigned length)
//
// AAPCS assumption:
//   r0=state, r1=d0, r2=d1, r3=d2, stack: d3, offset, length
// -----------------------------------------------------------------------------
.align 8
.global KeccakF1600x4_StateExtractBytes
.type   KeccakF1600x4_StateExtractBytes,%function
KeccakF1600x4_StateExtractBytes:
    .equ stack_offset, ((12-4+2)*4+(15-8+1)*8)
    push {r4-r12, lr}
    vpush {d8-d15}

    // Register Assignments
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
    nB                .req lr
    tmp               .req r12

    qP                .req q7
    qIdx              .req q6
    qd0               .req q0
    qd1               .req q1
    qd2               .req q2
    qd3               .req q3

    // Load the stack arguments
    ldr     dp3,      [sp, #stack_offset+0]
    ldr     off_full, [sp, #stack_offset+4]
    ldr     length,   [sp, #stack_offset+8]

    cmp     length,  #0             // if len==0 done
    beq     state_extract_exit

    and     off, off_full, #7
    bic     lane_offset_bytes, off_full, #7

    add     rSE, state, lane_offset_bytes, lsl #1
    add     rSO, rSE, #400

    // -------------------------------------------------------------------------
    // PROLOGUE: if (offset_in_lane != 0) absorb min(len, 8-offset) into one lane
    // -------------------------------------------------------------------------
    cmp     off, #0                 // if off==0 skip
    beq     pre_main

    // read the state
    vldrw.u32 qd0, [rSE], #16
    vldrw.u32 qd1, [rSO], #16

    // De-interleave one 16B Even lane and one 16B Odd lane into bytes
    // NOTE: _internal_from_bit_interleaving_4x clobbers r0,q2,q3,q4
    bl _internal_from_bit_interleaving_4x

    // Vector transpose: split q0/q1 into per-stream 8-byte chunks
    // (inverse of the gather path used in XOR function)
    // Vectors:             ||           q0          ||           q1          ||           q2          ||           q3          ||
    // Elements:            || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h ||                       ||                       ||
    vrev64.u32 q2, q0    // || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l ||                       ||
    vrev64.u32 q3, q1    // || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    mov r0, #0x0F0F
    vmsr p0, r0
    vpsel q0, q0, q3     // || d0l | d0h | d2l | d2h || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    vpsel q1, q2, q1     // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    vmov d4, d1          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h | d3l | d2l || d1h | d0h | d3h | d2h ||
    vmov d6, d3          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h | d3l | d2l || d3l | d3h | d3h | d2h ||

    // Now, qd0 through qd3 contain up to 7 bytes. Prepare to write them.
    // r0 = n = min(length, 8-off)
    rsb     nB, off, #8
    cmp     length, nB
    it      ls
    movls   nB, length

    // calculate the predicates
    // mask = (1 << nB) - 1 over 8-bit lanes, then << off
    vctp.8 nB
    vmrs mask, p0
    // mask << offset
    lsl mask, mask, off
    vmsr p0, mask

    // subtract the offset from the addresses to match the predicate
    subs dp0, dp0, off
    subs dp1, dp1, off
    subs dp2, dp2, off
    subs dp3, dp3, off

    // Predicated tail store of up to 7 bytes per stream at intra-lane offset
    // Note that 8 bytes are read, but only post-inc by 4, since
    // main body pre-increments by 4.
    vpstttt
    vstrbt.u8 qd0, [dp0], #4
    vstrbt.u8 qd1, [dp1], #4
    vstrbt.u8 qd2, [dp2], #4
    vstrbt.u8 qd3, [dp3], #4

    // length -= n
    subs    length, length, nB
    cmp     length, #0
    beq     state_extract_exit

    // Build qP = {d0,d1,d2,d3} as u32 lanes (vector of base addresses)    
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    b       main_body

pre_main:
    vmov    qP[2], qP[0],  dp0, dp2
    vmov    qP[3], qP[1],  dp1, dp3
    mov     tmp, #4
    vsub.u32    qP, qP, tmp

    // -------------------------------------------------------------------------
    // MAIN BODY: process full 8-byte lanes while len >= 8 and within frame
    // -------------------------------------------------------------------------
main_body:
    // Calculate the number of full 8-byte lanes to process
    lsr     lr, length, #3
    // Low-overhead loop on LR
    wls     lr, lr, main_loop_end
main_loop_start:
    vldrw.u32 qd0, [rSE], #16
    vldrw.u32 qd1, [rSO], #16
    // Save/restore LR around BL because LR is used by the low-overhead loop
    // for wls/le and would be clobbered by the call
    mov tmp, lr
    bl _internal_from_bit_interleaving_4x
    mov lr, tmp

    // Store to output:
    vstrw.u32   qd0, [qP, #4]!
    vstrw.u32   qd1, [qP, #4]!
    le      lr, main_loop_start
main_loop_end:
    // -------------------------------------------------------------------------
    // TAIL: if length remaining <8, absorb it at offset_in_lane=0
    // -------------------------------------------------------------------------

    // length &= 7
    // Placeholder: if r6 == 0, done.
    ands    length, length, #7
    cbz     length, state_extract_exit

    // Tail via predicated byte stores like prologue, but off=0 (no base adjust)
    mov     tmp, #4
    vadd.u32    qP, qP, tmp
    vmov    dp0, dp2, qP[2], qP[0]
    vmov    dp1, dp3, qP[3], qP[1]

    vldrw.u32 qd0, [rSE], #16
    vldrw.u32 qd1, [rSO], #16

    // De-interleave one 16B Even lane and one 16B Odd lane into bytes
    // NOTE: _internal_from_bit_interleaving_4x clobbers r0,q2,q3,q4
    bl _internal_from_bit_interleaving_4x

    // Vector transpose to obtain per-stream 8-byte chunks
    // Vectors:             ||           q0          ||           q1          ||           q2          ||           q3          ||
    // Elements:            || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h ||                       ||                       ||
    vrev64.u32 q2, q0    // || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l ||                       ||
    vrev64.u32 q3, q1    // || d0l | d1l | d2l | d3l || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    mov r0, #0x0F0F
    vmsr p0, r0
    vpsel q0, q0, q3     // || d0l | d0h | d2l | d2h || d0h | d1h | d2h | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    vpsel q1, q2, q1     // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d1l | d0l | d3l | d2l || d1h | d0h | d3h | d2h ||
    vmov d4, d1          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h | d3l | d2l || d1h | d0h | d3h | d2h ||
    vmov d6, d3          // || d0l | d0h | d2l | d2h || d1l | d1h | d3l | d3h || d2l | d2h | d3l | d2l || d3l | d3h | d3h | d2h ||

    // calculate the predicates
    // mask = (1 << length)
    vctp.8 length

    // now write the partial lanes
    // Note that 8 bytes are read, but only post-inc by 4, since
    // main body pre-increments by 4.
    vpstttt
    vstrbt.u8 qd0, [dp0], #4
    vstrbt.u8 qd1, [dp1], #4
    vstrbt.u8 qd2, [dp2], #4
    vstrbt.u8 qd3, [dp3], #4
state_extract_exit:
    vpop {d8-d15}
    pop {r4-r12, pc}
.size KeccakF1600x4_StateExtractBytes, .-KeccakF1600x4_StateExtractBytes
