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
    defined(MLK_USE_FIPS202_X1_XOR_BYTES_NATIVE) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

.thumb
.syntax unified
.text

// -----------------------------------------------------------------------------
// Interleave macros
// -----------------------------------------------------------------------------
// interleave_odds: in-place SWAR bit permutation that compacts odd-numbered
// bits of each byte/halfword/word in \t toward the upper half, preparing the
// odd bit-plane. Uses vshl + vsri insertion per the semantics above.
.macro interleave_odds t, u
    vshl.u8     \u, \t, #2       // u = t[5..0],00
    vsri.u8     \t, \u, #1       // t = t[7],u[6..0]  => t = t[7],t[5..0],0
    vshl.u8     \u, \t, #3       // u = t[3..0],0000
    vsri.u8     \t, \u, #2       // t = t[7..6],u[5..0] => t = t[7],t[5],t[3..0],00
    vshl.u8     \u, \t, #4       // u = t[1..0],000000
    vsri.u8     \t, \u, #3       // t = t[7],t[5],t[3],u[4..0] => t = t[7],t[5],t[3],t[1..0],000
                                 // t16 = t[15],t[13],t[11],t[9..8],000,t[7],t[5],t[3],t[1..0],000
    vshl.u16    \u, \t, #8       // u16 = t[7],t[5],t[3],t[1..0],000
    vsri.u8     \t, \u, #4       // t16 = t[15,13,11,9,7,5,3,1]
    vshl.u32    \u, \t, #16      // u32 = t[15,13,11,9,7,5,3,1]
    vsri.u16    \t, \u, #8       // u16 = t[31,29,27,25,23,21,19,17,15,13,11,9,7,5,3,1]
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

.balign 8
.macro to_bit_interleaving_x1 tmp
    // NOTE: This macro clobbers r0, q0, q1, q2, q3
    // Inputs on entry:
    //   q0 = [d0l, d0h, d1l, d1h] (Two complete 64-bit lanes in 32-bit chunks)
    // Output on return:
    //   q0 = Even bit-plane packed (e0, o0, e1, o1)
    // Vectors:                ||           q0          ||           q1          ||           q2          ||           q3          ||
    // Elements:               || d0l | d0h | d1l | d1h ||  X  |  X  |  X  |  X  ||  X  |  X  |  X  |  X  ||  X  |  X  |  X  |  X  ||
    vshl.u32 q1, q0, #0     // || d0l | d0h | d1l | d1h || d0l | d0h | d1l | d1h ||  X  |  X  |  X  |  X  ||  X  |  X  |  X  |  X  ||
    interleave_evens q1, q2 // || d0l | d0h | d1l | d1h || e0l | e0h | e1l | e1h ||  X  |  X  |  X  |  X  ||  X  |  X  |  X  |  X  ||
    vrev64.u32 q2, q1       // || d0l | d0h | d1l | d1h || e0l | e0h | e1l | e1h || e0h | e0l | e1h | e1l ||  X  |  X  |  X  |  X  ||
    vsli.u32   q1, q2, #16  // || d0l | d0h | d1l | d1h || e0  |  X  | e1  |  X  || e0h | e0l | e1h | e1l ||  X  |  X  |  X  |  X  ||
    interleave_odds  q0, q3 // || o0l | o0h | o1l | o1h || e0  |  X  | e1  |  X  || e0h | e0l | e1h | e1l ||  X  |  X  |  X  |  X  ||
    vrev64.u32 q3, q0       // || o0l | o0h | o1l | o1h || e0  |  X  | e1  |  X  || e0h | e0l | e1h | e1l || o0h | o0l | o1h | o1l ||
    vsri.u32   q0, q3, #16  // ||  X  | o0  |  X  | o1  || e0  |  X  | e1  |  X  || e0h | e0l | e1h | e1l || o0h | o0l | o1h | o1l ||
    mov \tmp, #0x0F0F
    vmsr p0, \tmp
    vpsel q0, q1, q0        // || e0  | o0  | e1  | o1  || e0  |  X  | e1  |  X  || e0h | e0l | e1h | e1l || o0h | o0l | o1h | o1l ||
.endm

@ -----------------------------------------------------------------------------
@ void keccak_f1600_x4_state_xor_bytes_asm(void *state,
@                                          const uint8_t *d,
@                                          uint32_t offset, uint32_t length)
@
@ AAPCS assumption:
@   r0=state, r1=d, r2=offset, r3=length
@ -----------------------------------------------------------------------------

.balign 8
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_state_xor_bytes_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_state_xor_bytes_asm)
    .equ stack_offset, ((12-4+2)*4+(15-8+1)*8)
    push    {r4-r12, lr}
    @ vpush   {d8-d15}

    state               .req r0
    dp                  .req r1
    off_full            .req r2
    length              .req r3
    tmp                 .req r4
    off                 .req r5
    lane_offset_bytes   .req r6
    mask                .req r7
    nB                  .req lr
    // ---- Vector naming ----
    qd                  .req q0
    qs                  .req q1



    cmp     length,  #0             // if len==0 done
    beq     keccak_f1600_x1_state_xor_bytes_asm_exit

    and     off, off_full, #15
    bic     lane_offset_bytes, off_full, #15

    add     state, state, lane_offset_bytes

    // -------------------------------------------------------------------------
    // PROLOGUE: if (offset_in_lane != 0) absorb min(len, 8-offset) into one lane
    // -------------------------------------------------------------------------
    cmp     off, #0                 // if off==0 skip
    beq     keccak_f1600_x1_state_xor_bytes_asm_pre_main
    // subtract the offset from the addresses to match the predicate
    subs dp, dp, off

    // r0 = n = min(length, 8-off)
    rsb     nB, off, #16
    cmp     length, nB
    it      ls
    movls   nB, length
    // length -= n
    subs    length, length, nB
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
    vpst
    vldrbt.u8 qd, [dp], #16

    // Bit interleave
    // NOTE: q2,q3,q4 are dead here and not preserved.
    to_bit_interleaving_x1 tmp

    vldrw.u32 qs, [state]
    veor      qs, qs, qd
    vstrw.u32 qs, [state], #16

    cmp     length, #0
    beq     keccak_f1600_x1_state_xor_bytes_asm_exit

keccak_f1600_x1_state_xor_bytes_asm_pre_main:
keccak_f1600_x1_state_xor_bytes_asm_main_body:
    // -------------------------------------------------------------------------
    // MAIN BODY: process full 8-byte lanes while len >= 8 and within frame
    // -------------------------------------------------------------------------
    // Calculate the number of full 8-byte lanes to process
    lsr     lr, length, #4
    // Low-overhead loop: wls/le use LR as the hardware loop counter
    wls     lr, lr, keccak_f1600_x1_state_xor_bytes_asm_main_loop_end
keccak_f1600_x1_state_xor_bytes_asm_main_loop_start:
    // Read two u32 vectors and bump per-stream pointer
    vldrw.u32 qd, [dp], #16
    // Bit interleave
    // NOTE: q2,q3,q4 are dead here and not preserved.
    to_bit_interleaving_x1 tmp

    // XOR into state (stores post-increment state by 16)
    vldrw.u32 qs, [state]
    veor      qs, qs, qd
    vstrw.u32 qs, [state], #16

    // loop end, branch to loop_start while LR>0
    le      lr, keccak_f1600_x1_state_xor_bytes_asm_main_loop_start 
keccak_f1600_x1_state_xor_bytes_asm_main_loop_end:
    // -------------------------------------------------------------------------
    // TAIL: if length remaining <8, absorb it at offset_in_lane=0
    // -------------------------------------------------------------------------

    // length &= 15
    // Placeholder: if r6 == 0, done.
    ands    length, length, #15
    cmp     length, #0
    beq     keccak_f1600_x1_state_xor_bytes_asm_exit

    // Tail via predicated byte loads like prologue, but off=0 (no base adjust)
    vctp.8  length
    vpst
    vldrbt.u8 qd, [dp], #16

    // Bit interleave
    // NOTE: q2,q3,q4 are dead here and not preserved.
    to_bit_interleaving_x1 tmp

    vldrw.u32 qs, [state]
    veor      qs, qs, qd
    vstrw.u32 qs, [state], #16

keccak_f1600_x1_state_xor_bytes_asm_exit:
    @ vpop    {d8-d15}
    pop     {r4-r12, pc}

/* simpasm: footer-start */
#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
