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
/* simpasm: header-end */

.thumb
.syntax unified
.text

// -----------------------------------------------------------------------------
// Deinterleave macros (adapted from x4 version)
// -----------------------------------------------------------------------------

// deinterleave_even: inverse of the even-bit compaction. Inflates the even
// bit-plane stored in \e back into byte positions (odd bits garbage).
.macro deinterleave_even e, tmp
                                // | e[31:24] | e[23:16] | e[15:8] | e[7:0] |
    vsli.u32    \e, \e, #8      // | e[23:16] | e[15:8]  | e[7:0]  | e[7:0] |
    vsli.u16    \e, \e, #4      // | e[19:12] | e[11:8,11:8]  | e[3:0,7:4]  | e[3:0,3:0] |
    vsli.u8     \e, \e, #1      // | e[18:12,12] | e[10:8,11:8,8]  | e[2:0,7:4,4]  | e[2:0,3:0,0] |
    vshr.u8     \tmp, \e, #3
    vsli.u8     \e, \tmp, #4    // | e[17:14,14:12,12] | e[9:8,11:10,10:8,8]  | e[1:0,7:6,6:4,4]  | e[1:0,3:2,2:0,0] |
    vshr.u8     \tmp, \e, #5
    vsli.u8     \e, \tmp, #6    // | e[16:15,15:14,14:12,12] | e[8,11,11:10,10:8,8]  | e[0,7,7:6,6:4,4]  | e[0,3,3:2,2:0,0] |
                                // after 0x55 mask
                                // | e[15,14,13,12] | e[11,10,9,8]  | e[7,6,5,4]  | e[3,2,1,0] |
.endm

.balign 8
.macro from_bit_interleaving_x1 tmp
    // Input:  q0 = [e0, o0, e1, o1]
    // Output: q0 = [d0l, d0h, d1l, d1h]
    // Clobbers: r0, q1, q2, q3, q4
    
    mov         \tmp, #0x0F0F
    vmsr        p0, \tmp
    //                        // q0.u16: [e0l, e0h, o0l, o0h, e1l, e1h, o1l, o1h] 
    vrev32.u16  q1, q0        // q1.u16: [e0h, e0l, o0h, o0l, e1h, e1l, o1h, o1l] 
    vrev64.u32  q2, q1        // q2.u16: [o0h, o0l, e0h, e0l, o1h, o1l, e1h, e1l]
    vrev64.u32  q3, q0        // q3.u16: [o0l, o0h, e0l, e0h, o1l, o1h, e1l, e1h] 
    // construct an e vector
    vpsel       q0, q0, q2    // q0.u16: [e0l, e0h, e0h, e0l, e1l, e1h, e1h, e1l] 
    // construct an o vector
    vpsel       q1, q3, q1    // q0.u16: [o0l, o0h, o0h, o0l, o1l, o1h, o1l, o1h] 
    // expand vectors
    deinterleave_even q0, q2
    deinterleave_even q1, q2
    // Zero garbage bits
    mov         \tmp, #0x55
    vdup.u8     q2, \tmp
    vand.u32    q0, q0, q2
    vand.u32    q1, q1, q2
    // Merge vectors
    vshl.u32    q1, q1, #1
    vorr        q0, q1, q0
.endm

@ -----------------------------------------------------------------------------
@ void keccak_f1600_x1_state_extract_bytes_asm(void *state,
@                                             uint8_t *d,
@                                             uint32_t offset, uint32_t length)
@
@ AAPCS assumption:
@   r0=state, r1=d, r2=offset, r3=length
@ -----------------------------------------------------------------------------

.balign 8
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_state_extract_bytes_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_state_extract_bytes_asm)
    .equ stack_offset, ((12-4+2)*4+(15-8+1)*8)
    push    {r4-r12, lr}
    @ vpush   {d8-d15}

    state               .req r0
    dp                  .req r1
    off_full            .req r2
    length              .req r3
    tmp                 .req r4
    nB                  .req lr
    off                 .req r5
    lane_offset_bytes   .req r9
    mask                .req r11
    // ---- Vector naming ----
    qd                  .req q0
    qs                  .req q1

    cmp     length,  #0             // if len==0 done
    beq     keccak_f1600_x1_state_extract_bytes_asm_exit

    and     off, off_full, #15
    bic     lane_offset_bytes, off_full, #15

    add     state, state, lane_offset_bytes

    // -------------------------------------------------------------------------
    // PROLOGUE: if (offset_in_lane != 0) write min(len, 8-offset) from one lane
    // -------------------------------------------------------------------------
    cmp     off, #0                 // if off==0 skip
    beq     keccak_f1600_x1_state_extract_bytes_asm_pre_main
    // subtract the offset from the data pointer to match the predicate
    subs    dp, dp, off

    // r0 = n = min(length, 16-off)
    rsb     nB, off, #16
    cmp     length, nB
    it      ls
    movls   nB, length
    // length -= n
    subs    length, length, nB

    // Load state for the partial lane
    vldrw.u32 qd, [state], #16
    // Deinterleave to bytes
    from_bit_interleaving_x1 tmp
    // Predicated byte store of up to 16 bytes
    // calculate the predicates
    // mask = (1 << nB) - 1 over 8-bit lanes, then shift by 'off'.
    // vctp.8 sets p0[0..nB-1]=1 (others 0). We read it as an integer mask,
    // left-shift to align the active bytes within the 16-byte double-lane, and write
    // it back to p0 to predicate the subsequent byte stores.
    vctp.8 nB
    vmrs mask, p0
    // mask << offset
    lsl mask, mask, off
    vmsr p0, mask
    vpst
    vstrbt.u8 qd, [dp], #16

    cmp     length, #0
    beq     keccak_f1600_x1_state_extract_bytes_asm_exit

keccak_f1600_x1_state_extract_bytes_asm_pre_main:
keccak_f1600_x1_state_extract_bytes_asm_main_body:
    // -------------------------------------------------------------------------
    // MAIN BODY: process full 8-byte lanes while len >= 8 and within frame
    // -------------------------------------------------------------------------
    // Calculate the number of full 8-byte lanes to process
    lsr     lr, length, #4
    // Low-overhead loop: wls/le use LR as the hardware loop counter
    wls     lr, lr, keccak_f1600_x1_state_extract_bytes_asm_main_loop_end
keccak_f1600_x1_state_extract_bytes_asm_main_loop_start:
    // Load 16B (two lanes) from state and bump pointer
    vldrw.u32 qd, [state], #16
    // Deinterleave to bytes
    from_bit_interleaving_x1 tmp
    // Store 16B of output bytes (post-increment by 16)
    vstrw.u32 qd, [dp], #16

    // loop end, branch to loop_start while LR>0
    le      lr, keccak_f1600_x1_state_extract_bytes_asm_main_loop_start 
keccak_f1600_x1_state_extract_bytes_asm_main_loop_end:
    // -------------------------------------------------------------------------
    // TAIL: if length remaining <8, write it at offset_in_lane=0
    // -------------------------------------------------------------------------

    // length &= 15
    ands    length, length, #15
    cmp     length, #0
    beq     keccak_f1600_x1_state_extract_bytes_asm_exit

    // Load next state lane, deinterleave, store tail
    vldrw.u32 qd, [state], #16
    from_bit_interleaving_x1 tmp
    // Tail via predicated byte stores like prologue, but off=0 (no base adjust)
    vctp.8  length
    vpst
    vstrbt.u8 qd, [dp], #16

keccak_f1600_x1_state_extract_bytes_asm_exit:
    @ vpop    {d8-d15}
    pop     {r4-r12, pc}

/* simpasm: footer-start */
#endif /* MLK_FIPS202_ARMV81M_NEED_X1 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
