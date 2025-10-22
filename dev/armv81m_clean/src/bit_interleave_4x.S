///
/// Copyright (c) 2025 Arm Limited
/// SPDX-License-Identifier: Apache-2.0 OR MIT OR ISC
///

 .thumb
 .syntax unified
.text


.macro interleave_odds x, t
    vshl.u32    \t, \x, #0
    vshl.u8     u, \t, #2
    vsri.u8     \t, u, #1
    vshl.u8     u, \t, #3
    vsri.u8     \t, u, #2
    vshl.u8     u, \t, #4
    vsri.u8     \t, u, #3
    vshl.u16    u, \t, #8
    vsri.u8     \t, u, #4
    vshl.u32    u, \t, #16
    vsri.u16    \t, u, #8

.endm

.macro interleave_evens x, t
    vshl.u32    \t, \x, #0
    vshr.u8     u, \t, #2
    vsli.u8     \t, u, #1
    vshr.u8     u, \t, #3
    vsli.u8     \t, u, #2
    vshr.u8     u, \t, #4
    vsli.u8     \t, u, #3
    vshr.u16    u, \t, #8
    vsli.u8     \t, u, #4
    vshr.u32    u, \t, #16
    vsli.u16    \t, u, #8
.endm

.align 8
.type to_bit_interleaving_4x, %function
.global to_bit_interleaving_4x
to_bit_interleaving_4x:
    push	{r4 - r11, lr}
    vpush   {d8 - d15}
to_bit_interleaving_4x_start:
    interleave_evens q0, E0
    interleave_evens q1, E1
    vsli.32          E0, E1, #16
    interleave_odds  q0, O0
    interleave_odds  q1, O1
    vsri.32          O1, O0, #16
    vshl.u32         q0, E0, #0
    vshl.u32         q1, O1, #0
to_bit_interleaving_4x_exit:
    vpop {d8 - d15}
    pop {r4 - r11, pc}

.macro deinterleave_inner t
    vsli.u32     \t, \t, #8
    vsli.u16     \t, \t, #4
    vshr.u8       u, \t, #3
    vsli.u8      \t,  u, #4
    vshr.u8       u, \t, #2
    vsli.u8      \t,  u, #3
    vshr.u8       u, \t, #1
    vsli.u8      \t,  u, #2
.endm

.align 8
.type from_bit_interleaving_4x, %function
.global from_bit_interleaving_4x
from_bit_interleaving_4x:
    push	{r4 - r11, lr}
    vpush   {d8 - d15}
from_bit_interleaving_4x_start:
    vshr.u32     E1, q0, #16
    deinterleave_inner E1
    vshr.u32     O1, q1, #16
    deinterleave_inner O1
    mov          r, #0x55
    vdup.u8      M, r
    vand.u32     E1, E1, M
    vand.u32     O1, O1, M
    deinterleave_inner q0
    deinterleave_inner q1
    vand.u32     q0, q0, M
    vand.u32     q1, q1, M
    vshl.u32     q1, q1, #1
    vorr         q0, q0, q1
    vshl.u32     O1, O1, #1
    vorr         q1, E1, O1
from_bit_interleaving_4x_exit:
    vpop {d8 - d15}
    pop {r4 - r11, pc}

@ ----------------------------------------------------------------------------
@ uint32x4_t KeccakF1600x4_StateXORBytes_aligned(uint32_t nvecs, uint8_t* state, uint32x4_t data_ptrs)
@ WARNING: Assumes that length limits are already applied
@ WARNING: Assumes that state is offset by -16
@----------------------------------------------------------------------------

.align 8
.global   KeccakF1600x4_StateXORBytes_aligned
.type KeccakF1600x4_StateXORBytes_aligned,%function
KeccakF1600x4_StateXORBytes_aligned:
    push {r4, lr}
    vpush {d14 - d15}
    @ Setup the two state pointers
    add r2, r1, #400
    @ Offset the data pointers
    mov r3, #4
    vsub.u32 q7, q0, r3
    @ vmov q7, q0
    @ mov lr, r0
    @ xor each vector into the state
    wls lr, r0, x4_aligned_loop_end
x4_aligned_loop_start:
        @ load each vector
    vldrw.u32 q0, [q7, #4]!
    vldrw.u32 q1, [q7, #4]!
        @ Convert to bit-interleaved representation
    mov r4, lr
    bl to_bit_interleaving_4x
    mov lr, r4
        @ load state
    vldrw.u32 q2, [r1, #16]
    vldrw.u32 q3, [r2, #16]
        @ xor bit interleaved vector with state
    veor      q2, q2, q0
    veor      q3, q3, q1
        @ write state back
    vstrw.u32 q2, [r1, #16]!
    vstrw.u32 q3, [r2, #16]!
        @ decrement length
    le  lr, x4_aligned_loop_start
x4_aligned_loop_end:
    vadd.u32 q0, q7, r3
    vpop {d14 - d15}
    pop {r4, pc}


@----------------------------------------------------------------------------
@ uint32x4x2_t KeccakF1600x4_LoadBytesInLane(uint32x4_t data_ptrs, uint32_t length, uint32_t offset)
@----------------------------------------------------------------------------
.align 8
.global   KeccakF1600x4_LoadBytesInLane
.type KeccakF1600x4_LoadBytesInLane,%function
KeccakF1600x4_LoadBytesInLane:
    push {r4-r11, lr}
    vpush {d8-d11}
    @ generate incremeting sequence
    mov r2, #0
    vidup.u8 q1, r2, #1
    @ calculate the predicates
    @ mask = (1 << length) - 1
    mov r3, #1
    lsl r3, r3, r0
    sub r3, r3, #1
    @ mask << offset
    lsl r3, r3, r1
    vmsr p0, r3
    @ subtract the offset from the addresses to match the predicate
    vsub.u32 q0, q0, r1
    @ get the addresses
    vmov r4, r6, q0[2], q0[0]
    vmov r5, r7, q0[3], q0[1]
    @ now load the partial lanes
    vpstttt
    vldrbt.u8 q2, [r4, q1]
    vldrbt.u8 q3, [r5, q1]
    vldrbt.u8 q4, [r6, q1]
    vldrbt.u8 q5, [r7, q1]
    @ sort the partial lanes into two 4x32 vectors
    vmov r8, r9, d4
    vmov r10, r11, d8
    vmov q0[2], q0[0], r8, r10
    vmov q1[2], q1[0], r9, r11

    vmov r8, r9, d6
    vmov r10, r11, d10
    vmov q0[3], q0[1], r8, r10
    vmov q1[3], q1[1], r9, r11

    vpop {d8 - d11}
    pop {r4-r11, pc}

