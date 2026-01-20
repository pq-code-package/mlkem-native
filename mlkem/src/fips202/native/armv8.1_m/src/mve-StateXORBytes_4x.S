///
/// Copyright (c) 2025 Arm Limited
/// SPDX-License-Identifier: Apache-2.0 OR MIT OR ISC
///

#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X4) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

 .thumb
 .syntax unified
.text

@ ----------------------------------------------------------------------------
@ uint32x4_t KeccakF1600x4_StateXORBytes_aligned(uint32_t nvecs, uint8_t* state, uint32x4_t data_ptrs)
@ WARNING: Assumes that length limits are already applied
@ WARNING: Assumes that state is offset by -16
@----------------------------------------------------------------------------

.align 8
.global   MLK_ASM_NAMESPACE(KeccakF1600x4_StateXORBytes_aligned)
.type MLK_ASM_NAMESPACE(KeccakF1600x4_StateXORBytes_aligned),%function
MLK_ASM_FN_SYMBOL(KeccakF1600x4_StateXORBytes_aligned)
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
    wls lr, r0, KeccakF1600x4_StateXORBytes_aligned_x4_aligned_loop_end
KeccakF1600x4_StateXORBytes_aligned_x4_aligned_loop_start:
        @ load each vector
    vldrw.u32 q0, [q7, #4]!
    vldrw.u32 q1, [q7, #4]!
        @ Convert to bit-interleaved representation
    mov r4, lr
    bl MLK_ASM_NAMESPACE(to_bit_interleaving_4x)
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
    le  lr, KeccakF1600x4_StateXORBytes_aligned_x4_aligned_loop_start
KeccakF1600x4_StateXORBytes_aligned_x4_aligned_loop_end:
    vadd.u32 q0, q7, r3
    vpop {d14 - d15}
    pop {r4, pc}

#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
