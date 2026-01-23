/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) 2025 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X4) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

.thumb
.syntax unified
.text

@----------------------------------------------------------------------------
@ uint32x4x2_t keccak_f1600_x4_load_bytes_in_lane(uint32x4_t data_ptrs, uint32_t length, uint32_t offset)
@----------------------------------------------------------------------------
.balign 8
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_load_bytes_in_lane)
.type MLK_ASM_NAMESPACE(keccak_f1600_x4_load_bytes_in_lane), %function
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_load_bytes_in_lane)
    push {r4-r11, lr}
    vpush {d8-d11}
    @ generate incrementing sequence
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

/* simpasm: footer-start */
#endif /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
