/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [ADOMNICAI23]
 *   An update on Keccak performance on ARMv7-M
 *   Alexandre Adomnicai
 *   https://eprint.iacr.org/2023/773
 *
 * - [SLOTHYM7]
 *   Enabling Microarchitectural Agility: Taking ML-KEM & ML-DSA from Cortex-M4
 *   to M7 with SLOTHY
 *   Abdulrahman, Kannwischer, Lim
 *   https://eprint.iacr.org/2025/366
 *
 * - [XKCP]
 *   eXtended Keccak Code Package
 *   Bertoni, Daemen, Peeters, Van Assche, Van Keer
 *   https://github.com/XKCP/XKCP
 */

/*
 * This file is derived from the public domain implementation @[XKCP].
 * Optimizations for Armv7-M are described in @[ADOMNICAI23].
 * Further optimizations using SLOTHY are described in @[SLOTHYM7].
 */

#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X1) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/armv81m/src/keccak_f1600_x1_armv7m.S using scripts/simpasm. Do not modify it directly.
 */

.thumb
.syntax unified

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_armv7m_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_armv7m_asm)

        push.w	{r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
        sub	sp, #0x18
        str	r1, [sp, #0x14]

slothy_start:
        ldr.w	r3, [r0, #0x3c]
        ldr.w	r11, [r0, #0x20]
        ldr.w	lr, [r0, #0x14]
        ldr.w	r10, [r0, #0x48]
        ldr.w	r9, [r0, #0x64]
        ldr.w	r8, [r0, #0x70]
        ldr.w	r4, [r0, #0x80]
        eor.w	r7, lr, r3
        ldr.w	r3, [r0, #0x34]
        eor.w	r6, r11, r10
        ldr.w	lr, [r0, #0xc]
        eor.w	r9, r7, r9
        ldr.w	r7, [r0, #0x5c]
        eor.w	r11, r6, r8
        eor.w	r6, lr, r3
        ldr.w	r2, [r0, #0x30]
        ldr.w	r3, [r0, #0x28]
        ldr.w	r10, [r0, #0x84]
        eor.w	r1, r6, r7
        ldr.w	r12, [r0, #0xac]
        ldr.w	r8, [r0]
        ldr.w	r7, [r0, #0x8c]
        ldr.w	lr, [r0, #0x8]
        eor.w	r5, r1, r10
        eor.w	r3, r8, r3
        ldr.w	r1, [r0, #0x50]
        eor.w	r5, r5, r12
        ldr	r6, [r0, #0x78]
        eor.w	r10, lr, r2
        ldr.w	lr, [r0, #0x40]
        eor.w	r12, r3, r1
        ldr.w	r1, [r0, #0x98]
        ldr.w	r2, [r0, #0x18]
        eor.w	r6, r12, r6
        ldr.w	r12, [r0, #0xb4]
        ldr.w	r3, [r0, #0x68]
        eor.w	r9, r9, r7
        ldr.w	r7, [r0, #0x58]
        eor.w	lr, r2, lr
        eor.w	r9, r9, r12
        ldr.w	r8, [r0, #0xc0]
        ldr.w	r12, [r0, #0x1c]
        eor.w	r11, r11, r1
        eor.w	r10, r10, r7
        ldr.w	r2, [r0, #0x44]
        ldr.w	r1, [r0, #0xa0]
        eor.w	r8, r11, r8
        eor.w	r3, lr, r3
        ldr.w	r11, [r0, #0x90]
        eor.w	r2, r12, r2
        ldr.w	lr, [r0, #0x6c]
        eor.w	r7, r8, r5, ror #31
        eor.w	r8, r8, r9
        eor.w	r12, r3, r11
        ldr.w	r3, [r0, #0x94]
        str.w	r7, [sp]
        eor.w	lr, r2, lr
        eor.w	r2, r6, r1
        ldr.w	r11, [r0, #0xbc]
        eor.w	lr, lr, r3
        ldr.w	r1, [r0, #0xb8]
        ldr.w	r7, [r0, #0xa8]
        eor.w	r4, r10, r4
        eor.w	r6, lr, r11
        ldr.w	r11, [r0, #0x9c]
        eor.w	r3, r12, r1
        ldr.w	r1, [r0, #0x4c]
        eor.w	r7, r4, r7
        eor.w	lr, r6, r2
        eor.w	r10, r2, r9, ror #31
        ldr.w	r12, [r0, #0xc4]
        eor.w	r2, r5, r3
        ldr.w	r5, [r0, #0x24]
        ldr.w	r4, [r0, #0x38]
        eor.w	r6, r7, r6, ror #31
        ldr.w	r9, [r0, #0x10]
        eor.w	r1, r5, r1
        ldr.w	r5, [r0, #0x74]
        str.w	r6, [sp, #0x10]
        ldr.w	r6, [r0, #0x2c]
        eor.w	r4, r9, r4
        ldr.w	r9, [r0, #0x4]
        eor.w	r1, r1, r5
        ldr.w	r5, [r0, #0x54]
        eor.w	r9, r9, r6
        ldr.w	r6, [r0, #0x60]
        eor.w	r1, r1, r11
        ldr.w	r11, [r0, #0x7c]
        eor.w	r9, r9, r5
        ldr.w	r5, [r0, #0x88]
        eor.w	r4, r4, r6
        ldr.w	r6, [r0, #0xa4]
        str.w	r8, [sp, #0xc]
        eor.w	r9, r9, r11
        eor.w	r5, r4, r5
        ldr.w	r8, [r0, #0xb0]
        ldr.w	r4, [r0, #0xb4]
        eor.w	r11, r9, r6
        eor.w	r9, r1, r12
        ldr.w	r1, [r0, #0x84]
        eor.w	r5, r5, r8
        ldr.w	r8, [r0, #0x54]
        eor.w	r12, r3, r11, ror #31
        eor.w	r7, r9, r7
        eor.w	r8, r7, r8
        eor.w	r11, r11, r5
        eor.w	r9, r5, r9, ror #31
        eor.w	r5, r11, r1
        bic.w	r3, r5, r8, ror #21
        eor.w	r1, r2, r4
        ldr.w	r4, [r0, #0x18]
        bic.w	r6, r1, r5, ror #8
        eor.w	r6, r6, r8, ror #29
        eor.w	r4, r9, r4
        str.w	r6, [r0, #0xb4]
        bic.w	r6, r4, r1, ror #15
        eor.w	r5, r6, r5, ror #23
        ldr.w	r6, [r0, #0x48]
        str.w	r7, [sp, #0x4]
        eor.w	r6, r12, r6
        str.w	r5, [r0, #0x18]
        bic.w	r5, r6, r4, ror #28
        eor.w	r1, r5, r1, ror #11
        ldr.w	r5, [r0, #0x3c]
        eor.w	r3, r3, r6, ror #13
        eor.w	r5, r2, r5
        str.w	r1, [r0, #0x48]
        ldr.w	r1, [r0, #0x8]
        str.w	r3, [r0, #0x84]
        eor.w	r3, r10, r1
        bic.w	r6, r8, r6, ror #24
        ldr.w	r8, [r0, #0x68]
        eor.w	r1, r9, r8
        ldr.w	r8, [r0, #0xa4]
        eor.w	r7, r7, r8
        bic.w	r8, r1, r5, ror #9
        eor.w	r4, r6, r4, ror #20
        ldr.w	r6, [r0, #0x9c]
        eor.w	r6, lr, r6
        eor.w	r8, r8, r3, ror #12
        str.w	r4, [r0, #0x54]
        bic.w	r4, r6, r1, ror #24
        str.w	r8, [r0, #0xa4]
        bic.w	r8, r7, r6, ror #5
        str.w	r9, [sp, #0x8]
        eor.w	r4, r4, r5, ror #1
        eor.w	r1, r8, r1, ror #29
        str.w	r4, [r0, #0x8]
        bic.w	r4, r5, r3, ror #3
        ldr.w	r5, [r0, #0x58]
        eor.w	r5, r10, r5
        bic.w	r3, r3, r7, ror #23
        eor.w	r6, r3, r6, ror #28
        str.w	r1, [r0, #0x3c]
        str.w	r6, [r0, #0x68]
        ldr.w	r8, [r0, #0x8c]
        eor.w	r1, r4, r7, ror #26
        ldr.w	r7, [r0, #0xb8]
        ldr.w	r4, [r0, #0x28]
        str.w	r1, [r0, #0x9c]
        eor.w	r1, r2, r8
        ldr.w	r8, [sp]
        eor.w	r3, r9, r7
        eor.w	r7, r8, r4
        ldr.w	r6, [r0, #0x40]
        bic.w	r4, r1, r5, ror #3
        eor.w	r4, r4, r7, ror #22
        str.w	r4, [r0, #0x58]
        eor.w	r4, r9, r6
        bic.w	r9, r3, r1, ror #20
        ldr.w	r6, [r0, #0x24]
        eor.w	r9, r9, r5, ror #23
        str.w	r9, [r0, #0x8c]
        eor.w	r9, lr, r6
        bic.w	r6, r9, r3, ror #18
        eor.w	r1, r6, r1, ror #6
        ldr.w	r6, [r0, #0x14]
        str.w	r1, [r0, #0xb8]
        bic.w	r1, r7, r9, ror #4
        bic.w	r7, r5, r7, ror #19
        ldr.w	r5, [r0, #0x70]
        eor.w	r9, r7, r9, ror #23
        str.w	r9, [r0, #0x28]
        ldr.w	r9, [r0, #0x78]
        eor.w	r5, r12, r5
        eor.w	r1, r1, r3, ror #22
        eor.w	r7, r8, r9
        ldr.w	r9, [r0, #0xac]
        bic.w	r3, r7, r5, ror #1
        eor.w	r3, r3, r4, ror #25
        str.w	r3, [r0, #0xac]
        eor.w	r3, r2, r6
        eor.w	r6, r11, r9
        str.w	r1, [r0, #0x24]
        ldr	r1, [r0, #0x64]
        eor.w	r1, r2, r1
        bic.w	r9, r5, r4, ror #24
        bic.w	r4, r4, r3, ror #28
        ldr	r2, [r0, #0x30]
        eor.w	r4, r4, r6, ror #26
        str.w	r4, [r0, #0x70]
        eor.w	r4, r10, r2
        bic.w	r2, r3, r6, ror #30
        eor.w	r9, r9, r3, ror #20
        ldr.w	r3, [r0]
        eor.w	r3, r8, r3
        str.w	r9, [r0, #0x78]
        eor.w	r2, r2, r7, ror #11
        str.w	r2, [r0, #0x40]
        bic.w	r9, r6, r7, ror #13
        ldr.w	r6, [r0, #0x94]
        eor.w	r7, r9, r5, ror #14
        ldr.w	r9, [sp, #0xc]
        bic.w	r5, r1, r4
        eor.w	r6, r9, r6
        bic.w	r2, r6, r1, ror #21
        str.w	r7, [r0, #0x14]
        eor.w	r2, r2, r4, ror #21
        ldr.w	r7, [r0, #0xc0]
        eor.w	r7, r12, r7
        eor.w	r5, r3, r5, ror #10
        str.w	r2, [r0, #0x30]
        bic.w	r2, r7, r6, ror #28
        eor.w	r1, r2, r1, ror #17
        str.w	r1, [r0, #0x64]
        bic.w	r1, r3, r7, ror #25
        ldr.w	r2, [sp, #0x10]
        eor.w	r1, r1, r6, ror #21
        str.w	r1, [r0, #0x94]
        bic.w	r1, r4, r3, ror #22
        ldr	r4, [sp, #0x14]
        ldr.w	r3, [r0, #0x20]
        eor.w	r1, r1, r7, ror #15
        ldr	r6, [r4]
        str.w	r1, [r0, #0xc0]
        eor.w	r5, r6, r5
        str.w	r5, [r0]
        ldr.w	r1, [r0, #0x6c]
        ldr.w	r6, [r0, #0xa0]
        eor.w	r5, r9, r1
        ldr.w	r1, [r0, #0x98]
        eor.w	r7, r12, r1
        eor.w	r1, r8, r6
        eor.w	r3, r12, r3
        bic.w	r6, r7, r5, ror #23
        bic.w	r4, r1, r7, ror #5
        ldr.w	r12, [r0, #0x38]
        eor.w	r4, r4, r5, ror #28
        str.w	r4, [r0, #0x38]
        ldr.w	r4, [r0, #0x50]
        eor.w	r12, r2, r12
        eor.w	r4, r8, r4
        ldr.w	r8, [r0, #0xc]
        eor.w	r8, r11, r8
        eor.w	r6, r6, r12, ror #1
        str.w	r6, [r0, #0xc]
        bic.w	r5, r5, r12, ror #10
        ldr.w	r6, [r0, #0x2c]
        bic.w	r12, r12, r8, ror #2
        eor.w	r5, r5, r8, ror #12
        str.w	r5, [r0, #0xa0]
        ldr.w	r5, [r0, #0x4c]
        bic.w	r8, r8, r1, ror #24
        eor.w	r1, r12, r1, ror #26
        str.w	r1, [r0, #0x98]
        eor.w	r8, r8, r7, ror #29
        str.w	r8, [r0, #0x6c]
        eor.w	r5, lr, r5
        ldr.w	r12, [r0, #0x80]
        eor.w	r1, r10, r12
        ldr.w	r8, [r0, #0xb0]
        eor.w	r12, r2, r8
        bic.w	r7, r1, r4, ror #21
        eor.w	r8, r7, r5, ror #12
        str.w	r8, [r0, #0x80]
        bic.w	r8, r12, r1, ror #8
        ldr.w	r7, [r0, #0x1c]
        eor.w	r8, r8, r4, ror #29
        eor.w	r7, r9, r7
        str.w	r8, [r0, #0xb0]
        bic.w	r8, r4, r5, ror #23
        eor.w	r4, r8, r7, ror #19
        str.w	r4, [r0, #0x50]
        bic.w	r4, r7, r12, ror #16
        ldr.w	r8, [sp, #0x4]
        eor.w	r1, r4, r1, ror #24
        str.w	r1, [r0, #0x1c]
        eor.w	r4, r8, r6
        bic.w	r5, r5, r7, ror #28
        eor.w	r12, r5, r12, ror #12
        ldr.w	r7, [r0, #0xbc]
        ldr.w	r6, [r0, #0x88]
        ldr.w	r1, [r0, #0x5c]
        eor.w	r6, r2, r6
        eor.w	r5, r11, r1
        str.w	r12, [r0, #0x4c]
        bic.w	r1, r5, r4, ror #19
        eor.w	r7, r9, r7
        eor.w	r1, r1, r3, ror #24
        str.w	r1, [r0, #0x2c]
        bic.w	r1, r6, r5, ror #2
        ldr.w	r12, [r0, #0x74]
        eor.w	r1, r1, r4, ror #21
        str.w	r1, [r0, #0x5c]
        bic.w	r1, r4, r3, ror #5
        ldr.w	r4, [r0, #0x44]
        eor.w	r4, r9, r4
        bic.w	r9, r7, r6, ror #21
        eor.w	r5, r9, r5, ror #23
        str.w	r5, [r0, #0x88]
        bic.w	r3, r3, r7, ror #17
        ldr.w	r9, [r0, #0x7c]
        eor.w	r6, r3, r6, ror #6
        str.w	r6, [r0, #0xbc]
        eor.w	r5, r1, r7, ror #22
        ldr.w	r1, [r0, #0x10]
        eor.w	r1, r2, r1
        ldr.w	r7, [r0, #0xa8]
        eor.w	r12, lr, r12
        eor.w	r3, r8, r9
        bic.w	r9, r12, r4, ror #24
        eor.w	r6, r10, r7
        eor.w	r7, r9, r1, ror #21
        ldr.w	r9, [r0, #0x90]
        bic.w	r10, r1, r6, ror #30
        str.w	r5, [r0, #0x20]
        str.w	r7, [r0, #0x7c]
        bic.w	r7, r3, r12, ror #1
        eor.w	r7, r7, r4, ror #25
        str.w	r7, [r0, #0xa8]
        eor.w	r5, r10, r3, ror #10
        ldr	r7, [r0, #0x60]
        eor.w	r7, r2, r7
        bic.w	r2, r4, r1, ror #29
        bic.w	r3, r6, r3, ror #12
        ldr.w	r10, [sp, #0x8]
        eor.w	r9, r10, r9
        eor.w	r10, r2, r6, ror #27
        eor.w	r3, r3, r12, ror #13
        str.w	r3, [r0, #0x10]
        str.w	r5, [r0, #0x44]
        ldr.w	r4, [r0, #0xc4]
        eor.w	r4, lr, r4
        ldr.w	lr, [r0, #0x4]
        eor.w	r6, r8, lr
        ldr.w	r8, [r0, #0x34]
        eor.w	r2, r11, r8
        str.w	r10, [r0, #0x74]
        bic.w	r12, r9, r7, ror #21
        ldr.w	r5, [r0, #0x98]
        ldr	r1, [sp, #0x14]
        bic.w	r3, r6, r4, ror #25
        eor.w	lr, r3, r9, ror #22
        str.w	lr, [r0, #0x90]
        eor.w	lr, r12, r2, ror #20
        str.w	lr, [r0, #0x34]
        bic.w	lr, r4, r9, ror #29
        ldr.w	r11, [r1, #0x4]
        ldr.w	r8, [r0, #0xc0]
        eor.w	r12, lr, r7, ror #18
        bic.w	lr, r7, r2, ror #31
        str.w	r12, [r0, #0x60]
        bic.w	r10, r2, r6, ror #22
        ldr.w	r7, [r0, #0x34]
        eor.w	r4, r10, r4, ror #15
        str.w	r4, [r0, #0xc4]
        eor.w	r6, r6, lr, ror #11
        ldr.w	r9, [r0, #0x48]
        ldr.w	lr, [r0, #0x60]
        ldr.w	r1, [r0, #0xb0]
        ldr.w	r10, [r0, #0x3c]
        eor.w	r3, r8, r9, ror #12
        ldr.w	r4, [r0, #0x80]
        ldr.w	r9, [r0, #0x8]
        ldr.w	r12, [r0, #0x84]
        eor.w	r2, r11, r6
        ldr.w	r11, [r0, #0x30]
        ldr.w	r6, [r0, #0x54]
        eor.w	r8, r3, r5, ror #19
        ldr.w	r3, [r0, #0xc]
        ldr.w	r5, [r0]
        eor.w	r12, r11, r12, ror #20
        str.w	r2, [r0, #0x4]
        ldr	r2, [r0, #0x58]
        ldr.w	r11, [r0, #0xa0]
        eor.w	r3, r12, r3, ror #7
        eor.w	r6, r5, r6, ror #30
        ldr.w	r12, [r0, #0xa8]
        eor.w	r5, r3, r2, ror #3
        ldr.w	r2, [r0, #0x9c]
        eor.w	r3, r6, r11, ror #19
        ldr.w	r11, [r0, #0x24]
        eor.w	r6, r5, r12, ror #22
        ldr.w	r5, [r0, #0xc4]
        ldr.w	r12, [r0, #0x74]
        eor.w	r7, r7, r4, ror #20
        eor.w	r11, r8, r11, ror #4
        ldr.w	r8, [r0, #0x4c]
        eor.w	r7, r7, r9, ror #6
        ror.w	r6, r6, #0x15
        ldr.w	r9, [r0, #0x20]
        eor.w	r4, lr, r1, ror #9
        eor.w	lr, r5, r8, ror #12
        ldr.w	r1, [r0, #0x1c]
        ldr.w	r8, [r0, #0x90]
        eor.w	r4, r4, r10, ror #30
        ldr	r5, [r0, #0x28]
        eor.w	r2, lr, r2, ror #19
        eor.w	r8, r8, r1, ror #18
        eor.w	r9, r2, r9, ror #4
        ldr.w	r2, [r0, #0x68]
        eor.w	r10, r3, r5, ror #27
        ldr.w	r1, [r0, #0x88]
        ldr.w	lr, [r0, #0xbc]
        eor.w	r12, r11, r12, ror #26
        eor.w	r5, r8, r2
        ldr	r3, [r0, #0x70]
        ldr.w	r8, [r0, #0x40]
        eor.w	r2, r4, r1, ror #11
        ldr.w	r11, [r0, #0x18]
        eor.w	lr, r5, lr, ror #19
        eor.w	r4, r9, r3, ror #27
        ldr.w	r3, [r0, #0x94]
        ldr	r1, [r0, #0x14]
        eor.w	r5, lr, r8, ror #1
        ldr.w	r9, [r0, #0x6c]
        eor.w	r3, r3, r11, ror #18
        ldr.w	lr, [r0, #0x5c]
        eor.w	r8, r6, r4, ror #10
        ror.w	r12, r12, #0xa
        eor.w	r2, r2, r1, ror #6
        eor.w	r11, r3, r9, ror #31
        ldr	r3, [r0, #0x7c]
        eor.w	lr, r7, lr, ror #3
        ldr.w	r1, [r0, #0xac]
        eor.w	r9, r12, r2, ror #25
        str.w	r9, [sp, #0xc]
        ldr.w	r9, [r0, #0xb8]
        eor.w	r10, r10, r3, ror #12
        eor.w	r1, lr, r1, ror #22
        ldr.w	r7, [r0, #0x64]
        eor.w	lr, r5, r10
        eor.w	r6, r6, r5, ror #31
        eor.w	r5, r11, r9, ror #18
        ldr	r3, [r0, #0x44]
        ldr.w	r11, [r0, #0xb4]
        eor.w	r9, r12, r1, ror #21
        eor.w	r10, r10, r2, ror #24
        str.w	r9, [sp]
        eor.w	r3, r5, r3, ror #1
        ldr.w	r12, [r0, #0x10]
        str.w	r6, [sp, #0x10]
        ldr.w	r5, [r0, #0x38]
        eor.w	r7, r7, r11, ror #8
        ldr.w	r6, [r0, #0xa4]
        eor.w	r2, r3, r1, ror #22
        ldr.w	r11, [r0, #0x8c]
        ldr.w	r1, [r0, #0x50]
        eor.w	r5, r7, r5, ror #30
        ldr.w	r9, [r0, #0x4]
        eor.w	r7, r8, r6, ror #20
        ldr.w	r6, [r0, #0xa4]
        eor.w	r1, r9, r1, ror #31
        str.w	r8, [sp, #0x4]
        eor.w	r11, r5, r11, ror #11
        ldr	r5, [r0, #0x2c]
        eor.w	r9, r1, r6, ror #20
        ldr.w	r6, [r0, #0x14]
        eor.w	r1, r11, r12, ror #6
        ldr.w	r11, [r0, #0x78]
        eor.w	r9, r9, r5, ror #27
        ldr.w	r12, [r0, #0x78]
        eor.w	r6, r2, r6, ror #31
        ror.w	r1, r1, #0x19
        eor.w	r11, r9, r11, ror #13
        ldr.w	r5, [r0, #0x5c]
        eor.w	r9, r1, r4, ror #9
        eor.w	r4, r8, r12, ror #13
        ldr.w	r8, [r0, #0x48]
        eor.w	r12, r3, r11, ror #31
        eor.w	r11, r11, r1
        eor.w	r3, r11, r5, ror #25
        ldr.w	r5, [r0, #0x94]
        eor.w	r8, r12, r8, ror #22
        eor.w	r1, r9, r5
        bic.w	r5, r1, r6, ror #15
        eor.w	r5, r5, r3, ror #23
        str.w	r5, [r0, #0x94]
        bic.w	r5, r7, r8, ror #24
        eor.w	r5, r5, r1, ror #20
        str.w	r5, [r0, #0xa4]
        bic.w	r1, r8, r1, ror #28
        eor.w	r5, r1, r6, ror #11
        str.w	r5, [r0, #0x48]
        bic.w	r5, r6, r3, ror #8
        ldr.w	r1, [r0, #0x20]
        eor.w	r6, r5, r7, ror #29
        ldr.w	r5, [r0, #0xb0]
        bic.w	r3, r3, r7, ror #21
        ldr.w	r7, [r0, #0x6c]
        str.w	r6, [r0, #0x14]
        eor.w	r6, lr, r1, ror #14
        eor.w	r1, r2, r5, ror #2
        ldr.w	r5, [r0, #0x30]
        eor.w	r7, r9, r7, ror #31
        eor.w	r3, r3, r8, ror #13
        str.w	r3, [r0, #0x5c]
        eor.w	r3, r10, r5, ror #21
        ldr.w	r8, [r0, #0x88]
        bic.w	r5, r6, r7, ror #24
        eor.w	r5, r5, r1, ror #1
        str.w	r5, [r0, #0x30]
        bic.w	r5, r4, r6, ror #5
        eor.w	r5, r5, r7, ror #29
        str.w	r5, [r0, #0xb0]
        bic.w	r7, r7, r1, ror #9
        str.w	r9, [sp, #0x8]
        bic.w	r1, r1, r3, ror #3
        ldr.w	r5, [r0, #0xc4]
        eor.w	r7, r7, r3, ror #12
        str.w	r7, [r0, #0x78]
        bic.w	r7, r3, r4, ror #23
        eor.w	r3, lr, r5, ror #10
        eor.w	r1, r1, r4, ror #26
        ldr.w	r4, [r0, #0xc]
        eor.w	r7, r7, r6, ror #28
        str.w	r7, [r0, #0x6c]
        ldr.w	r7, [r0, #0x44]
        str.w	r1, [r0, #0x20]
        eor.w	r6, r2, r8, ror #4
        eor.w	r5, r10, r4, ror #28
        ldr.w	r4, [r0, #0x54]
        eor.w	r1, r9, r7, ror #1
        ldr.w	r8, [sp]
        eor.w	r7, r8, r4, ror #30
        bic.w	r4, r1, r6, ror #20
        eor.w	r4, r4, r5, ror #23
        str.w	r4, [r0, #0x88]
        bic.w	r4, r5, r7, ror #19
        eor.w	r4, r4, r3, ror #23
        str.w	r4, [r0, #0x54]
        ldr.w	r4, [r0, #0x18]
        bic.w	r5, r6, r5, ror #3
        eor.w	r5, r5, r7, ror #22
        str.w	r5, [r0, #0xc]
        bic.w	r5, r3, r1, ror #18
        eor.w	r5, r5, r6, ror #6
        str.w	r5, [r0, #0x44]
        bic.w	r7, r7, r3, ror #4
        ldr.w	r3, [r0, #0xac]
        eor.w	r5, r9, r4, ror #18
        ldr.w	r9, [r0, #0x28]
        ldr.w	r4, [r0, #0x98]
        eor.w	r1, r7, r1, ror #22
        eor.w	r7, r11, r3, ror #12
        ldr.w	r3, [r0, #0x60]
        eor.w	r6, r8, r9, ror #27
        str.w	r1, [r0, #0xc4]
        eor.w	r4, r12, r4, ror #29
        eor.w	r3, r2, r3, ror #25
        bic.w	r1, r7, r6, ror #13
        bic.w	r9, r6, r4, ror #1
        eor.w	r9, r9, r5, ror #25
        str.w	r9, [r0, #0xac]
        eor.w	r9, r1, r4, ror #14
        str.w	r9, [r0, #0x60]
        bic.w	r1, r4, r5, ror #24
        ldr.w	r9, [r0, #0x3c]
        eor.w	r1, r1, r3, ror #20
        str.w	r1, [r0, #0x28]
        ldr.w	r4, [r0, #0xbc]
        bic.w	r5, r5, r3, ror #28
        eor.w	r5, r5, r7, ror #26
        str.w	r5, [r0, #0x98]
        bic.w	r1, r3, r7, ror #30
        ldr	r3, [r0, #0x74]
        eor.w	r6, r1, r6, ror #11
        ldr.w	r5, [r0, #0xa0]
        eor.w	r7, r2, r9, ror #23
        ldr.w	r9, [sp, #0xc]
        str.w	r6, [r0, #0x18]
        eor.w	r6, r12, r3, ror #4
        ldr.w	r1, [r0]
        eor.w	r4, r9, r4, ror #19
        eor.w	r5, r8, r5, ror #19
        eor.w	r2, r8, r1
        bic.w	r3, r2, r6, ror #25
        ldr.w	r1, [r0, #0x84]
        eor.w	r3, r3, r4, ror #21
        str.w	r3, [r0, #0xbc]
        bic.w	r3, r6, r4, ror #28
        eor.w	r1, r10, r1, ror #9
        bic.w	r4, r4, r7, ror #21
        eor.w	r3, r3, r7, ror #17
        str.w	r3, [r0, #0x3c]
        eor.w	r4, r4, r1, ror #21
        str.w	r4, [r0, #0x84]
        bic.w	r3, r7, r1
        ldr.w	r7, [r0, #0x10]
        bic.w	r1, r1, r2, ror #22
        ldr.w	r4, [r0, #0x58]
        eor.w	r3, r2, r3, ror #10
        ldr.w	r2, [sp, #0x10]
        eor.w	r1, r1, r6, ror #15
        eor.w	r6, r10, r4, ror #24
        ldr.w	r4, [r0, #0x7c]
        eor.w	r7, r2, r7, ror #31
        str.w	r1, [r0, #0x74]
        ldr	r1, [sp, #0x14]
        eor.w	r8, r8, r4, ror #12
        ldr	r4, [r1, #0x8]
        ldr.w	r1, [r0, #0x4c]
        eor.w	r4, r4, r3
        bic.w	r3, r6, r5, ror #21
        str.w	r4, [r0]
        bic.w	r4, r7, r6, ror #8
        eor.w	r1, lr, r1, ror #22
        eor.w	r4, r4, r5, ror #29
        str.w	r4, [r0, #0x10]
        ldr.w	r4, [r0, #0x90]
        eor.w	r3, r3, r1, ror #12
        str.w	r3, [r0, #0x58]
        bic.w	r3, r5, r1, ror #23
        eor.w	r4, r9, r4
        bic.w	r5, r4, r7, ror #16
        eor.w	r6, r5, r6, ror #24
        str.w	r6, [r0, #0x90]
        eor.w	r3, r3, r4, ror #19
        ldr.w	r5, [r0, #0xb4]
        bic.w	r6, r1, r4, ror #28
        ldr.w	r4, [r0, #0x34]
        eor.w	r6, r6, r7, ror #12
        ldr.w	r7, [r0, #0x24]
        str.w	r6, [r0, #0x4c]
        eor.w	r6, r2, r5, ror #1
        eor.w	r4, r11, r4, ror #22
        str.w	r3, [r0, #0xa0]
        eor.w	r7, r12, r7, ror #14
        ldr.w	r3, [r0, #0x68]
        bic.w	r5, r4, r8, ror #24
        bic.w	r1, r6, r4, ror #2
        eor.w	r3, r9, r3
        eor.w	r5, r5, r7, ror #29
        eor.w	r1, r1, r8, ror #26
        str.w	r1, [r0, #0x24]
        str.w	r5, [r0, #0x68]
        bic.w	r5, r3, r6, ror #10
        eor.w	r4, r5, r4, ror #12
        ldr.w	r5, [r0, #0xc0]
        str.w	r4, [r0, #0x7c]
        bic.w	r8, r8, r7, ror #5
        bic.w	r4, r7, r3, ror #23
        ldr.w	r7, [r0, #0x40]
        eor.w	r1, r12, r5, ror #10
        eor.w	r5, r8, r3, ror #28
        ldr.w	r8, [r0, #0x8]
        str.w	r5, [r0, #0xb4]
        eor.w	r7, r9, r7, ror #1
        eor.w	r4, r4, r6, ror #1
        ldr.w	r5, [r0, #0x8c]
        ldr.w	r12, [r0, #0x50]
        eor.w	r6, r11, r8, ror #28
        bic.w	r3, r1, r7, ror #17
        ldr.w	r8, [sp, #0x4]
        str.w	r4, [r0, #0x34]
        eor.w	r4, r2, r5, ror #4
        eor.w	r12, r8, r12, ror #31
        bic.w	r5, r4, r6, ror #2
        eor.w	r3, r3, r4, ror #6
        eor.w	r5, r5, r12, ror #21
        str.w	r5, [r0, #0x8]
        bic.w	r5, r7, r4, ror #21
        ldr.w	r4, [r0, #0x9c]
        eor.w	r5, r5, r6, ror #23
        str.w	r5, [r0, #0x8c]
        bic.w	r5, r6, r12, ror #19
        ldr.w	r6, [r0, #0x2c]
        eor.w	r5, r5, r1, ror #24
        str.w	r5, [r0, #0x50]
        eor.w	r5, lr, r4, ror #29
        eor.w	r6, r8, r6, ror #27
        ldr.w	r4, [r0, #0x1c]
        str.w	r3, [r0, #0x40]
        bic.w	r1, r12, r1, ror #5
        bic.w	r12, r6, r5, ror #1
        ldr.w	r3, [r0, #0xa8]
        eor.w	r9, r9, r4, ror #18
        ldr.w	r4, [r0, #0x4]
        eor.w	r7, r1, r7, ror #22
        str.w	r7, [r0, #0xc0]
        eor.w	r10, r10, r3, ror #11
        ldr.w	r1, [r0, #0x64]
        eor.w	r3, r12, r9, ror #25
        eor.w	r12, r8, r4
        str.w	r3, [r0, #0xa8]
        bic.w	r7, r10, r6, ror #12
        eor.w	r7, r7, r5, ror #13
        str.w	r7, [r0, #0x64]
        eor.w	r8, r2, r1, ror #25
        ldr.w	r1, [r0, #0xb8]
        ldr	r3, [r0, #0x70]
        bic.w	r5, r5, r9, ror #24
        bic.w	r4, r8, r10, ror #30
        ldr.w	r7, [r0, #0x80]
        eor.w	r5, r5, r8, ror #21
        str.w	r5, [r0, #0x2c]
        eor.w	r5, r4, r6, ror #10
        ldr	r6, [r0, #0x38]
        eor.w	r3, lr, r3, ror #5
        ldr.w	lr, [r0, #0x10]
        str.w	r5, [r0, #0x1c]
        eor.w	r11, r11, r7, ror #10
        eor.w	r2, r2, r6, ror #23
        ldr	r6, [sp, #0x8]
        bic.w	r5, r11, r12, ror #22
        ldr	r4, [sp, #0x14]
        eor.w	r5, r5, r3, ror #15
        str.w	r5, [r0, #0x70]
        ldr	r7, [r4, #0xc]
        bic.w	r5, r9, r8, ror #29
        ldr.w	r4, [r0, #0x48]
        bic.w	r9, r2, r11, ror #31
        eor.w	r5, r5, r10, ror #27
        str.w	r5, [r0, #0x9c]
        eor.w	r8, r12, r9, ror #11
        ldr.w	r5, [r0, #0x74]
        ldr.w	r10, [r0, #0x58]
        eor.w	r1, r6, r1, ror #18
        eor.w	r8, r7, r8
        eor.w	r9, r5, r4, ror #12
        ldr.w	r4, [r0, #0x24]
        bic.w	r5, r1, r2, ror #21
        eor.w	r5, r5, r11, ror #20
        str.w	r5, [r0, #0x80]
        ldr.w	r7, [r0, #0xc4]
        bic.w	r5, r3, r1, ror #29
        eor.w	r2, r5, r2, ror #18
        str.w	r8, [r0, #0x4]
        str.w	r2, [r0, #0x38]
        eor.w	r9, r9, r4, ror #19
        bic.w	r6, r12, r3, ror #25
        ldr.w	r2, [r0, #0x80]
        eor.w	r3, r9, r7, ror #4
        ldr.w	r8, [r0, #0x30]
        eor.w	r9, r2, r10, ror #20
        ldr	r7, [r0, #0x8]
        eor.w	r6, r6, r1, ror #22
        ldr.w	r2, [r0, #0x38]
        eor.w	r8, r9, r8, ror #6
        ldr.w	r10, [r0, #0xb0]
        str.w	r6, [r0, #0xb8]
        eor.w	r5, r2, lr, ror #9
        ldr.w	r11, [r0, #0x8c]
        eor.w	r7, r8, r7, ror #3
        ldr.w	r4, [r0, #0x4c]
        eor.w	r8, r5, r10, ror #30
        ldr.w	r6, [r0, #0x70]
        ldr.w	r12, [r0, #0x5c]
        ldr.w	r9, [r0, #0x68]
        ldr.w	r5, [r0, #0x84]
        eor.w	lr, r6, r4, ror #12
        ldr.w	r6, [r0, #0x34]
        eor.w	r12, r5, r12, ror #20
        ldr.w	r1, [r0, #0x94]
        ldr	r5, [r0, #0x60]
        ldr.w	r10, [r0, #0xbc]
        ldr	r2, [r0, #0xc]
        eor.w	r12, r12, r6, ror #7
        eor.w	r10, r10, r1, ror #18
        ldr.w	r4, [r0, #0x3c]
        eor.w	r1, r8, r11, ror #11
        ldr.w	r11, [r0, #0x9c]
        eor.w	r6, r12, r2, ror #3
        ldr.w	r8, [r0, #0x14]
        eor.w	r9, r10, r9, ror #31
        ldr.w	r10, [r0, #0x44]
        eor.w	r3, r3, r11, ror #26
        ldr.w	r2, [r0, #0x20]
        eor.w	r12, r4, r8, ror #8
        ldr.w	r8, [r0, #0xac]
        eor.w	r11, r9, r10, ror #18
        ldr.w	r9, [r0, #0xb4]
        ldr.w	r4, [r0, #0x88]
        eor.w	r10, r1, r5, ror #6
        ldr.w	r1, [r0, #0xc0]
        eor.w	r5, r7, r8, ror #22
        eor.w	r12, r12, r9, ror #30
        ldr.w	r9, [r0, #0xa4]
        eor.w	lr, lr, r2, ror #19
        ror.w	r3, r3, #0xa
        eor.w	r2, r12, r4, ror #11
        ldr.w	r12, [r0]
        ldr.w	r8, [r0, #0x7c]
        eor.w	r7, r3, r10, ror #25
        ldr.w	r4, [r0, #0xa8]
        eor.w	r9, r12, r9, ror #30
        eor.w	r1, lr, r1, ror #4
        ldr.w	r12, [r0, #0x54]
        eor.w	lr, r9, r8, ror #19
        ldr.w	r9, [r0, #0x98]
        eor.w	r6, r6, r4, ror #22
        ldr.w	r8, [r0, #0x2c]
        eor.w	lr, lr, r12, ror #27
        ldr.w	r4, [r0, #0x90]
        eor.w	r1, r1, r9, ror #27
        ldr.w	r9, [r0, #0xb8]
        eor.w	lr, lr, r8, ror #12
        ldr.w	r12, [r0, #0x6c]
        eor.w	r4, r9, r4, ror #18
        ldr.w	r9, [r0, #0x1c]
        ldr.w	r8, [r0, #0x64]
        eor.w	r10, lr, r10, ror #24
        str.w	r7, [sp, #0xc]
        eor.w	r4, r4, r12
        eor.w	r7, r3, r5, ror #21
        ldr.w	r12, [r0, #0x40]
        str.w	r7, [sp]
        eor.w	r3, r11, r9, ror #1
        eor.w	r7, r2, r8, ror #6
        ldr.w	r9, [r0, #0x18]
        eor.w	r12, r4, r12, ror #19
        ldr.w	r11, [r0, #0xa0]
        ror.w	r7, r7, #0x19
        eor.w	r2, r3, r5, ror #22
        ldr.w	r8, [r0, #0x4]
        eor.w	r5, r12, r9, ror #1
        eor.w	r9, r7, r1, ror #9
        ldr.w	r4, [r0, #0x78]
        ror.w	r6, r6, #0x15
        eor.w	r11, r8, r11, ror #31
        str.w	r9, [sp, #0x8]
        eor.w	r8, r6, r1, ror #10
        ldr.w	r1, [r0, #0x10]
        eor.w	r6, r6, r5, ror #31
        eor.w	lr, r5, lr
        ldr.w	r12, [r0, #0x28]
        eor.w	r4, r11, r4, ror #20
        ldr.w	r11, [r0, #0x50]
        ldr.w	r5, [r0, #0x28]
        eor.w	r1, r2, r1, ror #2
        str.w	r6, [sp, #0x10]
        eor.w	r4, r4, r11, ror #27
        ldr.w	r11, [r0, #0x78]
        eor.w	r5, r8, r5, ror #13
        ldr.w	r6, [r0, #0x84]
        eor.w	r12, r4, r12, ror #13
        str.w	r8, [sp, #0x4]
        eor.w	r4, r8, r11, ror #20
        ldr.w	r8, [r0, #0x68]
        eor.w	r11, r12, r7
        eor.w	r6, r10, r6, ror #21
        eor.w	r12, r3, r12, ror #31
        eor.w	r3, r9, r8, ror #31
        ldr.w	r8, [r0, #0xc0]
        bic.w	r7, r1, r6, ror #3
        eor.w	r7, r7, r5, ror #26
        eor.w	r8, lr, r8, ror #14
        str.w	r7, [r0, #0xc0]
        bic.w	r7, r3, r1, ror #9
        eor.w	r7, r7, r6, ror #12
        str.w	r7, [r0, #0x28]
        bic.w	r7, r5, r8, ror #5
        eor.w	r7, r7, r3, ror #29
        str.w	r7, [r0, #0x10]
        bic.w	r7, r8, r3, ror #24
        bic.w	r3, r6, r5, ror #23
        ldr.w	r5, [r0, #0x48]
        eor.w	r6, r7, r1, ror #1
        ldr.w	r7, [r0, #0x8]
        eor.w	r1, r3, r8, ror #28
        ldr.w	r8, [r0, #0x60]
        eor.w	r5, r12, r5, ror #22
        str.w	r6, [r0, #0x84]
        eor.w	r3, r11, r7, ror #25
        ldr.w	r6, [r0, #0xbc]
        eor.w	r8, r2, r8, ror #31
        eor.w	r6, r9, r6
        str.w	r1, [r0, #0x68]
        bic.w	r7, r4, r5, ror #24
        eor.w	r7, r7, r6, ror #20
        str.w	r7, [r0, #0x78]
        bic.w	r7, r5, r6, ror #28
        ldr.w	r1, [r0, #0x70]
        eor.w	r7, r7, r8, ror #11
        str.w	r7, [r0, #0x48]
        bic.w	r7, r8, r3, ror #8
        bic.w	r8, r6, r8, ror #15
        ldr.w	r6, [r0, #0x8c]
        eor.w	r7, r7, r4, ror #29
        str.w	r7, [r0, #0x60]
        bic.w	r4, r3, r4, ror #21
        ldr.w	r7, [r0, #0x34]
        eor.w	r3, r8, r3, ror #23
        ldr.w	r8, [sp]
        eor.w	r5, r4, r5, ror #13
        ldr.w	r4, [r0, #0xa4]
        str.w	r5, [r0, #0x8]
        eor.w	r6, r2, r6, ror #4
        eor.w	r5, r10, r7, ror #28
        ldr.w	r7, [r0, #0x1c]
        str.w	r3, [r0, #0xbc]
        eor.w	r4, r8, r4, ror #30
        eor.w	r3, lr, r1, ror #10
        eor.w	r7, r9, r7, ror #1
        bic.w	r1, r5, r4, ror #19
        eor.w	r1, r1, r3, ror #23
        str.w	r1, [r0, #0xa4]
        bic.w	r1, r6, r5, ror #3
        eor.w	r1, r1, r4, ror #22
        str.w	r1, [r0, #0x34]
        bic.w	r1, r7, r6, ror #20
        eor.w	r1, r1, r5, ror #23
        str.w	r1, [r0, #0x8c]
        bic.w	r4, r4, r3, ror #4
        ldr.w	r1, [r0, #0x94]
        bic.w	r3, r3, r7, ror #18
        ldr.w	r5, [r0, #0x24]
        eor.w	r6, r3, r6, ror #6
        str.w	r6, [r0, #0x1c]
        eor.w	r1, r9, r1, ror #18
        ldr.w	r9, [r0, #0x54]
        eor.w	r6, r12, r5, ror #29
        ldr.w	r5, [r0, #0x38]
        eor.w	r3, r4, r7, ror #22
        ldr.w	r4, [r0, #0xac]
        str.w	r3, [r0, #0x70]
        eor.w	r7, r8, r9, ror #27
        eor.w	r9, r2, r5, ror #25
        eor.w	r5, r11, r4, ror #12
        bic.w	r3, r6, r1, ror #24
        eor.w	r4, r3, r9, ror #20
        str.w	r4, [r0, #0x54]
        bic.w	r4, r5, r7, ror #13
        eor.w	r4, r4, r6, ror #14
        str.w	r4, [r0, #0x38]
        bic.w	r3, r9, r5, ror #30
        ldr	r4, [r0, #0x5c]
        eor.w	r3, r3, r7, ror #11
        str.w	r3, [r0, #0x94]
        bic.w	r6, r7, r6, ror #1
        ldr.w	r7, [r0, #0xb0]
        eor.w	r6, r6, r1, ror #25
        str.w	r6, [r0, #0xac]
        bic.w	r9, r1, r9, ror #28
        ldr	r1, [sp, #0x14]
        eor.w	r3, r10, r4, ror #9
        ldr	r6, [r0, #0x40]
        eor.w	r7, r2, r7, ror #23
        ldr.w	r2, [r0]
        eor.w	r9, r9, r5, ror #26
        ldr	r4, [r1, #0x10]
        str.w	r9, [r0, #0x24]
        bic.w	r1, r7, r3
        eor.w	r5, r8, r2
        ldr.w	r9, [sp, #0xc]
        eor.w	r2, r5, r1, ror #10
        ldr.w	r1, [r0, #0x9c]
        eor.w	r6, r9, r6, ror #19
        eor.w	r4, r4, r2
        bic.w	r2, r3, r5, ror #22
        eor.w	r1, r12, r1, ror #4
        str.w	r4, [r0]
        bic.w	r4, r6, r7, ror #21
        eor.w	r3, r4, r3, ror #21
        ldr.w	r4, [r0, #0x4c]
        bic.w	r5, r5, r1, ror #25
        str.w	r3, [r0, #0x5c]
        eor.w	r2, r2, r1, ror #15
        str.w	r2, [r0, #0x9c]
        eor.w	r4, lr, r4, ror #22
        ldr.w	r2, [r0, #0xc]
        eor.w	r3, r5, r6, ror #21
        ldr.w	r5, [r0, #0x7c]
        str.w	r3, [r0, #0x40]
        bic.w	r3, r1, r6, ror #28
        ldr.w	r6, [r0, #0xb8]
        eor.w	r1, r3, r7, ror #17
        str.w	r1, [r0, #0xb0]
        eor.w	r5, r8, r5, ror #19
        eor.w	r3, r9, r6
        eor.w	r6, r10, r2, ror #24
        bic.w	r1, r5, r4, ror #23
        ldr.w	r7, [r0, #0x64]
        eor.w	r1, r1, r3, ror #19
        ldr.w	r2, [sp, #0x10]
        str.w	r1, [r0, #0x7c]
        bic.w	r1, r6, r5, ror #21
        eor.w	r7, r2, r7, ror #31
        eor.w	r1, r1, r4, ror #12
        str.w	r1, [r0, #0xc]
        bic.w	r1, r4, r3, ror #28
        ldr.w	r4, [r0, #0x2c]
        eor.w	r1, r1, r7, ror #12
        str.w	r1, [r0, #0x4c]
        bic.w	r1, r3, r7, ror #16
        ldr.w	r3, [r0, #0xc4]
        eor.w	r1, r1, r6, ror #24
        str.w	r1, [r0, #0xb8]
        ldr.w	r1, [r0, #0x14]
        bic.w	r6, r7, r6, ror #8
        ldr.w	r7, [r0, #0x74]
        eor.w	r5, r6, r5, ror #29
        eor.w	r8, r8, r4, ror #12
        ldr.w	r6, [r0, #0x80]
        str.w	r5, [r0, #0x64]
        eor.w	r3, r12, r3, ror #14
        ldr.w	r4, [r0, #0x6c]
        eor.w	r5, r2, r1, ror #1
        eor.w	r1, r11, r6, ror #22
        eor.w	r4, r9, r4
        bic.w	r6, r8, r3, ror #5
        eor.w	r6, r6, r4, ror #28
        str.w	r6, [r0, #0x14]
        eor.w	r12, r12, r7, ror #10
        ldr.w	r7, [r0, #0xa8]
        bic.w	r6, r3, r4, ror #23
        bic.w	r4, r4, r5, ror #10
        eor.w	r4, r4, r1, ror #12
        str.w	r4, [r0, #0x2c]
        eor.w	r7, r10, r7, ror #11
        ldr.w	r4, [r0, #0x90]
        bic.w	r10, r1, r8, ror #24
        bic.w	r1, r5, r1, ror #2
        eor.w	r8, r1, r8, ror #26
        ldr.w	r1, [r0, #0x18]
        eor.w	r4, r9, r4, ror #18
        str.w	r8, [r0, #0xc4]
        eor.w	r10, r10, r3, ror #29
        ldr.w	r8, [r0, #0x30]
        eor.w	r1, r9, r1, ror #1
        ldr.w	r3, [r0, #0x88]
        str.w	r10, [r0, #0x6c]
        eor.w	r5, r6, r5, ror #1
        ldr.w	r10, [r0, #0xa0]
        eor.w	r9, r11, r8, ror #28
        ldr.w	r8, [sp, #0x4]
        eor.w	r6, r2, r3, ror #4
        bic.w	r3, r12, r1, ror #17
        str.w	r5, [r0, #0x80]
        eor.w	r10, r8, r10, ror #31
        eor.w	r5, r3, r6, ror #6
        str.w	r5, [r0, #0x18]
        bic.w	r5, r1, r6, ror #21
        bic.w	r3, r10, r12, ror #5
        eor.w	r1, r3, r1, ror #22
        ldr.w	r3, [r0, #0x3c]
        str.w	r1, [r0, #0x74]
        eor.w	r5, r5, r9, ror #23
        bic.w	r6, r6, r9, ror #2
        ldr.w	r1, [r0, #0x50]
        str.w	r5, [r0, #0x88]
        eor.w	r6, r6, r10, ror #21
        eor.w	r3, r2, r3, ror #25
        ldr.w	r5, [r0, #0x20]
        str.w	r6, [r0, #0x30]
        eor.w	r6, r8, r1, ror #27
        bic.w	r10, r9, r10, ror #19
        eor.w	r5, lr, r5, ror #29
        eor.w	r12, r10, r12, ror #24
        ldr.w	r10, [r0, #0xb4]
        bic.w	r9, r6, r5, ror #1
        eor.w	r1, r9, r4, ror #25
        str.w	r1, [r0, #0xa8]
        ldr.w	r9, [sp, #0x8]
        bic.w	r1, r5, r4, ror #24
        str.w	r12, [r0, #0xa0]
        bic.w	r12, r7, r6, ror #12
        eor.w	r12, r12, r5, ror #13
        str.w	r12, [r0, #0x3c]
        bic.w	r12, r4, r3, ror #29
        ldr	r4, [r0, #0x58]
        eor.w	r12, r12, r7, ror #27
        str.w	r12, [r0, #0x20]
        eor.w	r5, r2, r10, ror #23
        ldr	r2, [r0, #0x44]
        eor.w	r1, r1, r3, ror #21
        str.w	r1, [r0, #0x50]
        bic.w	r1, r3, r7, ror #30
        ldr.w	r7, [r0, #0x9c]
        eor.w	r1, r1, r6, ror #10
        ldr.w	r6, [r0, #0x98]
        eor.w	r9, r9, r2, ror #18
        ldr.w	r12, [r0, #0x4]
        eor.w	r3, r11, r4, ror #10
        ldr.w	r11, [r0, #0x48]
        eor.w	lr, lr, r6, ror #5
        eor.w	r12, r8, r12
        bic.w	r8, r9, r5, ror #21
        ldr.w	r10, [r0, #0xc4]
        eor.w	r2, r7, r11, ror #12
        ldr.w	r11, [r0, #0x20]
        bic.w	r7, r12, lr, ror #25
        str.w	r1, [r0, #0x90]
        eor.w	r4, r7, r9, ror #22
        str.w	r4, [r0, #0x44]
        eor.w	r6, r2, r10, ror #19
        ldr.w	r7, [r0, #0x64]
        bic.w	r1, r3, r12, ror #22
        ldr.w	r10, [r0, #0x70]
        eor.w	r2, r1, lr, ror #15
        str.w	r2, [r0, #0x98]
        bic.w	r1, lr, r9, ror #29
        ldr.w	r2, [r0, #0xc]
        eor.w	r8, r8, r3, ror #20
        str.w	r8, [r0, #0x58]
        eor.w	r4, r1, r5, ror #18
        str.w	r4, [r0, #0xb4]
        bic.w	r5, r5, r3, ror #31
        ldr	r3, [r0, #0x30]
        eor.w	r10, r6, r10, ror #4
        ldr.w	r8, [sp, #0x14]
        eor.w	r5, r12, r5, ror #11
        ldr.w	lr, [r0, #0x58]
        ldr.w	r1, [r0, #0x10]
        ldr.w	r12, [r0, #0x84]
        eor.w	r9, lr, r2, ror #20
        ldr.w	r2, [r8, #0x14]
        eor.w	r8, r10, r11, ror #26
        ldr.w	lr, [r0, #0xb4]
        eor.w	r12, r9, r12, ror #6
        ldr.w	r9, [r0, #0xac]
        eor.w	r10, lr, r7, ror #9
        ror.w	r8, r8, #0xa
        eor.w	r6, r12, r3, ror #3
        eor.w	r3, r2, r5
        eor.w	lr, r10, r1, ror #30
        ldr.w	r4, [r0, #0x88]
        ldr	r2, [r0, #0x38]
        eor.w	r7, r6, r9, ror #22
        str.w	r3, [r0, #0x4]
        ldr.w	r11, [r0, #0x1c]
        ldr.w	r5, [r0, #0x6c]
        ldr.w	r1, [r0, #0xbc]
        eor.w	r6, r8, r7, ror #21
        eor.w	r3, lr, r4, ror #11
        ldr.w	r12, [r0, #0x90]
        ldr.w	r10, [r0, #0x4]
        ldr.w	lr, [r0, #0x8]
        ldr.w	r9, [r0, #0x7c]
        eor.w	r4, r3, r2, ror #6
        ldr.w	r2, [r0, #0x40]
        str.w	r6, [sp]
        ldr.w	r3, [r0, #0x98]
        ldr.w	r6, [r0, #0x4c]
        eor.w	r1, r2, r1, ror #18
        eor.w	r10, r10, r9, ror #31
        ldr.w	r9, [r0, #0x5c]
        eor.w	r2, r1, r5, ror #31
        ldr.w	r5, [r0, #0xb8]
        eor.w	lr, r9, lr, ror #20
        ldr.w	r1, [r0, #0x80]
        eor.w	r6, r3, r6, ror #12
        ldr.w	r3, [r0, #0x44]
        eor.w	r2, r2, r11, ror #18
        ldr.w	r11, [r0, #0x28]
        eor.w	r9, r3, r5, ror #18
        ldr.w	r5, [r0, #0xc0]
        eor.w	r8, r8, r4, ror #25
        str.w	r8, [sp, #0xc]
        eor.w	r11, r10, r11, ror #20
        ldr.w	r10, [r0, #0x68]
        eor.w	r6, r6, r5, ror #19
        ldr	r5, [r0, #0x34]
        eor.w	r8, lr, r1, ror #7
        ldr.w	lr, [r0, #0xa0]
        eor.w	r1, r9, r10
        ldr.w	r3, [r0, #0xa8]
        ldr.w	r9, [r0, #0x60]
        eor.w	r8, r8, r5, ror #3
        eor.w	r10, r2, r12, ror #1
        ldr	r5, [r0, #0x54]
        eor.w	lr, r11, lr, ror #27
        ldr.w	r11, [r0, #0x74]
        eor.w	r8, r8, r3, ror #22
        ldr.w	r12, [r0, #0xb0]
        ldr.w	r3, [r0, #0x78]
        eor.w	r2, r10, r7, ror #22
        eor.w	r12, r12, r9, ror #8
        ldr.w	r9, [r0, #0x18]
        eor.w	r7, r6, r11, ror #4
        ldr.w	r6, [r0, #0x14]
        eor.w	r11, lr, r5, ror #13
        ldr.w	r5, [r0]
        eor.w	lr, r1, r9, ror #19
        ldr.w	r9, [r0, #0x8c]
        eor.w	r6, r12, r6, ror #30
        ldr.w	r1, [r0, #0xa4]
        eor.w	r12, r10, r11, ror #31
        ldr.w	r10, [r0, #0x2c]
        eor.w	r5, r5, r3, ror #30
        ldr.w	r3, [r0, #0x94]
        ror.w	r8, r8, #0x15
        eor.w	r9, r6, r9, ror #11
        eor.w	r5, r5, r10, ror #19
        ldr.w	r10, [r0, #0x24]
        eor.w	r6, lr, r3, ror #1
        ldr	r3, [r0, #0x50]
        eor.w	r5, r5, r1, ror #27
        ldr.w	lr, [r0, #0x3c]
        eor.w	r1, r7, r10, ror #27
        ldr.w	r7, [r0, #0x38]
        eor.w	r10, r5, r3, ror #12
        ldr.w	r5, [r0, #0x28]
        ldr.w	r3, [r0, #0x48]
        eor.w	r9, r9, lr, ror #6
        eor.w	lr, r6, r10
        eor.w	r6, r8, r6, ror #31
        eor.w	r7, r2, r7, ror #31
        str.w	r6, [sp, #0x10]
        eor.w	r10, r10, r4, ror #24
        ror.w	r9, r9, #0x19
        eor.w	r4, r12, r3, ror #22
        ldr.w	r3, [r0, #0x40]
        ldr.w	r6, [r0, #0x30]
        eor.w	r8, r8, r1, ror #10
        eor.w	r11, r11, r9
        eor.w	r9, r9, r1, ror #9
        str.w	r8, [sp, #0x4]
        eor.w	r1, r11, r6, ror #25
        eor.w	r3, r9, r3
        eor.w	r6, r8, r5, ror #20
        bic.w	r5, r3, r7, ror #15
        eor.w	r5, r5, r1, ror #23
        ror.w	r5, r5, #0x12
        str.w	r5, [r0, #0x40]
        bic.w	r5, r1, r6, ror #21
        eor.w	r5, r5, r4, ror #13
        bic.w	r1, r7, r1, ror #8
        ror.w	r5, r5, #0x9
        eor.w	r1, r1, r6, ror #29
        str.w	r5, [r0, #0x30]
        bic.w	r5, r6, r4, ror #24
        ror.w	r1, r1, #0x1
        eor.w	r6, r5, r3, ror #20
        bic.w	r3, r4, r3, ror #28
        ldr.w	r5, [r0, #0x54]
        str.w	r1, [r0, #0x38]
        ldr.w	r1, [r0, #0x74]
        eor.w	r3, r3, r7, ror #11
        ldr.w	r7, [r0, #0x6c]
        eor.w	r4, r8, r5, ror #13
        ldr.w	r8, [r0, #0x5c]
        ror.w	r3, r3, #0x16
        eor.w	r1, lr, r1, ror #14
        str.w	r3, [r0, #0x48]
        eor.w	r5, r9, r7, ror #31
        eor.w	r3, r10, r8, ror #21
        ldr.w	r7, [r0, #0x64]
        ror.w	r8, r6, #0x1e
        bic.w	r6, r4, r1, ror #5
        str.w	r8, [r0, #0x28]
        eor.w	r6, r6, r5, ror #29
        eor.w	r7, r2, r7, ror #2
        ror.w	r6, r6, #0x17
        bic.w	r8, r3, r4, ror #23
        str.w	r6, [r0, #0x64]
        eor.w	r6, r8, r1, ror #28
        str.w	r6, [r0, #0x6c]
        bic.w	r6, r7, r3, ror #3
        eor.w	r6, r6, r4, ror #26
        ldr.w	r4, [r0, #0x78]
        bic.w	r1, r1, r5, ror #24
        ldr.w	r8, [r0, #0x80]
        ror.w	r6, r6, #0x1d
        eor.w	r1, r1, r7, ror #1
        str.w	r6, [r0, #0x74]
        ldr.w	r6, [r0, #0x88]
        bic.w	r7, r5, r7, ror #9
        ror.w	r1, r1, #0x1c
        eor.w	r5, r10, r8, ror #28
        ldr.w	r8, [sp]
        str.w	r1, [r0, #0x5c]
        eor.w	r6, r2, r6, ror #4
        eor.w	r4, r8, r4, ror #30
        eor.w	r3, r7, r3, ror #12
        ldr.w	r7, [r0, #0x98]
        bic.w	r1, r6, r5, ror #3
        ror.w	r3, r3, #0x14
        eor.w	r1, r1, r4, ror #22
        str.w	r3, [r0, #0x54]
        eor.w	r3, lr, r7, ror #10
        ror.w	r1, r1, #0x18
        ldr.w	r7, [r0, #0x90]
        str.w	r1, [r0, #0x80]
        bic.w	r1, r5, r4, ror #19
        eor.w	r1, r1, r3, ror #23
        eor.w	r7, r9, r7, ror #1
        ror.w	r1, r1, #0x1b
        bic.w	r4, r4, r3, ror #4
        str.w	r1, [r0, #0x78]
        bic.w	r1, r7, r6, ror #20
        eor.w	r1, r1, r5, ror #23
        ldr.w	r5, [r0, #0xbc]
        bic.w	r3, r3, r7, ror #18
        str.w	r9, [sp, #0x8]
        eor.w	r3, r3, r6, ror #6
        ror.w	r6, r1, #0x4
        eor.w	r9, r9, r5, ror #18
        ldr.w	r1, [r0, #0xc4]
        eor.w	r4, r4, r7, ror #22
        ldr.w	r7, [r0, #0xa4]
        str.w	r6, [r0, #0x88]
        ldr.w	r5, [r0, #0xb4]
        ror.w	r4, r4, #0xe
        eor.w	r1, r12, r1, ror #29
        str.w	r4, [r0, #0x98]
        eor.w	r6, r8, r7, ror #27
        eor.w	r7, r2, r5, ror #25
        ldr.w	r5, [r0, #0xac]
        ror.w	r3, r3, #0x12
        bic.w	r4, r6, r1, ror #1
        eor.w	r4, r4, r9, ror #25
        str.w	r3, [r0, #0x90]
        bic.w	r3, r1, r9, ror #24
        ror.w	r4, r4, #0xc
        eor.w	r3, r3, r7, ror #20
        eor.w	r5, r11, r5, ror #12
        str.w	r4, [r0, #0xac]
        ror.w	r3, r3, #0xd
        bic.w	r4, r9, r7, ror #28
        str.w	r3, [r0, #0xa4]
        bic.w	r3, r5, r6, ror #13
        eor.w	r3, r3, r1, ror #14
        ldr	r1, [r0, #0x8]
        bic.w	r9, r7, r5, ror #30
        ldr	r7, [r0, #0x20]
        eor.w	r6, r9, r6, ror #11
        ror.w	r3, r3, #0x1f
        str.w	r3, [r0, #0xb4]
        ldr	r3, [r0, #0x10]
        eor.w	r5, r4, r5, ror #26
        ldr	r4, [r0, #0x18]
        eor.w	r1, r10, r1, ror #9
        ldr.w	r9, [sp, #0xc]
        eor.w	r3, r2, r3, ror #23
        ror.w	r2, r5, #0x5
        ror.w	r5, r6, #0x1
        eor.w	r6, r9, r4, ror #19
        str.w	r2, [r0, #0xc4]
        eor.w	r2, r12, r7, ror #4
        str.w	r5, [r0, #0xbc]
        bic.w	r4, r6, r3, ror #21
        eor.w	r5, r4, r1, ror #21
        ldr.w	r4, [r0]
        eor.w	r4, r8, r4
        bic.w	r7, r2, r6, ror #28
        eor.w	r7, r7, r3, ror #17
        ror.w	r5, r5, #0x15
        str.w	r5, [r0, #0x8]
        bic.w	r3, r3, r1
        ror.w	r7, r7, #0x19
        str.w	r7, [r0, #0x10]
        bic.w	r5, r4, r2, ror #25
        ldr.w	r7, [r0, #0x3c]
        eor.w	r6, r5, r6, ror #21
        ldr.w	r5, [r0, #0x2c]
        bic.w	r1, r1, r4, ror #22
        str.w	r6, [r0, #0x18]
        eor.w	r1, r1, r2, ror #15
        ldr.w	r2, [sp, #0x10]
        eor.w	r5, r8, r5, ror #19
        ldr.w	r6, [r0, #0x34]
        eor.w	r7, r2, r7, ror #31
        ror.w	r1, r1, #0xa
        str.w	r1, [r0, #0x20]
        eor.w	r3, r4, r3, ror #10
        eor.w	r6, r10, r6, ror #24
        ldr	r1, [sp, #0x14]
        ldr	r4, [r1, #0x18]
        ldr.w	r1, [r0, #0x4c]
        eor.w	r3, r4, r3
        bic.w	r4, r7, r6, ror #8
        eor.w	r4, r4, r5, ror #29
        str.w	r3, [r0]
        eor.w	r1, lr, r1, ror #22
        ror.w	r3, r4, #0x2
        str.w	r3, [r0, #0x3c]
        bic.w	r3, r6, r5, ror #21
        ldr.w	r4, [r0, #0x44]
        eor.w	r4, r9, r4
        eor.w	r3, r3, r1, ror #12
        bic.w	r5, r5, r1, ror #23
        ror.w	r3, r3, #0xa
        eor.w	r5, r5, r4, ror #19
        bic.w	r1, r1, r4, ror #28
        str.w	r3, [r0, #0x34]
        ror.w	r3, r5, #0x1f
        eor.w	r5, r1, r7, ror #12
        bic.w	r7, r4, r7, ror #16
        ldr.w	r1, [r0, #0x50]
        eor.w	r6, r7, r6, ror #24
        ldr.w	r4, [r0, #0x58]
        ldr.w	r7, [r0, #0x60]
        str.w	r3, [r0, #0x2c]
        eor.w	r1, r8, r1, ror #12
        ror.w	r6, r6, #0x12
        ldr.w	r8, [r0, #0x70]
        eor.w	r4, r11, r4, ror #22
        eor.w	r3, r2, r7, ror #1
        ror.w	r7, r5, #0x16
        str.w	r7, [r0, #0x4c]
        ldr.w	r7, [r0, #0x68]
        str.w	r6, [r0, #0x44]
        bic.w	r5, r3, r4, ror #2
        eor.w	r6, r9, r7
        eor.w	r5, r5, r1, ror #26
        bic.w	r7, r6, r3, ror #10
        ror.w	r5, r5, #0x1d
        eor.w	r7, r7, r4, ror #12
        str.w	r5, [r0, #0x70]
        eor.w	r5, r12, r8, ror #14
        ror.w	r8, r7, #0x13
        bic.w	r4, r4, r1, ror #24
        bic.w	r7, r5, r6, ror #23
        str.w	r8, [r0, #0x50]
        bic.w	r1, r1, r5, ror #5
        ldr.w	r8, [sp, #0x4]
        eor.w	r7, r7, r3, ror #1
        ldr.w	r3, [r0, #0x9c]
        eor.w	r5, r4, r5, ror #29
        ldr.w	r4, [r0, #0x7c]
        eor.w	r1, r1, r6, ror #28
        ldr.w	r6, [r0, #0x84]
        eor.w	r3, r12, r3, ror #10
        ror.w	r5, r5, #0x1f
        ror.w	r1, r1, #0x17
        eor.w	r12, r8, r4, ror #31
        str.w	r5, [r0, #0x68]
        eor.w	r5, r11, r6, ror #28
        str.w	r1, [r0, #0x60]
        ldr.w	r1, [r0, #0x8c]
        ror.w	r6, r7, #0x1c
        bic.w	r4, r5, r12, ror #19
        eor.w	r4, r4, r3, ror #24
        str.w	r6, [r0, #0x58]
        eor.w	r6, r2, r1, ror #4
        ror.w	r1, r4, #0x1b
        ldr.w	r4, [r0, #0x94]
        str.w	r1, [r0, #0x7c]
        bic.w	r1, r6, r5, ror #2
        eor.w	r1, r1, r12, ror #21
        eor.w	r7, r9, r4, ror #1
        ror.w	r1, r1, #0x19
        bic.w	r4, r12, r3, ror #5
        bic.w	r12, r7, r6, ror #21
        str.w	r1, [r0, #0x84]
        eor.w	r5, r12, r5, ror #23
        ldr.w	r1, [r0, #0xb0]
        bic.w	r3, r3, r7, ror #17
        ldr.w	r12, [r0, #0xc]
        ror.w	r5, r5, #0x4
        eor.w	r4, r4, r7, ror #22
        eor.w	r7, r3, r6, ror #6
        str.w	r5, [r0, #0x8c]
        eor.w	r3, r2, r1, ror #25
        ldr	r6, [r0, #0x14]
        ror.w	r1, r7, #0x13
        ldr	r5, [r0, #0x24]
        eor.w	r7, r11, r12, ror #10
        ldr.w	r12, [r0, #0xb8]
        eor.w	r6, r2, r6, ror #23
        ldr.w	r11, [r0, #0xa8]
        eor.w	r5, lr, r5, ror #5
        ldr.w	r2, [r0, #0xc0]
        eor.w	r9, r9, r12, ror #18
        ldr.w	r12, [r0, #0xa0]
        eor.w	r10, r10, r11, ror #11
        str.w	r1, [r0, #0x94]
        eor.w	r11, lr, r2, ror #29
        ror.w	lr, r4, #0xe
        str.w	lr, [r0, #0x9c]
        eor.w	r2, r8, r12, ror #27
        bic.w	r12, r11, r9, ror #24
        ldr.w	lr, [r0, #0x4]
        eor.w	r8, r8, lr
        eor.w	r12, r12, r3, ror #21
        ldr	r1, [r0, #0x1c]
        bic.w	lr, r9, r3, ror #29
        ror.w	r4, r12, #0xc
        eor.w	r12, lr, r10, ror #27
        bic.w	lr, r7, r8, ror #22
        str.w	r4, [r0, #0xa0]
        eor.w	lr, lr, r5, ror #15
        ror.w	r12, r12, #0x4
        bic.w	r4, r2, r11, ror #1
        str.w	r12, [r0, #0xc0]
        ror.w	r12, lr, #0xa
        bic.w	lr, r3, r10, ror #30
        eor.w	r3, lr, r2, ror #10
        str.w	r12, [r0, #0x24]
        bic.w	lr, r10, r2, ror #12
        ldr.w	r12, [sp, #0x8]
        eor.w	r11, lr, r11, ror #13
        ror.w	lr, r3, #0x1
        eor.w	r2, r12, r1, ror #18
        ldr	r1, [sp, #0x14]
        str.w	lr, [r0, #0xb8]
        bic.w	r10, r6, r7, ror #31
        bic.w	r12, r8, r5, ror #25
        ror.w	lr, r11, #0x1f
        eor.w	r12, r12, r2, ror #22
        str.w	lr, [r0, #0xb0]
        eor.w	lr, r4, r9, ror #25
        ldr	r3, [r1, #0x1c]
        str.w	r12, [r0, #0x1c]
        bic.w	r4, r2, r6, ror #21
        ror.w	r12, lr, #0xb
        bic.w	lr, r5, r2, ror #29
        eor.w	lr, lr, r6, ror #18
        ldr	r11, [r1, #32]!
        eor.w	r2, r4, r7, ror #20
        str.w	r12, [r0, #0xa8]
        eor.w	r12, r8, r10, ror #11
        ror.w	lr, lr, #0x19
        ror.w	r6, r2, #0x16
        str.w	r6, [r0, #0xc]
        str	r1, [sp, #0x14]
        cmp.w	r11, #0xff
        eor.w	r1, r3, r12
        str.w	lr, [r0, #0x14]
        str.w	r1, [r0, #0x4]

slothy_end:
        bne.w	slothy_start      @ imm = #-0x1768
        add	sp, #0x18
        pop.w	{r4, r5, r6, r7, r8, r9, r10, r11, r12, pc}
        nop

#endif /* MLK_FIPS202_ARMV81M_NEED_X1 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
