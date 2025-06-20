/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) 2021-2022 Arm Limited
 * Copyright (c) 2022 Matthias Kannwischer
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */


// Author: Hanno Becker <hanno.becker@arm.com>
// Author: Matthias Kannwischer <matthias@kannwischer.eu>


#include "../../../../common.h"
#if defined(MLK_FIPS202_AARCH64_NEED_X1_SCALAR) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/aarch64/src/keccak_f1600_x1_scalar_asm.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_scalar_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_scalar_asm)

        sub	sp, sp, #0x1c0
        stp	x19, x20, [sp, #0x20]
        stp	x21, x22, [sp, #0x30]
        stp	x23, x24, [sp, #0x40]
        stp	x25, x26, [sp, #0x50]
        stp	x27, x28, [sp, #0x60]
        stp	x29, x30, [sp, #0x70]

keccak_f1600_x1_scalar_initial:
        mov	x26, x1
        str	x1, [sp, #0x8]
        ldp	x1, x6, [x0]
        ldp	x11, x16, [x0, #0x10]
        ldp	x21, x2, [x0, #0x20]
        ldp	x7, x12, [x0, #0x30]
        ldp	x17, x22, [x0, #0x40]
        ldp	x3, x8, [x0, #0x50]
        ldp	x13, x28, [x0, #0x60]
        ldp	x23, x4, [x0, #0x70]
        ldp	x9, x14, [x0, #0x80]
        ldp	x19, x24, [x0, #0x90]
        ldp	x5, x10, [x0, #0xa0]
        ldp	x15, x20, [x0, #0xb0]
        ldr	x25, [x0, #0xc0]
        str	x0, [sp]

keccak_f1600_x1_scalar_initial_start:
        eor	x30, x9, x10
        eor	x30, x30, x6
        eor	x27, x19, x20
        eor	x29, x30, x7
        str	x29, [sp, #0x80]
        eor	x0, x24, x25
        eor	x30, x27, x16
        eor	x0, x0, x21
        eor	x29, x0, x22
        eor	x26, x29, x23
        eor	x0, x14, x15
        eor	x27, x0, x11
        eor	x27, x27, x12
        eor	x0, x27, x13
        eor	x27, x4, x5
        eor	x29, x27, x1
        eor	x27, x30, x17
        str	x27, [sp, #0x88]
        eor	x27, x29, x2
        ldr	x29, [sp, #0x80]
        eor	x30, x29, x8
        eor	x29, x0, x26, ror #63
        str	x29, [sp, #0x80]
        eor	x26, x26, x30, ror #63
        eor	x29, x4, x26
        str	x29, [sp, #0x90]
        eor	x4, x27, x3
        ldr	x27, [sp, #0x88]
        ldr	x29, [sp, #0x80]
        eor	x0, x4, x0, ror #63
        eor	x1, x1, x26
        eor	x6, x6, x0
        str	x6, [sp, #0x80]
        eor	x20, x20, x29
        eor	x6, x27, x28
        eor	x27, x28, x29
        eor	x28, x10, x0
        eor	x4, x6, x4, ror #63
        eor	x6, x30, x6, ror #63
        eor	x30, x14, x6
        eor	x10, x21, x4
        str	x10, [sp, #0x88]
        eor	x21, x25, x4
        bic	x14, x1, x21, ror #50
        str	x14, [sp, #0x98]
        eor	x7, x7, x0
        str	x7, [sp, #0xa0]
        eor	x7, x15, x6
        eor	x15, x19, x29
        bic	x25, x21, x15, ror #57
        eor	x19, x22, x4
        eor	x22, x3, x26
        eor	x10, x8, x0
        eor	x8, x9, x0
        eor	x14, x24, x4
        str	x14, [sp, #0xa8]
        eor	x3, x5, x26
        ldr	x14, [sp, #0x98]
        str	x3, [sp, #0x98]
        eor	x5, x13, x6
        ldr	x24, [sp, #0x8]
        bic	x13, x7, x8, ror #16
        ldr	x0, [x24]
        str	x0, [sp, #0xb0]
        eor	x9, x23, x4
        eor	x4, x16, x29
        eor	x0, x2, x26
        bic	x3, x10, x0, ror #38
        str	x3, [sp, #0xb8]
        eor	x16, x14, x15, ror #43
        ldr	x3, [sp, #0xb8]
        eor	x26, x17, x29
        ldr	x29, [sp, #0x90]
        bic	x15, x15, x5, ror #42
        str	x15, [sp, #0x90]
        bic	x23, x19, x4, ror #56
        str	x23, [sp, #0xb8]
        bic	x23, x29, x9, ror #2
        bic	x15, x8, x22, ror #42
        str	x15, [sp, #0xc0]
        bic	x14, x4, x7, ror #31
        eor	x17, x14, x8, ror #47
        bic	x15, x28, x29, ror #25
        str	x15, [sp, #0xc8]
        bic	x8, x30, x10, ror #5
        bic	x15, x22, x19, ror #47
        eor	x2, x15, x4, ror #39
        str	x2, [sp, #0xd0]
        bic	x24, x20, x30, ror #41
        eor	x14, x24, x10, ror #46
        ldr	x10, [sp, #0x88]
        str	x14, [sp, #0x88]
        eor	x4, x3, x10, ror #47
        ldr	x14, [sp, #0xa8]
        ldr	x3, [sp, #0x98]
        eor	x2, x12, x6
        bic	x24, x0, x10, ror #9
        eor	x24, x24, x20, ror #44
        bic	x20, x10, x20, ror #35
        bic	x15, x27, x2, ror #19
        str	x15, [sp, #0x98]
        eor	x12, x13, x22, ror #58
        ldr	x15, [sp, #0xc8]
        bic	x22, x3, x14, ror #10
        eor	x10, x23, x26, ror #50
        ldr	x23, [sp, #0xb8]
        eor	x13, x22, x27, ror #57
        eor	x22, x23, x7, ror #23
        ldr	x7, [sp, #0xa0]
        str	x22, [sp, #0xa0]
        bic	x23, x7, x1, ror #44
        eor	x21, x23, x21, ror #30
        eor	x22, x11, x6
        ldr	x6, [sp, #0x80]
        str	x22, [sp, #0x80]
        bic	x22, x6, x3, ror #47
        str	x22, [sp, #0xa8]
        eor	x15, x15, x9, ror #27
        ldr	x22, [sp, #0x80]
        str	x15, [sp, #0x80]
        bic	x11, x5, x7, ror #63
        bic	x15, x2, x6, ror #5
        eor	x23, x15, x3, ror #52
        ldr	x15, [sp, #0x98]
        eor	x3, x15, x6, ror #24
        ldr	x15, [sp, #0x90]
        eor	x6, x15, x7, ror #41
        ldr	x15, [sp, #0xc0]
        eor	x7, x15, x19, ror #25
        bic	x15, x26, x22, ror #57
        eor	x1, x1, x11, ror #21
        bic	x26, x9, x26, ror #48
        eor	x9, x8, x0, ror #43
        mov	x19, #0x1               // =1
        eor	x11, x25, x5, ror #35
        eor	x5, x26, x22, ror #41
        str	x19, [sp, #0x10]
        bic	x27, x14, x27, ror #47
        eor	x19, x20, x30, ror #12
        ldr	x0, [sp, #0xb0]
        eor	x1, x1, x0
        eor	x8, x27, x2, ror #2
        ldr	x2, [sp, #0xd0]
        bic	x0, x22, x28, ror #60
        ldr	x22, [sp, #0xa8]
        eor	x20, x0, x29, ror #21
        eor	x25, x15, x28, ror #53
        ldr	x15, [sp, #0x80]
        eor	x28, x22, x14, ror #57
        ldr	x22, [sp, #0xa0]
        ldr	x14, [sp, #0x88]

keccak_f1600_x1_scalar_loop:
        eor	x29, x23, x22, ror #50
        eor	x30, x29, x24, ror #34
        eor	x26, x30, x21, ror #26
        eor	x29, x26, x25, ror #15
        str	x29, [sp, #0x80]
        eor	x27, x8, x9, ror #57
        eor	x27, x27, x6, ror #51
        eor	x29, x27, x10, ror #31
        eor	x30, x29, x7, ror #27
        ldr	x29, [sp, #0x80]
        ror	x0, x29, #0x3a
        eor	x27, x0, x30, ror #55
        str	x27, [sp, #0x80]
        eor	x0, x15, x11, ror #52
        eor	x0, x0, x13, ror #48
        eor	x0, x0, x14, ror #10
        eor	x26, x0, x12, ror #5
        ror	x27, x26, #0x3e
        eor	x0, x27, x29, ror #57
        eor	x27, x0, x20, ror #2
        str	x27, [sp, #0x88]
        eor	x27, x1, x2, ror #61
        eor	x29, x27, x4, ror #54
        eor	x29, x29, x3, ror #39
        eor	x27, x29, x5, ror #25
        eor	x29, x16, x28, ror #63
        ror	x30, x30, #0x38
        eor	x29, x29, x19, ror #37
        eor	x29, x29, x17, ror #36
        eor	x29, x29, x20, ror #2
        eor	x20, x29, x27, ror #63
        eor	x22, x20, x22, ror #44
        eor	x29, x30, x29, ror #63
        eor	x26, x27, x26, ror #61
        ldr	x27, [sp, #0x80]
        eor	x30, x27, x3, ror #39
        str	x30, [sp, #0x80]
        eor	x3, x27, x4, ror #54
        eor	x4, x26, x10, ror #23
        bic	x10, x4, x3, ror #25
        str	x10, [sp, #0x90]
        eor	x2, x27, x2, ror #61
        eor	x8, x26, x8, ror #56
        bic	x30, x8, x2, ror #38
        str	x30, [sp, #0x98]
        eor	x24, x20, x24, ror #28
        ldr	x30, [sp, #0x80]
        eor	x23, x20, x23, ror #58
        eor	x21, x20, x21, ror #20
        eor	x10, x20, x25, ror #9
        str	x10, [sp, #0x80]
        eor	x11, x29, x11, ror #50
        bic	x20, x11, x4, ror #60
        eor	x20, x20, x3, ror #21
        bic	x25, x3, x23, ror #2
        eor	x17, x0, x17, ror #36
        eor	x10, x25, x17, ror #50
        str	x10, [sp, #0xa0]
        eor	x3, x0, x16
        bic	x25, x17, x11, ror #57
        eor	x25, x25, x4, ror #53
        str	x25, [sp, #0xa8]
        bic	x25, x23, x17, ror #48
        eor	x10, x26, x9, ror #49
        eor	x19, x0, x19, ror #37
        bic	x16, x10, x30, ror #42
        eor	x15, x29, x15, ror #62
        bic	x9, x3, x15, ror #31
        eor	x17, x9, x10, ror #47
        eor	x12, x29, x12, ror #3
        str	x12, [sp, #0xb0]
        eor	x12, x29, x14, ror #8
        bic	x4, x12, x8, ror #5
        eor	x9, x4, x2, ror #43
        str	x9, [sp, #0xb8]
        eor	x14, x26, x7, ror #19
        eor	x7, x16, x22, ror #25
        bic	x9, x15, x10, ror #16
        ldr	x10, [sp, #0x80]
        str	x9, [sp, #0x80]
        eor	x13, x29, x13, ror #46
        eor	x1, x27, x1
        bic	x4, x1, x10, ror #50
        eor	x16, x4, x19, ror #43
        str	x16, [sp, #0xc0]
        bic	x4, x13, x14, ror #63
        str	x4, [sp, #0xc8]
        eor	x28, x0, x28, ror #63
        ldr	x4, [sp, #0xc8]
        eor	x0, x27, x5, ror #25
        bic	x27, x19, x13, ror #42
        str	x27, [sp, #0xc8]
        bic	x19, x10, x19, ror #57
        ldr	x27, [sp, #0x88]
        eor	x16, x1, x4, ror #21
        str	x16, [sp, #0x88]
        bic	x4, x21, x27, ror #35
        bic	x16, x14, x1, ror #44
        str	x16, [sp, #0xd0]
        eor	x5, x25, x11, ror #41
        bic	x29, x24, x28, ror #47
        bic	x1, x22, x3, ror #56
        eor	x11, x19, x13, ror #35
        str	x11, [sp, #0xd8]
        eor	x19, x4, x12, ror #12
        eor	x6, x26, x6, ror #43
        bic	x16, x2, x21, ror #9
        str	x16, [sp, #0xe0]
        bic	x16, x6, x0, ror #47
        str	x16, [sp, #0xe8]
        bic	x9, x27, x12, ror #41
        str	x9, [sp, #0xf0]
        ldr	x9, [sp, #0x8]
        str	x9, [sp, #0xf8]
        bic	x25, x30, x22, ror #47
        ldr	x9, [sp, #0x80]
        eor	x12, x9, x30, ror #58
        ldr	x9, [sp, #0xf8]
        ldr	x30, [sp, #0x98]
        str	x12, [sp, #0x80]
        eor	x4, x30, x21, ror #47
        ldr	x12, [sp, #0xb0]
        ldr	x26, [sp, #0x10]
        add	x2, x26, #0x1
        eor	x22, x1, x15, ror #23
        bic	x1, x0, x24, ror #10
        eor	x13, x1, x28, ror #57
        bic	x11, x28, x12, ror #19
        cmp	x2, #0x17
        ldr	x16, [sp, #0xe8]
        eor	x28, x16, x24, ror #57
        ldr	x16, [sp, #0xd0]
        eor	x21, x16, x10, ror #30
        ldr	x16, [sp, #0xe0]
        ldr	x10, [sp, #0x90]
        eor	x15, x10, x23, ror #27
        ldr	x10, [sp, #0xa0]
        ldr	x1, [x9, x26, lsl #3]
        ldr	x9, [sp, #0xf0]
        eor	x24, x16, x27, ror #44
        ldr	x16, [sp, #0x88]
        ldr	x27, [sp, #0xc8]
        bic	x23, x12, x6, ror #5
        eor	x23, x23, x0, ror #52
        str	x2, [sp, #0x10]
        eor	x1, x16, x1
        ldr	x16, [sp, #0xc0]
        eor	x2, x25, x3, ror #39
        ldr	x25, [sp, #0xa8]
        eor	x3, x11, x6, ror #24
        ldr	x11, [sp, #0xd8]
        eor	x6, x27, x14, ror #41
        eor	x14, x9, x8, ror #46
        ldr	x9, [sp, #0xb8]
        str	x14, [sp, #0x88]
        eor	x8, x29, x12, ror #2
        ldr	x12, [sp, #0x80]
        ldr	x14, [sp, #0x88]

keccak_f1600_x1_scalar_end_loop:
        b.le	keccak_f1600_x1_scalar_loop

keccak_f1600_x1_scalar_final:
        ror	x6, x6, #0x2b
        ror	x11, x11, #0x32
        ror	x21, x21, #0x14
        ror	x2, x2, #0x3d
        ror	x7, x7, #0x13
        ror	x12, x12, #0x3
        ror	x17, x17, #0x24
        ror	x22, x22, #0x2c
        ror	x3, x3, #0x27
        ror	x8, x8, #0x38
        ror	x13, x13, #0x2e
        ror	x28, x28, #0x3f
        ror	x23, x23, #0x3a
        ror	x4, x4, #0x36
        ror	x9, x9, #0x31
        ror	x14, x14, #0x8
        ror	x19, x19, #0x25
        ror	x24, x24, #0x1c
        ror	x5, x5, #0x19
        ror	x10, x10, #0x17
        ror	x15, x15, #0x3e
        ror	x20, x20, #0x2
        ror	x25, x25, #0x9
        ldr	x0, [sp]
        stp	x1, x6, [x0]
        stp	x11, x16, [x0, #0x10]
        stp	x21, x2, [x0, #0x20]
        stp	x7, x12, [x0, #0x30]
        stp	x17, x22, [x0, #0x40]
        stp	x3, x8, [x0, #0x50]
        stp	x13, x28, [x0, #0x60]
        stp	x23, x4, [x0, #0x70]
        stp	x9, x14, [x0, #0x80]
        stp	x19, x24, [x0, #0x90]
        stp	x5, x10, [x0, #0xa0]
        stp	x15, x20, [x0, #0xb0]
        str	x25, [x0, #0xc0]

keccak_f1600_x1_scalar_end_final:
        ldp	x19, x20, [sp, #0x20]
        ldp	x21, x22, [sp, #0x30]
        ldp	x23, x24, [sp, #0x40]
        ldp	x25, x26, [sp, #0x50]
        ldp	x27, x28, [sp, #0x60]
        ldp	x29, x30, [sp, #0x70]
        add	sp, sp, #0x1c0
        ret

#endif /* MLK_FIPS202_AARCH64_NEED_X1_SCALAR && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
