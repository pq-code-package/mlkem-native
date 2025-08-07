/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) 2021-2022 Arm Limited
 * Copyright (c) 2022 Matthias Kannwischer
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */


// Author: Hanno Becker <hanno.becker@arm.com>
// Author: Matthias Kannwischer <matthias@kannwischer.eu>


/*yaml
  Name: keccak_f1600_x1_scalar_no_lazy_symbolic
  Description: AArch64 scalar symbolic implementation of Keccak-f[1600] permutation for single state (no lazy rotation version for optimization)
  Signature: void mlk_keccak_f1600_x1_scalar_no_lazy_asm(uint64_t state[25], const uint64_t rc[24])
  ABI:
    x0:
      type: buffer
      size_bytes: 200
      permissions: read/write
      c_parameter: uint64_t *state
      description: Keccak state (25 x uint64_t)
    x1:
      type: buffer
      size_bytes: 192
      permissions: read-only
      c_parameter: uint64_t const *rc
      description: Round constants (24 x uint64_t)
  Stack:
    bytes: 128
    description: register preservation and temporary storage
*/

#include "../../../../common.h"
#if defined(MLK_FIPS202_AARCH64_NEED_X1_SCALAR) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/aarch64/src/keccak_f1600_x1_scalar_no_lazy_asm.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_scalar_no_lazy_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_scalar_no_lazy_asm)

        sub	sp, sp, #0x1c0
        stp	x19, x20, [sp, #0x20]
        stp	x21, x22, [sp, #0x30]
        stp	x23, x24, [sp, #0x40]
        stp	x25, x26, [sp, #0x50]
        stp	x27, x28, [sp, #0x60]
        stp	x29, x30, [sp, #0x70]

keccak_f1600_x1_scalar_no_lazy_initial:
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

keccak_f1600_x1_scalar_no_lazy_initial_start:
        eor	x27, x14, x15
        eor	x26, x27, x11
        eor	x27, x26, x12
        eor	x29, x27, x13
        eor	x27, x4, x5
        eor	x30, x27, x1
        eor	x30, x30, x2
        eor	x30, x30, x3
        eor	x0, x30, x29, ror #63
        eor	x27, x6, x0
        str	x27, [sp, #0x80]
        eor	x27, x24, x25
        eor	x27, x27, x21
        eor	x26, x27, x22
        eor	x26, x26, x23
        eor	x29, x29, x26, ror #63
        eor	x27, x17, x29
        str	x27, [sp, #0x88]
        eor	x27, x19, x20
        eor	x27, x27, x16
        eor	x17, x27, x17
        eor	x27, x17, x28
        eor	x17, x9, x10
        eor	x6, x17, x6
        eor	x6, x6, x7
        eor	x6, x6, x8
        eor	x26, x26, x6, ror #63
        eor	x4, x4, x26
        eor	x17, x27, x30, ror #63
        eor	x30, x23, x17
        bic	x23, x4, x30, ror #2
        str	x23, [sp, #0x90]
        eor	x6, x6, x27, ror #63
        eor	x27, x15, x6
        eor	x15, x9, x0
        bic	x23, x27, x15, ror #16
        str	x23, [sp, #0x98]
        eor	x23, x2, x26
        str	x23, [sp, #0xa0]
        eor	x23, x16, x29
        bic	x2, x23, x27, ror #31
        str	x2, [sp, #0xa8]
        eor	x16, x22, x17
        bic	x9, x16, x23, ror #56
        eor	x22, x9, x27, ror #23
        ldr	x27, [sp, #0x88]
        str	x22, [sp, #0x88]
        bic	x9, x30, x27, ror #48
        str	x9, [sp, #0xb0]
        eor	x9, x3, x26
        bic	x22, x9, x16, ror #47
        eor	x2, x22, x23, ror #39
        str	x2, [sp, #0xb8]
        eor	x3, x28, x29
        str	x3, [sp, #0xc0]
        eor	x10, x10, x0
        eor	x3, x11, x6
        bic	x22, x3, x10, ror #60
        eor	x28, x14, x6
        eor	x14, x12, x6
        ldr	x23, [sp, #0x98]
        str	x14, [sp, #0x98]
        eor	x12, x23, x9, ror #58
        str	x12, [sp, #0xc8]
        ldr	x2, [sp, #0x8]
        str	x2, [sp, #0xd0]
        bic	x9, x15, x9, ror #42
        eor	x2, x7, x0
        eor	x11, x21, x17
        mov	x12, #0x1               // =1
        eor	x7, x9, x16, ror #25
        bic	x23, x27, x3, ror #57
        eor	x8, x8, x0
        bic	x21, x10, x4, ror #25
        str	x12, [sp, #0x10]
        eor	x12, x24, x17
        eor	x14, x25, x17
        eor	x25, x19, x29
        eor	x29, x20, x29
        str	x29, [sp, #0xd8]
        eor	x20, x22, x4, ror #21
        ldr	x29, [sp, #0xd8]
        eor	x24, x13, x6
        eor	x9, x1, x26
        bic	x17, x14, x25, ror #57
        str	x17, [sp, #0xd8]
        bic	x19, x24, x2, ror #63
        ldr	x17, [sp, #0xd8]
        eor	x22, x9, x19, ror #21
        bic	x6, x25, x24, ror #42
        eor	x1, x5, x26
        bic	x4, x9, x14, ror #50
        bic	x0, x11, x29, ror #35
        eor	x16, x4, x25, ror #43
        eor	x25, x23, x10, ror #53
        ldr	x23, [sp, #0x90]
        eor	x10, x23, x27, ror #50
        ldr	x23, [sp, #0xa0]
        bic	x5, x8, x23, ror #38
        str	x5, [sp, #0x90]
        bic	x26, x29, x28, ror #41
        ldr	x5, [sp, #0x90]
        bic	x27, x23, x11, ror #9
        bic	x13, x2, x9, ror #44
        ldr	x9, [sp, #0xb0]
        str	x13, [sp, #0x90]
        eor	x4, x5, x11, ror #47
        ldr	x13, [sp, #0x90]
        eor	x5, x9, x3, ror #41
        ldr	x3, [sp, #0xc0]
        eor	x6, x6, x2, ror #41
        ldr	x2, [sp, #0xa8]
        eor	x11, x17, x24, ror #35
        eor	x17, x2, x15, ror #47
        ldr	x2, [sp, #0xd0]
        str	x17, [sp, #0x90]
        eor	x15, x21, x30, ror #27
        eor	x24, x27, x29, ror #44
        ldr	x27, [sp, #0x80]
        bic	x30, x27, x1, ror #47
        str	x30, [sp, #0x80]
        eor	x21, x13, x14, ror #30
        ldr	x30, [sp, #0x80]
        eor	x19, x0, x28, ror #12
        bic	x0, x28, x8, ror #5
        eor	x28, x30, x12, ror #57
        bic	x17, x1, x12, ror #10
        ldr	x29, [x2]
        ldr	x2, [sp, #0xb8]
        bic	x12, x12, x3, ror #47
        str	x12, [sp, #0x80]
        eor	x14, x26, x8, ror #46
        ldr	x12, [sp, #0x80]
        str	x14, [sp, #0x80]
        eor	x13, x17, x3, ror #57
        ldr	x14, [sp, #0x98]
        eor	x8, x12, x14, ror #2
        ldr	x12, [sp, #0xc8]
        bic	x17, x3, x14, ror #19
        eor	x3, x17, x27, ror #24
        ldr	x17, [sp, #0x90]
        bic	x26, x14, x27, ror #5
        ldr	x14, [sp, #0x80]
        eor	x9, x0, x23, ror #43
        eor	x23, x26, x1, ror #52
        eor	x1, x22, x29
        ldr	x22, [sp, #0x88]

keccak_f1600_x1_scalar_no_lazy_loop:
        eor	x27, x8, x9, ror #57
        eor	x27, x27, x6, ror #51
        eor	x30, x27, x10, ror #31
        eor	x30, x30, x7, ror #27
        ror	x27, x30, #0x38
        eor	x0, x16, x28, ror #63
        eor	x26, x0, x19, ror #37
        eor	x29, x26, x17, ror #36
        eor	x29, x29, x20, ror #2
        eor	x0, x27, x29, ror #63
        eor	x26, x0, x13, ror #46
        str	x26, [sp, #0x80]
        eor	x27, x15, x11, ror #52
        eor	x13, x27, x13, ror #48
        str	x13, [sp, #0x88]
        eor	x27, x1, x2, ror #61
        eor	x27, x27, x4, ror #54
        eor	x27, x27, x3, ror #39
        eor	x27, x27, x5, ror #25
        eor	x29, x29, x27, ror #63
        eor	x13, x29, x21, ror #20
        str	x13, [sp, #0x90]
        eor	x13, x23, x22, ror #50
        eor	x13, x13, x24, ror #34
        eor	x21, x13, x21, ror #26
        ldr	x13, [sp, #0x88]
        str	x21, [sp, #0x88]
        eor	x21, x13, x14, ror #10
        eor	x21, x21, x12, ror #5
        ror	x13, x21, #0x3e
        str	x13, [sp, #0x98]
        eor	x27, x27, x21, ror #61
        ldr	x21, [sp, #0x88]
        ldr	x13, [sp, #0x98]
        eor	x21, x21, x25, ror #15
        eor	x13, x13, x21, ror #57
        eor	x20, x13, x20, ror #2
        ror	x21, x21, #0x3a
        eor	x30, x21, x30, ror #55
        eor	x2, x30, x2, ror #61
        eor	x21, x13, x28, ror #63
        eor	x28, x27, x6, ror #43
        eor	x5, x30, x5, ror #25
        bic	x26, x28, x5, ror #47
        eor	x6, x29, x24, ror #28
        str	x6, [sp, #0x88]
        eor	x24, x0, x12, ror #3
        bic	x12, x21, x24, ror #19
        eor	x6, x30, x3, ror #39
        eor	x3, x12, x28, ror #24
        str	x3, [sp, #0x98]
        eor	x7, x27, x7, ror #19
        eor	x3, x30, x1
        bic	x1, x7, x3, ror #44
        eor	x22, x29, x22, ror #44
        bic	x12, x6, x22, ror #47
        str	x12, [sp, #0xa0]
        eor	x15, x0, x15, ror #62
        eor	x9, x27, x9, ror #49
        bic	x12, x15, x9, ror #16
        str	x12, [sp, #0xa8]
        eor	x16, x13, x16
        bic	x12, x22, x16, ror #56
        str	x12, [sp, #0xb0]
        eor	x8, x27, x8, ror #56
        ldr	x12, [sp, #0xa8]
        str	x8, [sp, #0xa8]
        eor	x12, x12, x6, ror #58
        str	x12, [sp, #0xb8]
        bic	x12, x9, x6, ror #42
        ldr	x6, [sp, #0x88]
        str	x12, [sp, #0x88]
        bic	x8, x6, x21, ror #47
        eor	x8, x8, x24, ror #2
        str	x8, [sp, #0xc0]
        bic	x8, x24, x28, ror #5
        str	x8, [sp, #0xc8]
        eor	x24, x29, x25, ror #9
        eor	x25, x30, x4, ror #54
        eor	x12, x13, x17, ror #36
        bic	x28, x5, x6, ror #10
        str	x28, [sp, #0xd0]
        eor	x19, x13, x19, ror #37
        ldr	x28, [sp, #0xd0]
        eor	x13, x28, x21, ror #57
        str	x13, [sp, #0xd0]
        eor	x21, x1, x24, ror #30
        ldr	x13, [sp, #0x90]
        eor	x28, x0, x11, ror #50
        eor	x10, x27, x10, ror #23
        eor	x27, x0, x14, ror #8
        bic	x4, x28, x10, ror #60
        bic	x17, x2, x13, ror #9
        bic	x11, x24, x19, ror #57
        bic	x0, x20, x27, ror #41
        bic	x1, x3, x24, ror #50
        eor	x24, x17, x20, ror #44
        bic	x14, x13, x20, ror #35
        eor	x20, x4, x25, ror #21
        bic	x8, x10, x25, ror #25
        str	x8, [sp, #0x90]
        bic	x4, x12, x28, ror #57
        eor	x30, x29, x23, ror #58
        bic	x8, x25, x30, ror #2
        str	x8, [sp, #0xd8]
        eor	x25, x4, x10, ror #53
        ldr	x8, [sp, #0xc8]
        bic	x17, x30, x12, ror #48
        eor	x23, x8, x5, ror #52
        eor	x5, x17, x28, ror #41
        ldr	x29, [sp, #0x10]
        ldr	x4, [sp, #0x8]
        ldr	x8, [x4, x29, lsl #3]
        str	x8, [sp, #0xc8]
        add	x4, x29, #0x1
        ldr	x8, [sp, #0xd8]
        str	x4, [sp, #0x10]
        eor	x10, x8, x12, ror #50
        ldr	x8, [sp, #0xa8]
        ldr	x12, [sp, #0x88]
        cmp	x4, #0x17
        eor	x28, x26, x6, ror #57
        ldr	x26, [sp, #0x80]
        bic	x4, x19, x26, ror #42
        eor	x6, x4, x7, ror #41
        bic	x29, x26, x7, ror #63
        eor	x7, x12, x22, ror #25
        ldr	x12, [sp, #0xb0]
        eor	x22, x12, x15, ror #23
        bic	x17, x16, x15, ror #31
        eor	x17, x17, x9, ror #47
        bic	x12, x27, x8, ror #5
        eor	x9, x12, x2, ror #43
        ldr	x12, [sp, #0xa0]
        bic	x15, x8, x2, ror #38
        eor	x2, x12, x16, ror #39
        ldr	x12, [sp, #0xb8]
        eor	x16, x1, x19, ror #43
        eor	x19, x14, x27, ror #12
        eor	x14, x0, x8, ror #46
        ldr	x8, [sp, #0x90]
        eor	x4, x15, x13, ror #47
        ldr	x13, [sp, #0xd0]
        eor	x11, x11, x26, ror #35
        eor	x15, x8, x30, ror #27
        ldr	x8, [sp, #0xc8]
        eor	x1, x3, x29, ror #21
        ldr	x3, [sp, #0x98]
        eor	x1, x1, x8
        ldr	x8, [sp, #0xc0]

keccak_f1600_x1_scalar_no_lazy_end_loop:
        b.le	keccak_f1600_x1_scalar_no_lazy_loop

keccak_f1600_x1_scalar_no_lazy_final:
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

keccak_f1600_x1_scalar_no_lazy_end_final:
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
