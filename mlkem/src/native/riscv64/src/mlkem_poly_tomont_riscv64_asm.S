/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: poly_tomont_riscv64_asm
  Description: Convert all coefficients of a polynomial to Montgomery form
  Signature: void mlk_poly_tomont_riscv64_asm(int16_t p[256])
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [RVV]
    a0:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t p[256]
      description: Input/output polynomial
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/riscv64/src/mlkem_poly_tomont_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(poly_tomont_riscv64_asm)
MLK_ASM_FN_SYMBOL(poly_tomont_riscv64_asm)

        csrwi vxrm, 0x0
        lui t1, 0x1
        addiw t1, t1, -0x2ff
        li t2, -0x414
        lui t3, 0xffffd
        addiw t3, t3, 0x7dc
        li a1, 0x100
        vsetvli t0, a1, e16, m4, ta, ma
        slli t4, t0, 0x1

mlk_poly_tomont_riscv64_loop:
        vle16.v v0, (a0)
        vsmul.vx v4, v0, t3
        vmul.vx v0, v0, t2
        vnmsac.vx v0, t1, v4
        vse16.v v0, (a0)
        add a0, a0, t4
        sub a1, a1, t0
        bnez a1, mlk_poly_tomont_riscv64_loop
        ret

.option pop
MLK_ASM_FN_SIZE(poly_tomont_riscv64_asm)

#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
