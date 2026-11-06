/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: poly_reduce_riscv64_asm
  Description: Barrett-reduce all coefficients of a polynomial to their unsigned canonical representatives mod q
  Signature: void mlk_poly_reduce_riscv64_asm(int16_t p[256])
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
 *   dev/riscv64/src/mlkem_poly_reduce_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(poly_reduce_riscv64_asm)
MLK_ASM_FN_SYMBOL(poly_reduce_riscv64_asm)

        lui t1, 0x1
        addiw t1, t1, -0x2ff
        lui t2, 0x5
        addiw t2, t2, -0x141
        li t3, 0x200
        li a1, 0x100
        vsetvli t0, a1, e16, m4, ta, ma
        slli t4, t0, 0x1

mlk_poly_reduce_riscv64_loop:
        vle16.v v0, (a0)
        vmulh.vx v4, v0, t2
        vadd.vx v4, v4, t3
        vsra.vi v4, v4, 0xa
        vmul.vx v4, v4, t1
        vsub.vv v0, v0, v4
        vsra.vi v4, v0, 0xf
        vand.vx v4, v4, t1
        vadd.vv v0, v0, v4
        vse16.v v0, (a0)
        add a0, a0, t4
        sub a1, a1, t0
        bnez a1, mlk_poly_reduce_riscv64_loop
        ret

.option pop
MLK_ASM_FN_SIZE(poly_reduce_riscv64_asm)

#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
