/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: rej_uniform_riscv64_asm
  Description: Run rejection sampling on uniform random bytes to generate uniform random integers mod q
  Signature: uint64_t mlk_rej_uniform_riscv64_asm(int16_t *r, uint64_t len, const uint8_t *buf, uint64_t buflen)
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [RVV]
    a0:
      type: buffer
      size_bytes: 512
      permissions: write-only
      c_parameter: int16_t *r
      description: Output buffer (2 * len bytes)
    a1:
      type: scalar
      c_parameter: uint64_t len
      description: Maximum number of coefficients to sample
      test_with: 256  # MLKEM_N
    a2:
      type: buffer
      size_bytes: a3
      permissions: read-only
      c_parameter: const uint8_t *buf
      description: Input buffer
    a3:
      type: scalar
      c_parameter: uint64_t buflen
      description: Length of input buffer (must be multiple of 12)
      test_with: 504  # MLKEM_GEN_MATRIX_NBLOCKS * MLK_XOF_RATE
*/


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/riscv64/src/mlkem_rej_uniform_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global mlk_rej_uniform_riscv64_asm
mlk_rej_uniform_riscv64_asm:

        li a4, 0x0
        lui t2, 0x1
        addiw t2, t2, -0x2ff
        lui t3, 0x1
        addiw t3, t3, -0x1
        vsetvli t0, zero, e16, m2, ta, ma
        vid.v v6
        li t4, 0xc
        vmul.vx v4, v6, t4
        vsrl.vi v2, v4, 0x4
        vsll.vi v6, v6, 0x2
        slli a5, t0, 0x1
        add a5, a5, t0
        srli a6, a5, 0x2
        srli a5, a5, 0x1

mlk_rej_uniform_riscv64_loop:
        bgeu a4, a1, mlk_rej_uniform_riscv64_done
        bltu a3, a5, mlk_rej_uniform_riscv64_tail

mlk_rej_uniform_riscv64_body:
        vsetvli zero, a6, e16, m2, ta, ma
        vle16.v v8, (a2)
        add a2, a2, a5
        sub a3, a3, a5
        vsetvli zero, t0, e16, m2, ta, ma
        vrgather.vv v10, v8, v2
        vslidedown.vi v12, v10, 0x1
        vsrl.vv v10, v10, v4
        vsll.vv v12, v12, v6
        vor.vv v10, v10, v12
        vand.vx v10, v10, t3
        vmsltu.vx v0, v10, t2
        vcpop.m t1, v0
        vcompress.vm v14, v10, v0
        sub a7, a1, a4
        bgeu a7, t1, mlk_rej_uniform_riscv64_store
        mv t1, a7

mlk_rej_uniform_riscv64_store:
        vsetvli zero, t1, e16, m2, ta, ma
        vse16.v v14, (a0)
        add a4, a4, t1
        slli t1, t1, 0x1
        add a0, a0, t1
        j mlk_rej_uniform_riscv64_loop

mlk_rej_uniform_riscv64_tail:
        beqz a3, mlk_rej_uniform_riscv64_done
        mv a5, a3
        srli a6, a3, 0x1
        lui t4, 0xb
        addiw t4, t4, -0x555
        mul t0, a3, t4
        srli t0, t0, 0x10
        j mlk_rej_uniform_riscv64_body

mlk_rej_uniform_riscv64_done:
        mv a0, a4
        ret

.option pop
#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
