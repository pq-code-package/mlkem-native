/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: keccak_f1600_x1_zbb_riscv64_asm
  Description: RV64 scalar implementation of the Keccak-f[1600] permutation for a single state, using Zbb
  Signature: void mlk_keccak_f1600_x1_zbb_riscv64_asm(uint64_t state[25], const uint64_t rc[24])
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [ZBB]
    a0:
      type: buffer
      size_bytes: 200
      permissions: read/write
      c_parameter: uint64_t state[25]
      description: Keccak state (25 x uint64_t)
    a1:
      type: buffer
      size_bytes: 192
      permissions: read-only
      c_parameter: const uint64_t rc[24]
      description: Round constants (24 x uint64_t)
  Stack:
    bytes: 144
    description: register preservation and temporary storage
*/


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/riscv64/src/keccak_f1600_x1_zbb_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global mlk_keccak_f1600_x1_zbb_riscv64_asm
mlk_keccak_f1600_x1_zbb_riscv64_asm:

        addi sp, sp, -0x90
        sd ra, 0x0(sp)
        sd s0, 0x8(sp)
        sd s1, 0x10(sp)
        sd s2, 0x18(sp)
        sd s3, 0x20(sp)
        sd s4, 0x28(sp)
        sd s5, 0x30(sp)
        sd s6, 0x38(sp)
        sd s7, 0x40(sp)
        sd s8, 0x48(sp)
        sd s9, 0x50(sp)
        sd s10, 0x58(sp)
        sd s11, 0x60(sp)
        sd a0, 0x68(sp)
        sd a1, 0x70(sp)
        addi t0, a1, 0xc0
        sd t0, 0x78(sp)
        ld a1, 0x8(a0)
        ld a2, 0x10(a0)
        ld a3, 0x18(a0)
        ld a4, 0x20(a0)
        ld a5, 0x28(a0)
        ld a6, 0x30(a0)
        ld a7, 0x38(a0)
        ld s2, 0x40(a0)
        ld s3, 0x48(a0)
        ld s4, 0x50(a0)
        ld s5, 0x58(a0)
        ld s6, 0x60(a0)
        ld s7, 0x68(a0)
        ld s8, 0x70(a0)
        ld s9, 0x78(a0)
        ld s10, 0x80(a0)
        ld s11, 0x88(a0)
        ld s0, 0x90(a0)
        ld s1, 0x98(a0)
        ld t3, 0xa0(a0)
        ld t4, 0xa8(a0)
        ld t5, 0xb0(a0)
        ld t6, 0xb8(a0)
        ld ra, 0xc0(a0)
        ld a0, 0x0(a0)

mlk_keccak_f1600_x1_zbb_riscv64_loop:
        xor t0, a0, a5
        xor t0, t0, s4
        xor t0, t0, s9
        xor t0, t0, t3
        sd t0, 0x80(sp)
        xor t0, a2, a7
        xor t0, t0, s6
        xor t0, t0, s11
        xor t0, t0, t5
        sd t0, 0x88(sp)
        xor t0, a1, a6
        xor t0, t0, s5
        xor t0, t0, s10
        xor t0, t0, t4
        xor t1, a4, s3
        xor t1, t1, s8
        xor t1, t1, s1
        xor t1, t1, ra
        rori t2, t0, 0x3f
        xor t2, t2, t1
        rori t1, t1, 0x3f
        xor a0, a0, t2
        xor a5, a5, t2
        xor s4, s4, t2
        xor s9, s9, t2
        xor t3, t3, t2
        ld t2, 0x88(sp)
        xor t1, t1, t2
        xor t2, a3, s2
        xor t2, t2, s7
        xor t2, t2, s0
        xor t2, t2, t6
        xor a3, a3, t1
        xor s2, s2, t1
        xor s7, s7, t1
        xor s0, s0, t1
        xor t6, t6, t1
        rori t1, t2, 0x3f
        xor t0, t0, t1
        ld t1, 0x80(sp)
        xor a2, a2, t0
        xor a7, a7, t0
        xor s6, s6, t0
        xor s11, s11, t0
        xor t5, t5, t0
        rori t0, t1, 0x3f
        xor t2, t2, t0
        ld t0, 0x88(sp)
        xor a4, a4, t2
        xor s3, s3, t2
        xor s8, s8, t2
        xor s1, s1, t2
        xor ra, ra, t2
        rori t0, t0, 0x3f
        xor t0, t0, t1
        xor t2, a1, t0
        xor a6, a6, t0
        xor s5, s5, t0
        xor s10, s10, t0
        xor t4, t4, t0
        rori a1, a6, 0x14
        rori a6, s3, 0x2c
        rori s3, t5, 0x3
        rori t5, s8, 0x19
        rori s8, t3, 0x2e
        rori t3, a2, 0x2
        rori a2, s6, 0x15
        rori s6, s7, 0x27
        rori s7, s1, 0x38
        rori s1, t6, 0x8
        rori t6, s9, 0x17
        rori s9, a4, 0x25
        rori a4, ra, 0x32
        rori ra, t4, 0x3e
        rori t4, s2, 0x9
        rori s2, s10, 0x13
        rori s10, a5, 0x1c
        rori a5, a3, 0x24
        rori a3, s0, 0x2b
        rori s0, s11, 0x31
        rori s11, s5, 0x36
        rori s5, a7, 0x3a
        rori a7, s4, 0x3d
        rori s4, t2, 0x3f
        andn t0, a0, a4
        andn t1, a1, a0
        andn t2, a2, a1
        xor a0, a0, t2
        andn t2, a3, a2
        xor a1, a1, t2
        andn t2, a4, a3
        xor a2, a2, t2
        xor a3, a3, t0
        xor a4, a4, t1
        andn t0, a5, s3
        andn t1, a6, a5
        andn t2, a7, a6
        xor a5, a5, t2
        andn t2, s2, a7
        xor a6, a6, t2
        andn t2, s3, s2
        xor a7, a7, t2
        xor s2, s2, t0
        xor s3, s3, t1
        andn t0, s4, s8
        andn t1, s5, s4
        andn t2, s6, s5
        xor s4, s4, t2
        andn t2, s7, s6
        xor s5, s5, t2
        andn t2, s8, s7
        xor s6, s6, t2
        xor s7, s7, t0
        xor s8, s8, t1
        andn t0, s9, s1
        andn t1, s10, s9
        andn t2, s11, s10
        xor s9, s9, t2
        andn t2, s0, s11
        xor s10, s10, t2
        andn t2, s1, s0
        xor s11, s11, t2
        xor s0, s0, t0
        xor s1, s1, t1
        andn t0, t3, ra
        andn t1, t4, t3
        andn t2, t5, t4
        xor t3, t3, t2
        andn t2, t6, t5
        xor t4, t4, t2
        andn t2, ra, t6
        xor t5, t5, t2
        xor t6, t6, t0
        xor ra, ra, t1
        ld t0, 0x70(sp)
        ld t1, 0x0(t0)
        xor a0, a0, t1
        xor t0, a0, a5
        xor t0, t0, s4
        xor t0, t0, s9
        xor t0, t0, t3
        sd t0, 0x80(sp)
        xor t0, a2, a7
        xor t0, t0, s6
        xor t0, t0, s11
        xor t0, t0, t5
        sd t0, 0x88(sp)
        xor t0, a1, a6
        xor t0, t0, s5
        xor t0, t0, s10
        xor t0, t0, t4
        xor t1, a4, s3
        xor t1, t1, s8
        xor t1, t1, s1
        xor t1, t1, ra
        rori t2, t0, 0x3f
        xor t2, t2, t1
        rori t1, t1, 0x3f
        xor a0, a0, t2
        xor a5, a5, t2
        xor s4, s4, t2
        xor s9, s9, t2
        xor t3, t3, t2
        ld t2, 0x88(sp)
        xor t1, t1, t2
        xor t2, a3, s2
        xor t2, t2, s7
        xor t2, t2, s0
        xor t2, t2, t6
        xor a3, a3, t1
        xor s2, s2, t1
        xor s7, s7, t1
        xor s0, s0, t1
        xor t6, t6, t1
        rori t1, t2, 0x3f
        xor t0, t0, t1
        ld t1, 0x80(sp)
        xor a2, a2, t0
        xor a7, a7, t0
        xor s6, s6, t0
        xor s11, s11, t0
        xor t5, t5, t0
        rori t0, t1, 0x3f
        xor t2, t2, t0
        ld t0, 0x88(sp)
        xor a4, a4, t2
        xor s3, s3, t2
        xor s8, s8, t2
        xor s1, s1, t2
        xor ra, ra, t2
        rori t0, t0, 0x3f
        xor t0, t0, t1
        xor t2, a1, t0
        xor a6, a6, t0
        xor s5, s5, t0
        xor s10, s10, t0
        xor t4, t4, t0
        rori a1, a6, 0x14
        rori a6, s3, 0x2c
        rori s3, t5, 0x3
        rori t5, s8, 0x19
        rori s8, t3, 0x2e
        rori t3, a2, 0x2
        rori a2, s6, 0x15
        rori s6, s7, 0x27
        rori s7, s1, 0x38
        rori s1, t6, 0x8
        rori t6, s9, 0x17
        rori s9, a4, 0x25
        rori a4, ra, 0x32
        rori ra, t4, 0x3e
        rori t4, s2, 0x9
        rori s2, s10, 0x13
        rori s10, a5, 0x1c
        rori a5, a3, 0x24
        rori a3, s0, 0x2b
        rori s0, s11, 0x31
        rori s11, s5, 0x36
        rori s5, a7, 0x3a
        rori a7, s4, 0x3d
        rori s4, t2, 0x3f
        andn t0, a0, a4
        andn t1, a1, a0
        andn t2, a2, a1
        xor a0, a0, t2
        andn t2, a3, a2
        xor a1, a1, t2
        andn t2, a4, a3
        xor a2, a2, t2
        xor a3, a3, t0
        xor a4, a4, t1
        andn t0, a5, s3
        andn t1, a6, a5
        andn t2, a7, a6
        xor a5, a5, t2
        andn t2, s2, a7
        xor a6, a6, t2
        andn t2, s3, s2
        xor a7, a7, t2
        xor s2, s2, t0
        xor s3, s3, t1
        andn t0, s4, s8
        andn t1, s5, s4
        andn t2, s6, s5
        xor s4, s4, t2
        andn t2, s7, s6
        xor s5, s5, t2
        andn t2, s8, s7
        xor s6, s6, t2
        xor s7, s7, t0
        xor s8, s8, t1
        andn t0, s9, s1
        andn t1, s10, s9
        andn t2, s11, s10
        xor s9, s9, t2
        andn t2, s0, s11
        xor s10, s10, t2
        andn t2, s1, s0
        xor s11, s11, t2
        xor s0, s0, t0
        xor s1, s1, t1
        andn t0, t3, ra
        andn t1, t4, t3
        andn t2, t5, t4
        xor t3, t3, t2
        andn t2, t6, t5
        xor t4, t4, t2
        andn t2, ra, t6
        xor t5, t5, t2
        xor t6, t6, t0
        xor ra, ra, t1
        ld t0, 0x70(sp)
        ld t1, 0x8(t0)
        xor a0, a0, t1
        addi t0, t0, 0x10
        sd t0, 0x70(sp)
        ld t1, 0x78(sp)
        bne t0, t1, mlk_keccak_f1600_x1_zbb_riscv64_loop
        ld t0, 0x68(sp)
        sd a1, 0x8(t0)
        sd a2, 0x10(t0)
        sd a3, 0x18(t0)
        sd a4, 0x20(t0)
        sd a5, 0x28(t0)
        sd a6, 0x30(t0)
        sd a7, 0x38(t0)
        sd s2, 0x40(t0)
        sd s3, 0x48(t0)
        sd s4, 0x50(t0)
        sd s5, 0x58(t0)
        sd s6, 0x60(t0)
        sd s7, 0x68(t0)
        sd s8, 0x70(t0)
        sd s9, 0x78(t0)
        sd s10, 0x80(t0)
        sd s11, 0x88(t0)
        sd s0, 0x90(t0)
        sd s1, 0x98(t0)
        sd t3, 0xa0(t0)
        sd t4, 0xa8(t0)
        sd t5, 0xb0(t0)
        sd t6, 0xb8(t0)
        sd ra, 0xc0(t0)
        sd a0, 0x0(t0)
        ld ra, 0x0(sp)
        ld s0, 0x8(sp)
        ld s1, 0x10(sp)
        ld s2, 0x18(sp)
        ld s3, 0x20(sp)
        ld s4, 0x28(sp)
        ld s5, 0x30(sp)
        ld s6, 0x38(sp)
        ld s7, 0x40(sp)
        ld s8, 0x48(sp)
        ld s9, 0x50(sp)
        ld s10, 0x58(sp)
        ld s11, 0x60(sp)
        addi sp, sp, 0x90
        ret

.option pop
#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
