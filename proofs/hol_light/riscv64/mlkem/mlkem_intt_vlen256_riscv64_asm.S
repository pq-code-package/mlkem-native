/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: intt_vlen256_riscv64_asm
  Description: Inverse negacyclic NTT of a polynomial in place, input in bitreversed order, with scaling to Montgomery form (VLEN=256 only)
  Signature: void mlk_intt_vlen256_riscv64_asm(int16_t p[256], const int16_t zetas[800], const uint16_t perms[160])
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
    a1:
      type: buffer
      size_bytes: 1600
      permissions: read-only
      c_parameter: const int16_t zetas[800]
      description: Twiddle table (mlk_rv64v_intt256_zetas)
    a2:
      type: buffer
      size_bytes: 320
      permissions: read-only
      c_parameter: const uint16_t perms[160]
      description: Permutation table (mlk_rv64v_ntt256_perms)
*/


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/riscv64/src/mlkem_intt_vlen256_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global mlk_intt_vlen256_riscv64_asm
mlk_intt_vlen256_riscv64_asm:

        csrwi vxrm, 0x0
        lui t0, 0x1
        addiw t0, t0, -0x2ff
        li t1, 0x10
        li t2, 0x20
        li a3, 0x40
        li a4, 0x80
        vsetvli zero, a4, e16, m8, ta, ma
        vle16.v v16, (a0)
        addi t5, a0, 0x100
        vle16.v v24, (t5)
        vsetvli zero, t2, e16, m2, ta, ma
        addi t5, a2, 0x100
        vle16.v v8, (t5)
        addi t5, a2, 0x80
        vle16.v v10, (t5)
        addi t5, a2, 0x40
        vle16.v v12, (t5)
        vle16.v v14, (a2)
        addi t6, a1, 0x40
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v16, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v16, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v16, v17
        vadd.vv v16, v16, v17
        vmul.vv v17, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v17, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v16, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v16, v2, v14
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v18, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v18, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v18, v19
        vadd.vv v18, v18, v19
        vmul.vv v19, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v19, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v18, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v18, v2, v14
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v20, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v20, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v20, v21
        vadd.vv v20, v20, v21
        vmul.vv v21, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v21, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v20, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v20, v2, v14
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v22, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v22, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v22, v23
        vadd.vv v22, v22, v23
        vmul.vv v23, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v23, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v22, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v22, v2, v14
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v24, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v24, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v24, v25
        vadd.vv v24, v24, v25
        vmul.vv v25, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v25, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v24, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v24, v2, v14
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v26, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v26, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v26, v27
        vadd.vv v26, v26, v27
        vmul.vv v27, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v27, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v26, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v26, v2, v14
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v28, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v28, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v28, v29
        vadd.vv v28, v28, v29
        vmul.vv v29, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v29, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v28, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v28, v2, v14
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v30, v8
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x200
        lui t4, 0x1
        addiw t4, t4, 0x3b0
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsmul.vx v5, v3, t4
        vmul.vx v3, v3, t3
        vnmsac.vx v3, t0, v5
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v30, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v30, v31
        vadd.vv v30, v30, v31
        vmul.vv v31, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v31, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v30, v12
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x20
        vle16.v v7, (t6)
        addi t6, t6, 0x20
        vsub.vv v5, v2, v3
        vadd.vv v2, v2, v3
        vmul.vv v3, v5, v6
        vsmul.vv v5, v5, v7
        vnmsac.vx v3, t0, v5
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v2, t4
        vmul.vx v2, v2, t3
        vnmsac.vx v2, t0, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v30, v2, v14
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a1)
        lh t4, 0x2(a1)
        vsub.vv v0, v16, v17
        vadd.vv v16, v16, v17
        vmul.vx v17, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v17, t0, v0
        lh t3, 0x4(a1)
        lh t4, 0x6(a1)
        vsub.vv v0, v18, v19
        vadd.vv v18, v18, v19
        vmul.vx v19, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v19, t0, v0
        lh t3, 0x8(a1)
        lh t4, 0xa(a1)
        vsub.vv v0, v20, v21
        vadd.vv v20, v20, v21
        vmul.vx v21, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v21, t0, v0
        lh t3, 0xc(a1)
        lh t4, 0xe(a1)
        vsub.vv v0, v22, v23
        vadd.vv v22, v22, v23
        vmul.vx v23, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v23, t0, v0
        lh t3, 0x10(a1)
        lh t4, 0x12(a1)
        vsub.vv v0, v24, v25
        vadd.vv v24, v24, v25
        vmul.vx v25, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v25, t0, v0
        lh t3, 0x14(a1)
        lh t4, 0x16(a1)
        vsub.vv v0, v26, v27
        vadd.vv v26, v26, v27
        vmul.vx v27, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v27, t0, v0
        lh t3, 0x18(a1)
        lh t4, 0x1a(a1)
        vsub.vv v0, v28, v29
        vadd.vv v28, v28, v29
        vmul.vx v29, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v29, t0, v0
        lh t3, 0x1c(a1)
        lh t4, 0x1e(a1)
        vsub.vv v0, v30, v31
        vadd.vv v30, v30, v31
        vmul.vx v31, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v31, t0, v0
        vsetvli zero, t2, e16, m2, ta, ma
        lh t3, 0x20(a1)
        lh t4, 0x22(a1)
        vsub.vv v0, v16, v18
        vadd.vv v16, v16, v18
        vmul.vx v18, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v18, t0, v0
        lh t3, 0x24(a1)
        lh t4, 0x26(a1)
        vsub.vv v0, v20, v22
        vadd.vv v20, v20, v22
        vmul.vx v22, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v22, t0, v0
        lh t3, 0x28(a1)
        lh t4, 0x2a(a1)
        vsub.vv v0, v24, v26
        vadd.vv v24, v24, v26
        vmul.vx v26, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v26, t0, v0
        lh t3, 0x2c(a1)
        lh t4, 0x2e(a1)
        vsub.vv v0, v28, v30
        vadd.vv v28, v28, v30
        vmul.vx v30, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v30, t0, v0
        vsetvli zero, a3, e16, m4, ta, ma
        lh t3, 0x30(a1)
        lh t4, 0x32(a1)
        vsub.vv v0, v16, v20
        vadd.vv v16, v16, v20
        vmul.vx v20, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v20, t0, v0
        lh t3, 0x34(a1)
        lh t4, 0x36(a1)
        vsub.vv v0, v24, v28
        vadd.vv v24, v24, v28
        vmul.vx v28, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v28, t0, v0
        vsetvli zero, t1, e16, m1, ta, ma
        li t3, 0x1
        li t4, 0xa
        vsmul.vx v5, v16, t4
        vmul.vx v16, v16, t3
        vnmsac.vx v16, t0, v5
        vsmul.vx v5, v24, t4
        vmul.vx v24, v24, t3
        vnmsac.vx v24, t0, v5
        vsetvli zero, a4, e16, m8, ta, ma
        lh t3, 0x38(a1)
        lh t4, 0x3a(a1)
        vsub.vv v0, v16, v24
        vadd.vv v16, v16, v24
        vmul.vx v24, v0, t3
        vsmul.vx v0, v0, t4
        vnmsac.vx v24, t0, v0
        vse16.v v16, (a0)
        addi t5, a0, 0x100
        vse16.v v24, (t5)
        ret

.option pop
#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
