/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: ntt_vlen128_riscv64_asm
  Description: Forward negacyclic NTT of a polynomial in place, output in bitreversed order (VLEN=128 only)
  Signature: void mlk_ntt_vlen128_riscv64_asm(int16_t p[256], const int16_t zetas[576], const uint16_t perms[96])
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
      size_bytes: 1152
      permissions: read-only
      c_parameter: const int16_t zetas[576]
      description: Twiddle table (mlk_rv64v_ntt128_zetas)
    a2:
      type: buffer
      size_bytes: 192
      permissions: read-only
      c_parameter: const uint16_t perms[96]
      description: Permutation table (mlk_rv64v_ntt128_perms)
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/riscv64/src/mlkem_ntt_vlen128_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(ntt_vlen128_riscv64_asm)
MLK_ASM_FN_SYMBOL(ntt_vlen128_riscv64_asm)

        csrwi vxrm, 0x0
        lui t0, 0x1
        addiw t0, t0, -0x2ff
        li t1, 0x8
        li t2, 0x10
        li a3, 0x20
        li a4, 0x40
        vsetvli zero, t1, e16, m1, ta, ma
        mv t5, a0
        vle16.v v16, (t5)
        addi t5, t5, 0x20
        vle16.v v17, (t5)
        addi t5, t5, 0x20
        vle16.v v18, (t5)
        addi t5, t5, 0x20
        vle16.v v19, (t5)
        addi t5, t5, 0x20
        vle16.v v20, (t5)
        addi t5, t5, 0x20
        vle16.v v21, (t5)
        addi t5, t5, 0x20
        vle16.v v22, (t5)
        addi t5, t5, 0x20
        vle16.v v23, (t5)
        addi t5, t5, 0x20
        vle16.v v24, (t5)
        addi t5, t5, 0x20
        vle16.v v25, (t5)
        addi t5, t5, 0x20
        vle16.v v26, (t5)
        addi t5, t5, 0x20
        vle16.v v27, (t5)
        addi t5, t5, 0x20
        vle16.v v28, (t5)
        addi t5, t5, 0x20
        vle16.v v29, (t5)
        addi t5, t5, 0x20
        vle16.v v30, (t5)
        addi t5, t5, 0x20
        vle16.v v31, (t5)
        addi t5, t5, 0x20
        vsetvli zero, a4, e16, m8, ta, ma
        lh t3, 0x0(a1)
        lh t4, 0x2(a1)
        vmul.vx v0, v24, t3
        vsmul.vx v24, v24, t4
        vnmsac.vx v0, t0, v24
        vsub.vv v24, v16, v0
        vadd.vv v16, v16, v0
        vsetvli zero, a3, e16, m4, ta, ma
        lh t3, 0x4(a1)
        lh t4, 0x6(a1)
        vmul.vx v0, v20, t3
        vsmul.vx v20, v20, t4
        vnmsac.vx v0, t0, v20
        vsub.vv v20, v16, v0
        vadd.vv v16, v16, v0
        lh t3, 0x8(a1)
        lh t4, 0xa(a1)
        vmul.vx v0, v28, t3
        vsmul.vx v28, v28, t4
        vnmsac.vx v0, t0, v28
        vsub.vv v28, v24, v0
        vadd.vv v24, v24, v0
        vsetvli zero, t2, e16, m2, ta, ma
        lh t3, 0xc(a1)
        lh t4, 0xe(a1)
        vmul.vx v0, v18, t3
        vsmul.vx v18, v18, t4
        vnmsac.vx v0, t0, v18
        vsub.vv v18, v16, v0
        vadd.vv v16, v16, v0
        lh t3, 0x10(a1)
        lh t4, 0x12(a1)
        vmul.vx v0, v22, t3
        vsmul.vx v22, v22, t4
        vnmsac.vx v0, t0, v22
        vsub.vv v22, v20, v0
        vadd.vv v20, v20, v0
        lh t3, 0x14(a1)
        lh t4, 0x16(a1)
        vmul.vx v0, v26, t3
        vsmul.vx v26, v26, t4
        vnmsac.vx v0, t0, v26
        vsub.vv v26, v24, v0
        vadd.vv v24, v24, v0
        lh t3, 0x18(a1)
        lh t4, 0x1a(a1)
        vmul.vx v0, v30, t3
        vsmul.vx v30, v30, t4
        vnmsac.vx v0, t0, v30
        vsub.vv v30, v28, v0
        vadd.vv v28, v28, v0
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x1c(a1)
        lh t4, 0x1e(a1)
        vmul.vx v0, v17, t3
        vsmul.vx v17, v17, t4
        vnmsac.vx v0, t0, v17
        vsub.vv v17, v16, v0
        vadd.vv v16, v16, v0
        lh t3, 0x20(a1)
        lh t4, 0x22(a1)
        vmul.vx v0, v19, t3
        vsmul.vx v19, v19, t4
        vnmsac.vx v0, t0, v19
        vsub.vv v19, v18, v0
        vadd.vv v18, v18, v0
        lh t3, 0x24(a1)
        lh t4, 0x26(a1)
        vmul.vx v0, v21, t3
        vsmul.vx v21, v21, t4
        vnmsac.vx v0, t0, v21
        vsub.vv v21, v20, v0
        vadd.vv v20, v20, v0
        lh t3, 0x28(a1)
        lh t4, 0x2a(a1)
        vmul.vx v0, v23, t3
        vsmul.vx v23, v23, t4
        vnmsac.vx v0, t0, v23
        vsub.vv v23, v22, v0
        vadd.vv v22, v22, v0
        lh t3, 0x2c(a1)
        lh t4, 0x2e(a1)
        vmul.vx v0, v25, t3
        vsmul.vx v25, v25, t4
        vnmsac.vx v0, t0, v25
        vsub.vv v25, v24, v0
        vadd.vv v24, v24, v0
        lh t3, 0x30(a1)
        lh t4, 0x32(a1)
        vmul.vx v0, v27, t3
        vsmul.vx v27, v27, t4
        vnmsac.vx v0, t0, v27
        vsub.vv v27, v26, v0
        vadd.vv v26, v26, v0
        lh t3, 0x34(a1)
        lh t4, 0x36(a1)
        vmul.vx v0, v29, t3
        vsmul.vx v29, v29, t4
        vnmsac.vx v0, t0, v29
        vsub.vv v29, v28, v0
        vadd.vv v28, v28, v0
        lh t3, 0x38(a1)
        lh t4, 0x3a(a1)
        vmul.vx v0, v31, t3
        vsmul.vx v31, v31, t4
        vnmsac.vx v0, t0, v31
        vsub.vv v31, v30, v0
        vadd.vv v30, v30, v0
        vsetvli zero, t1, e16, m1, ta, ma
        mv t5, a0
        vse16.v v16, (t5)
        addi t5, t5, 0x20
        vse16.v v17, (t5)
        addi t5, t5, 0x20
        vse16.v v18, (t5)
        addi t5, t5, 0x20
        vse16.v v19, (t5)
        addi t5, t5, 0x20
        vse16.v v20, (t5)
        addi t5, t5, 0x20
        vse16.v v21, (t5)
        addi t5, t5, 0x20
        vse16.v v22, (t5)
        addi t5, t5, 0x20
        vse16.v v23, (t5)
        addi t5, t5, 0x20
        vse16.v v24, (t5)
        addi t5, t5, 0x20
        vse16.v v25, (t5)
        addi t5, t5, 0x20
        vse16.v v26, (t5)
        addi t5, t5, 0x20
        vse16.v v27, (t5)
        addi t5, t5, 0x20
        vse16.v v28, (t5)
        addi t5, t5, 0x20
        vse16.v v29, (t5)
        addi t5, t5, 0x20
        vse16.v v30, (t5)
        addi t5, t5, 0x20
        vse16.v v31, (t5)
        addi t5, t5, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        addi t5, a0, 0x10
        vle16.v v16, (t5)
        addi t5, t5, 0x20
        vle16.v v17, (t5)
        addi t5, t5, 0x20
        vle16.v v18, (t5)
        addi t5, t5, 0x20
        vle16.v v19, (t5)
        addi t5, t5, 0x20
        vle16.v v20, (t5)
        addi t5, t5, 0x20
        vle16.v v21, (t5)
        addi t5, t5, 0x20
        vle16.v v22, (t5)
        addi t5, t5, 0x20
        vle16.v v23, (t5)
        addi t5, t5, 0x20
        vle16.v v24, (t5)
        addi t5, t5, 0x20
        vle16.v v25, (t5)
        addi t5, t5, 0x20
        vle16.v v26, (t5)
        addi t5, t5, 0x20
        vle16.v v27, (t5)
        addi t5, t5, 0x20
        vle16.v v28, (t5)
        addi t5, t5, 0x20
        vle16.v v29, (t5)
        addi t5, t5, 0x20
        vle16.v v30, (t5)
        addi t5, t5, 0x20
        vle16.v v31, (t5)
        addi t5, t5, 0x20
        vsetvli zero, a4, e16, m8, ta, ma
        lh t3, 0x0(a1)
        lh t4, 0x2(a1)
        vmul.vx v0, v24, t3
        vsmul.vx v24, v24, t4
        vnmsac.vx v0, t0, v24
        vsub.vv v24, v16, v0
        vadd.vv v16, v16, v0
        vsetvli zero, a3, e16, m4, ta, ma
        lh t3, 0x4(a1)
        lh t4, 0x6(a1)
        vmul.vx v0, v20, t3
        vsmul.vx v20, v20, t4
        vnmsac.vx v0, t0, v20
        vsub.vv v20, v16, v0
        vadd.vv v16, v16, v0
        lh t3, 0x8(a1)
        lh t4, 0xa(a1)
        vmul.vx v0, v28, t3
        vsmul.vx v28, v28, t4
        vnmsac.vx v0, t0, v28
        vsub.vv v28, v24, v0
        vadd.vv v24, v24, v0
        vsetvli zero, t2, e16, m2, ta, ma
        lh t3, 0xc(a1)
        lh t4, 0xe(a1)
        vmul.vx v0, v18, t3
        vsmul.vx v18, v18, t4
        vnmsac.vx v0, t0, v18
        vsub.vv v18, v16, v0
        vadd.vv v16, v16, v0
        lh t3, 0x10(a1)
        lh t4, 0x12(a1)
        vmul.vx v0, v22, t3
        vsmul.vx v22, v22, t4
        vnmsac.vx v0, t0, v22
        vsub.vv v22, v20, v0
        vadd.vv v20, v20, v0
        lh t3, 0x14(a1)
        lh t4, 0x16(a1)
        vmul.vx v0, v26, t3
        vsmul.vx v26, v26, t4
        vnmsac.vx v0, t0, v26
        vsub.vv v26, v24, v0
        vadd.vv v24, v24, v0
        lh t3, 0x18(a1)
        lh t4, 0x1a(a1)
        vmul.vx v0, v30, t3
        vsmul.vx v30, v30, t4
        vnmsac.vx v0, t0, v30
        vsub.vv v30, v28, v0
        vadd.vv v28, v28, v0
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x1c(a1)
        lh t4, 0x1e(a1)
        vmul.vx v0, v17, t3
        vsmul.vx v17, v17, t4
        vnmsac.vx v0, t0, v17
        vsub.vv v17, v16, v0
        vadd.vv v16, v16, v0
        lh t3, 0x20(a1)
        lh t4, 0x22(a1)
        vmul.vx v0, v19, t3
        vsmul.vx v19, v19, t4
        vnmsac.vx v0, t0, v19
        vsub.vv v19, v18, v0
        vadd.vv v18, v18, v0
        lh t3, 0x24(a1)
        lh t4, 0x26(a1)
        vmul.vx v0, v21, t3
        vsmul.vx v21, v21, t4
        vnmsac.vx v0, t0, v21
        vsub.vv v21, v20, v0
        vadd.vv v20, v20, v0
        lh t3, 0x28(a1)
        lh t4, 0x2a(a1)
        vmul.vx v0, v23, t3
        vsmul.vx v23, v23, t4
        vnmsac.vx v0, t0, v23
        vsub.vv v23, v22, v0
        vadd.vv v22, v22, v0
        lh t3, 0x2c(a1)
        lh t4, 0x2e(a1)
        vmul.vx v0, v25, t3
        vsmul.vx v25, v25, t4
        vnmsac.vx v0, t0, v25
        vsub.vv v25, v24, v0
        vadd.vv v24, v24, v0
        lh t3, 0x30(a1)
        lh t4, 0x32(a1)
        vmul.vx v0, v27, t3
        vsmul.vx v27, v27, t4
        vnmsac.vx v0, t0, v27
        vsub.vv v27, v26, v0
        vadd.vv v26, v26, v0
        lh t3, 0x34(a1)
        lh t4, 0x36(a1)
        vmul.vx v0, v29, t3
        vsmul.vx v29, v29, t4
        vnmsac.vx v0, t0, v29
        vsub.vv v29, v28, v0
        vadd.vv v28, v28, v0
        lh t3, 0x38(a1)
        lh t4, 0x3a(a1)
        vmul.vx v0, v31, t3
        vsmul.vx v31, v31, t4
        vnmsac.vx v0, t0, v31
        vsub.vv v31, v30, v0
        vadd.vv v30, v30, v0
        vsetvli zero, t1, e16, m1, ta, ma
        addi t5, a0, 0x10
        vse16.v v16, (t5)
        addi t5, t5, 0x20
        vse16.v v17, (t5)
        addi t5, t5, 0x20
        vse16.v v18, (t5)
        addi t5, t5, 0x20
        vse16.v v19, (t5)
        addi t5, t5, 0x20
        vse16.v v20, (t5)
        addi t5, t5, 0x20
        vse16.v v21, (t5)
        addi t5, t5, 0x20
        vse16.v v22, (t5)
        addi t5, t5, 0x20
        vse16.v v23, (t5)
        addi t5, t5, 0x20
        vse16.v v24, (t5)
        addi t5, t5, 0x20
        vse16.v v25, (t5)
        addi t5, t5, 0x20
        vse16.v v26, (t5)
        addi t5, t5, 0x20
        vse16.v v27, (t5)
        addi t5, t5, 0x20
        vse16.v v28, (t5)
        addi t5, t5, 0x20
        vse16.v v29, (t5)
        addi t5, t5, 0x20
        vse16.v v30, (t5)
        addi t5, t5, 0x20
        vse16.v v31, (t5)
        addi t5, t5, 0x20
        vsetvli zero, t2, e16, m2, ta, ma
        vle16.v v8, (a2)
        addi t5, a2, 0x20
        vle16.v v10, (t5)
        addi t5, a2, 0x40
        vle16.v v12, (t5)
        addi a5, a1, 0x40
        addi t6, a1, 0x80
        mv a6, a0
        vsetvli zero, a4, e16, m8, ta, ma
        vle16.v v16, (a6)
        addi t5, a6, 0x80
        vle16.v v24, (t5)
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v17, t3
        vsmul.vx v17, v17, t4
        vnmsac.vx v0, t0, v17
        vsub.vv v17, v16, v0
        vadd.vv v16, v16, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v16, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v16, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v17, v6
        vsmul.vv v4, v17, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v17, v16, v5
        vadd.vv v16, v16, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v16, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v19, t3
        vsmul.vx v19, v19, t4
        vnmsac.vx v0, t0, v19
        vsub.vv v19, v18, v0
        vadd.vv v18, v18, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v18, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v18, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v19, v6
        vsmul.vv v4, v19, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v19, v18, v5
        vadd.vv v18, v18, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v18, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v21, t3
        vsmul.vx v21, v21, t4
        vnmsac.vx v0, t0, v21
        vsub.vv v21, v20, v0
        vadd.vv v20, v20, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v20, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v20, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v21, v6
        vsmul.vv v4, v21, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v21, v20, v5
        vadd.vv v20, v20, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v20, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v23, t3
        vsmul.vx v23, v23, t4
        vnmsac.vx v0, t0, v23
        vsub.vv v23, v22, v0
        vadd.vv v22, v22, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v22, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v22, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v23, v6
        vsmul.vv v4, v23, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v23, v22, v5
        vadd.vv v22, v22, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v22, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v25, t3
        vsmul.vx v25, v25, t4
        vnmsac.vx v0, t0, v25
        vsub.vv v25, v24, v0
        vadd.vv v24, v24, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v24, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v24, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v25, v6
        vsmul.vv v4, v25, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v25, v24, v5
        vadd.vv v24, v24, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v24, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v27, t3
        vsmul.vx v27, v27, t4
        vnmsac.vx v0, t0, v27
        vsub.vv v27, v26, v0
        vadd.vv v26, v26, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v26, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v26, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v27, v6
        vsmul.vv v4, v27, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v27, v26, v5
        vadd.vv v26, v26, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v26, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v29, t3
        vsmul.vx v29, v29, t4
        vnmsac.vx v0, t0, v29
        vsub.vv v29, v28, v0
        vadd.vv v28, v28, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v28, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v28, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v29, v6
        vsmul.vv v4, v29, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v29, v28, v5
        vadd.vv v28, v28, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v28, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v31, t3
        vsmul.vx v31, v31, t4
        vnmsac.vx v0, t0, v31
        vsub.vv v31, v30, v0
        vadd.vv v30, v30, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v30, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v30, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v31, v6
        vsmul.vv v4, v31, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v31, v30, v5
        vadd.vv v30, v30, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v30, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, a4, e16, m8, ta, ma
        vle16.v v16, (a6)
        addi t5, a6, 0x80
        vle16.v v24, (t5)
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v17, t3
        vsmul.vx v17, v17, t4
        vnmsac.vx v0, t0, v17
        vsub.vv v17, v16, v0
        vadd.vv v16, v16, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v16, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v16, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v17, v6
        vsmul.vv v4, v17, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v17, v16, v5
        vadd.vv v16, v16, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v16, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v19, t3
        vsmul.vx v19, v19, t4
        vnmsac.vx v0, t0, v19
        vsub.vv v19, v18, v0
        vadd.vv v18, v18, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v18, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v18, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v19, v6
        vsmul.vv v4, v19, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v19, v18, v5
        vadd.vv v18, v18, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v18, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v21, t3
        vsmul.vx v21, v21, t4
        vnmsac.vx v0, t0, v21
        vsub.vv v21, v20, v0
        vadd.vv v20, v20, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v20, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v20, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v21, v6
        vsmul.vv v4, v21, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v21, v20, v5
        vadd.vv v20, v20, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v20, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v23, t3
        vsmul.vx v23, v23, t4
        vnmsac.vx v0, t0, v23
        vsub.vv v23, v22, v0
        vadd.vv v22, v22, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v22, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v22, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v23, v6
        vsmul.vv v4, v23, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v23, v22, v5
        vadd.vv v22, v22, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v22, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v25, t3
        vsmul.vx v25, v25, t4
        vnmsac.vx v0, t0, v25
        vsub.vv v25, v24, v0
        vadd.vv v24, v24, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v24, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v24, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v25, v6
        vsmul.vv v4, v25, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v25, v24, v5
        vadd.vv v24, v24, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v24, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v27, t3
        vsmul.vx v27, v27, t4
        vnmsac.vx v0, t0, v27
        vsub.vv v27, v26, v0
        vadd.vv v26, v26, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v26, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v26, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v27, v6
        vsmul.vv v4, v27, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v27, v26, v5
        vadd.vv v26, v26, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v26, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v29, t3
        vsmul.vx v29, v29, t4
        vnmsac.vx v0, t0, v29
        vsub.vv v29, v28, v0
        vadd.vv v28, v28, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v28, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v28, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v29, v6
        vsmul.vv v4, v29, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v29, v28, v5
        vadd.vv v28, v28, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v28, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        vsetvli zero, t1, e16, m1, ta, ma
        lh t3, 0x0(a5)
        lh t4, 0x2(a5)
        addi a5, a5, 0x4
        vmul.vx v0, v31, t3
        vsmul.vx v31, v31, t4
        vnmsac.vx v0, t0, v31
        vsub.vv v31, v30, v0
        vadd.vv v30, v30, v0
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v30, v8
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v3, v6
        vsmul.vv v4, v3, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v3, v2, v5
        vadd.vv v2, v2, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v30, v2, v10
        vsetvli zero, t1, e16, m1, ta, ma
        vle16.v v6, (t6)
        addi t6, t6, 0x10
        vle16.v v7, (t6)
        addi t6, t6, 0x10
        vmul.vv v5, v31, v6
        vsmul.vv v4, v31, v7
        vnmsac.vx v5, t0, v4
        vsub.vv v31, v30, v5
        vadd.vv v30, v30, v5
        vsetvli zero, t2, e16, m2, ta, ma
        vrgatherei16.vv v2, v30, v12
        vse16.v v2, (a6)
        addi a6, a6, 0x20
        ret

.option pop
MLK_ASM_FN_SIZE(ntt_vlen128_riscv64_asm)

#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
