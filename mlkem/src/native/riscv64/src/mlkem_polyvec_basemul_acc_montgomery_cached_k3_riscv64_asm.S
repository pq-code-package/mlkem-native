/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm
  Description: Scalar product of length-3 polynomial vectors in NTT domain, using the multiplication cache of b, with Montgomery reduction
  Signature: void mlk_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm(int16_t r[256], const int16_t a[768], const int16_t b[768], const int16_t b_cache[384])
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [RVV]
    a0:
      type: buffer
      size_bytes: 512
      permissions: write-only
      c_parameter: int16_t r[256]
      description: Output polynomial
    a1:
      type: buffer
      size_bytes: 1536
      permissions: read-only
      c_parameter: const int16_t a[768]
      description: Input polynomial vector a (3 x 256 x int16_t)
    a2:
      type: buffer
      size_bytes: 1536
      permissions: read-only
      c_parameter: const int16_t b[768]
      description: Input polynomial vector b (3 x 256 x int16_t)
    a3:
      type: buffer
      size_bytes: 768
      permissions: read-only
      c_parameter: const int16_t b_cache[384]
      description: Multiplication cache of b (3 x 128 x int16_t)
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 3)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/riscv64/src/mlkem_polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm)
MLK_ASM_FN_SYMBOL(polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm)

        lui t1, 0x1
        addiw t1, t1, -0x2ff
        lui t2, 0xfffff
        addiw t2, t2, 0x301
        li a4, 0x80
        vsetvli t0, a4, e16, m2, ta, ma
        slli t3, t0, 0x2
        slli t4, t0, 0x1

mlk_polyvec_basemul_acc_montgomery_cached_k3_riscv64_loop:
        mv t5, a1
        mv t6, a2
        mv a5, a3
        vlseg2e16.v v8, (t5)
        vlseg2e16.v v12, (t6)
        vle16.v v16, (a5)
        vwmul.vv v24, v8, v12
        vwmul.vv v28, v8, v14
        vwmacc.vv v24, v10, v16
        vwmacc.vv v28, v10, v12
        addi t5, a1, 0x200
        addi t6, a2, 0x200
        addi a5, a3, 0x100
        vlseg2e16.v v8, (t5)
        vlseg2e16.v v12, (t6)
        vle16.v v16, (a5)
        vwmacc.vv v24, v8, v12
        vwmacc.vv v28, v8, v14
        vwmacc.vv v24, v10, v16
        vwmacc.vv v28, v10, v12
        addi t5, a1, 0x400
        addi t6, a2, 0x400
        addi a5, a3, 0x200
        vlseg2e16.v v8, (t5)
        vlseg2e16.v v12, (t6)
        vle16.v v16, (a5)
        vwmacc.vv v24, v8, v12
        vwmacc.vv v28, v8, v14
        vwmacc.vv v24, v10, v16
        vwmacc.vv v28, v10, v12
        vnsrl.wi v20, v24, 0x0
        vnsra.wi v8, v24, 0x10
        vmul.vx v20, v20, t2
        vmulh.vx v20, v20, t1
        vsub.vv v8, v8, v20
        vnsrl.wi v20, v28, 0x0
        vnsra.wi v10, v28, 0x10
        vmul.vx v20, v20, t2
        vmulh.vx v20, v20, t1
        vsub.vv v10, v10, v20
        vsseg2e16.v v8, (a0)
        add a0, a0, t3
        add a1, a1, t3
        add a2, a2, t3
        add a3, a3, t4
        sub a4, a4, t0
        bnez a4, mlk_polyvec_basemul_acc_montgomery_cached_k3_riscv64_loop
        ret

.option pop
MLK_ASM_FN_SIZE(polyvec_basemul_acc_montgomery_cached_k3_riscv64_asm)

#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 3) */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
