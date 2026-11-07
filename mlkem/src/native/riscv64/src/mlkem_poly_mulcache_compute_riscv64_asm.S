/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: poly_mulcache_compute_riscv64_asm
  Description: Compute the multiplication cache of a polynomial in NTT domain
  Signature: void mlk_poly_mulcache_compute_riscv64_asm(int16_t cache[128], const int16_t p[256], const int16_t zetas[256])
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [RVV]
    a0:
      type: buffer
      size_bytes: 256
      permissions: write-only
      c_parameter: int16_t cache[128]
      description: Output multiplication cache
    a1:
      type: buffer
      size_bytes: 512
      permissions: read-only
      c_parameter: const int16_t p[256]
      description: Input polynomial
    a2:
      type: buffer
      size_bytes: 512
      permissions: read-only
      c_parameter: const int16_t zetas[256]
      description: Twiddle table (mlk_rv64v_mulcache_zetas)
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/riscv64/src/mlkem_poly_mulcache_compute_riscv64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(poly_mulcache_compute_riscv64_asm)
MLK_ASM_FN_SYMBOL(poly_mulcache_compute_riscv64_asm)

        csrwi vxrm, 0x0
        lui t1, 0x1
        addiw t1, t1, -0x2ff
        li a3, 0x80
        addi a4, a2, 0x100
        vsetvli t0, a3, e16, m2, ta, ma
        slli t2, t0, 0x2
        slli t3, t0, 0x1

mlk_poly_mulcache_compute_riscv64_loop:
        vlseg2e16.v v8, (a1)
        vle16.v v12, (a2)
        vle16.v v14, (a4)
        vsmul.vv v16, v10, v14
        vmul.vv v10, v10, v12
        vnmsac.vx v10, t1, v16
        vse16.v v10, (a0)
        add a1, a1, t2
        add a0, a0, t3
        add a2, a2, t3
        add a4, a4, t3
        sub a3, a3, t0
        bnez a3, mlk_poly_mulcache_compute_riscv64_loop
        ret

.option pop
MLK_ASM_FN_SIZE(poly_mulcache_compute_riscv64_asm)

#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
