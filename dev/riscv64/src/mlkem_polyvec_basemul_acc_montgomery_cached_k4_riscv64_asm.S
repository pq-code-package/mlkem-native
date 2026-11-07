/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm
  Description: Scalar product of length-4 polynomial vectors in NTT domain, using the multiplication cache of b, with Montgomery reduction
  Signature: void mlk_polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm(int16_t r[256], const int16_t a[1024], const int16_t b[1024], const int16_t b_cache[512])
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
      size_bytes: 2048
      permissions: read-only
      c_parameter: const int16_t a[1024]
      description: Input polynomial vector a (4 x 256 x int16_t)
    a2:
      type: buffer
      size_bytes: 2048
      permissions: read-only
      c_parameter: const int16_t b[1024]
      description: Input polynomial vector b (4 x 256 x int16_t)
    a3:
      type: buffer
      size_bytes: 1024
      permissions: read-only
      c_parameter: const int16_t b_cache[512]
      description: Multiplication cache of b (4 x 128 x int16_t)
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)
/* simpasm: header-end */

#include "rv64v_basemul.inc"

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm)
MLK_ASM_FN_SYMBOL(polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm)

        polyvec_basemul 4, mlk_polyvec_basemul_acc_montgomery_cached_k4_riscv64_loop

        ret
.option pop

MLK_ASM_FN_SIZE(polyvec_basemul_acc_montgomery_cached_k4_riscv64_asm)

/* simpasm: footer-start */
#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
