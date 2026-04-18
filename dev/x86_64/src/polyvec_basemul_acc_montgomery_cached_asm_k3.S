/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 3)
/*yaml
  Name: polyvec_basemul_acc_montgomery_cached_asm_k3
  Description: x86_64 AVX2 base multiplication with accumulation (k=3)
  Signature: void mlk_polyvec_basemul_acc_montgomery_cached_asm_k3(int16_t *r, const int16_t *a, const int16_t *b, const int16_t *b_cache)
  ABI:
    rdi:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t *r
      description: Output polynomial (256 x int16_t)
    rsi:
      type: buffer
      size_bytes: 1536
      permissions: read-only
      c_parameter: const int16_t *a
      description: Input polyvec a (3 x 256 x int16_t)
    rdx:
      type: buffer
      size_bytes: 1536
      permissions: read-only
      c_parameter: const int16_t *b
      description: Input polyvec b (3 x 256 x int16_t)
    rcx:
      type: buffer
      size_bytes: 768
      permissions: read-only
      c_parameter: const int16_t *b_cache
      description: Mulcache for b (3 x 128 x int16_t)
*/

/* simpasm: header-end */

#include "consts.h"
#include "poly_basemul.inc"

.global MLK_ASM_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k3)
.balign 4
MLK_ASM_FN_SYMBOL(polyvec_basemul_acc_montgomery_cached_asm_k3)

polyvec_basemul 3

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 3) */
