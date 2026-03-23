/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/*yaml
  Name: poly_mulcache_compute_avx2
  Description: x86_64 AVX2 mulcache computation
  Signature: void mlk_poly_mulcache_compute_avx2(int16_t *out, const int16_t *in, const int16_t *qdata)
  ABI:
    rdi:
      type: buffer
      size_bytes: 256
      permissions: write-only
      c_parameter: int16_t *out
      description: Output mulcache (128 x int16_t)
    rsi:
      type: buffer
      size_bytes: 512
      permissions: read-only
      c_parameter: const int16_t *in
      description: Input polynomial (256 x int16_t)
    rdx:
      type: buffer
      size_bytes: 1248
      permissions: read-only
      c_parameter: const int16_t *qdata
      description: Precomputed constants (624 x int16_t)
*/

/* simpasm: header-end */

#include "consts.h"

.macro mulcache_compute_iter i
vmovdqa (64*\i+16)*2(%rsi), %ymm2
vmovdqa (64*\i+48)*2(%rsi), %ymm3
vmovdqa (MLK_AVX2_BACKEND_DATA_OFFSET_MULCACHE_TWIDDLES + 16*\i)*2(%rdx), %ymm4
vmovdqa (MLK_AVX2_BACKEND_DATA_OFFSET_MULCACHE_TWIDDLES + 64 + 16*\i)*2(%rdx), %ymm1

vpmullw %ymm2, %ymm1, %ymm5
vpmullw %ymm3, %ymm1, %ymm6

vpmulhw %ymm2, %ymm4, %ymm7
vpmulhw %ymm3, %ymm4, %ymm8
vpmulhw %ymm5, %ymm0, %ymm9
vpmulhw %ymm6, %ymm0, %ymm10

vpsubw %ymm9, %ymm7, %ymm7
vpsubw %ymm10, %ymm8, %ymm8

vmovdqa %ymm7, (32*\i)*2(%rdi)
vmovdqa %ymm8, (32*\i+16)*2(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(poly_mulcache_compute_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_mulcache_compute_avx2)

// Broadcast 3329 (0x0D01) to all elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

mulcache_compute_iter 0
mulcache_compute_iter 1
mulcache_compute_iter 2
mulcache_compute_iter 3

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
