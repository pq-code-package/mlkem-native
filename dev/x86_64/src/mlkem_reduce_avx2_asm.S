/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [REF_AVX2]
 *   CRYSTALS-Kyber optimized AVX2 implementation
 *   Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/kyber/tree/main/avx2
 */

/*
 * This file is derived from the public domain
 * AVX2 Kyber implementation @[REF_AVX2].
 *
 * Changes:
 * - Replace Barrett reduction and conditional subtraction by the
 *   plantard_red16 sequence from fq.inc, which produces outputs in
 *   [0,1,...,q-1] directly, matching the semantics of mlk_poly_reduce().
 *   Its constants are those of the multiplier 1: W = (-2^32 mod q) * q^-1
 *   mod 2^32 = 0x0013afb8, split as H = 0x0014 and L = 0xafb8, bias 2.
 * - Use a macro instead of a local function call.
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/*yaml
  Name: reduce_avx2_asm
  Description: x86_64 AVX2 modular reduction
  Signature: void mlk_reduce_avx2_asm(int16_t *r)
  ABI:
    Architecture: x86_64
    CallingConvention: SysV
    Features: [AVX2]
    rdi:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t *r
      description: Input/output polynomial (256 x int16_t)
*/

/* simpasm: header-end */

#include "consts.h"
#include "fq.inc"

.macro reduce_128_coefficients offset
vmovdqa (\offset +   0)(%rdi), %ymm4
vmovdqa (\offset +  32)(%rdi), %ymm5
vmovdqa (\offset +  64)(%rdi), %ymm6
vmovdqa (\offset +  96)(%rdi), %ymm7
vmovdqa (\offset + 128)(%rdi), %ymm8
vmovdqa (\offset + 160)(%rdi), %ymm9
vmovdqa (\offset + 192)(%rdi), %ymm10
vmovdqa (\offset + 224)(%rdi), %ymm11

plantard_red16 4
plantard_red16 5
plantard_red16 6
plantard_red16 7
plantard_red16 8
plantard_red16 9
plantard_red16 10
plantard_red16 11

vmovdqa %ymm4,  (\offset +   0)(%rdi)
vmovdqa %ymm5,  (\offset +  32)(%rdi)
vmovdqa %ymm6,  (\offset +  64)(%rdi)
vmovdqa %ymm7,  (\offset +  96)(%rdi)
vmovdqa %ymm8,  (\offset + 128)(%rdi)
vmovdqa %ymm9,  (\offset + 160)(%rdi)
vmovdqa %ymm10, (\offset + 192)(%rdi)
vmovdqa %ymm11, (\offset + 224)(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(reduce_avx2_asm)
.balign 4
MLK_ASM_FN_SYMBOL(reduce_avx2_asm)

// Broadcast 3329 (0x0D01) to all elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast 0xAFB8, the low half of W, to all elements of ymm1
movl $0xAFB8AFB8, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

// Broadcast 0x0014, the high half of W, to all elements of ymm2
movl $0x00140014, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

// Broadcast the bias s = 2 to all elements of ymm3
movl $0x00020002, %eax
vmovd %eax, %xmm3
vpbroadcastd %xmm3, %ymm3

reduce_128_coefficients 0
reduce_128_coefficients 128*2

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
