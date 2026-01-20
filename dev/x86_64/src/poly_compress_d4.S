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
 */

/*************************************************
 * Name:        mlk_poly_compress_d4_avx2_avx2
 *
 * Description: Compression of a polynomial vector to 4 bits per coefficient.
 *
 * Arguments:   - uint8_t *r:       pointer to output byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D4)
 *              - const int16_t *a: pointer to input polynomial
 *              - const int32_t *data: pointer to qdata containing permdidx
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)
/* simpasm: header-end */

#include "consts.h"

.text
.global MLK_ASM_NAMESPACE(poly_compress_d4_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d4_avx2)

// Broadcast 20159 (0x4EBF) to all 16-bit elements of ymm0
movl $0x4ebf4ebf, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast 512 (1 << 9) to all 16-bit elements of ymm1
movl $0x02000200, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

// Broadcast 15 (0x000F) to all 16-bit elements of ymm2
movl $0x000f000f, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

// Broadcast 4097 ((16 << 8) + 1) to all 16-bit elements of ymm3
movl $0x10011001, %eax
vmovd %eax, %xmm3
vpbroadcastd %xmm3, %ymm3

// Load permutation index for final reordering
vmovdqa (%rdx), %ymm4

// Loop counter: 4 iterations for 256 coefficients / 64 per iteration
movl $4, %ecx

poly_compress_d4_avx2_loop:
// Load 64 coefficients
vmovdqa 0(%rsi), %ymm5
vmovdqa 32(%rsi), %ymm6
vmovdqa 64(%rsi), %ymm7
vmovdqa 96(%rsi), %ymm8

// Multiply by v and take high 16 bits
vpmulhw %ymm0, %ymm5, %ymm5
vpmulhw %ymm0, %ymm6, %ymm6
vpmulhw %ymm0, %ymm7, %ymm7
vpmulhw %ymm0, %ymm8, %ymm8

// Rounding: multiply-high-round-saturate by shift1
vpmulhrsw %ymm1, %ymm5, %ymm5
vpmulhrsw %ymm1, %ymm6, %ymm6
vpmulhrsw %ymm1, %ymm7, %ymm7
vpmulhrsw %ymm1, %ymm8, %ymm8

// Mask to 4 bits
vpand %ymm2, %ymm5, %ymm5
vpand %ymm2, %ymm6, %ymm6
vpand %ymm2, %ymm7, %ymm7
vpand %ymm2, %ymm8, %ymm8

// Pack 16-bit to 8-bit
vpackuswb %ymm6, %ymm5, %ymm5
vpackuswb %ymm8, %ymm7, %ymm7

// Combine pairs of 4-bit values into bytes
vpmaddubsw %ymm3, %ymm5, %ymm5
vpmaddubsw %ymm3, %ymm7, %ymm7

// Pack 16-bit to 8-bit again
vpackuswb %ymm7, %ymm5, %ymm5

// Permute to correct output order
vpermd %ymm5, %ymm4, %ymm5

// Store 32 bytes
vmovdqu %ymm5, 0(%rdi)

// Advance pointers
addq $128, %rsi
addq $32, %rdi

decl %ecx
jnz poly_compress_d4_avx2_loop

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == \
          3) */
