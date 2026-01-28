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
 * Name:        mlk_poly_compress_d5_avx2
 *
 * Description: Compression of a polynomial to 5 bits per coefficient.
 *
 * Arguments:   - uint8_t *r:       pointer to output byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D5)
 *              - const int16_t *a: pointer to input polynomial
 *              - const int8_t *data: pointer to shufbidx constant
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)
/* simpasm: header-end */

.text
.global MLK_ASM_NAMESPACE(poly_compress_d5_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d5_avx2)

// Broadcast v = 20159 (0x4EBF) to all 16-bit elements of ymm0
movl $0x4ebf4ebf, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast shift1 = 1024 (1 << 10) to all 16-bit elements of ymm1
movl $0x04000400, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

// Broadcast mask = 31 (0x001F) to all 16-bit elements of ymm2
movl $0x001f001f, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

// Broadcast shift2 = (32 << 8) + 1 = 0x2001 to all 16-bit elements of ymm3
movl $0x20012001, %eax
vmovd %eax, %xmm3
vpbroadcastd %xmm3, %ymm3

// Broadcast shift3 = (1024 << 16) + 1 = 0x04000001 to all 32-bit elements
movl $0x04000001, %eax
vmovd %eax, %xmm4
vpbroadcastd %xmm4, %ymm4

// Broadcast sllvdidx = 12 to all 64-bit elements of ymm5
movl $12, %eax
vmovq %rax, %xmm5
vpbroadcastq %xmm5, %ymm5

// Load shufbidx constant from 3rd argument
vmovdqa (%rdx), %ymm6

// Loop counter: 8 iterations for 256 coefficients / 32 per iteration
movl $8, %ecx

poly_compress_d5_avx2_loop:
// Load 32 coefficients (64 bytes)
vmovdqa 0(%rsi), %ymm7
vmovdqa 32(%rsi), %ymm8

// Multiply by v and take high 16 bits
vpmulhw %ymm0, %ymm7, %ymm7
vpmulhw %ymm0, %ymm8, %ymm8

// Rounding: multiply-high-round-saturate by shift1
vpmulhrsw %ymm1, %ymm7, %ymm7
vpmulhrsw %ymm1, %ymm8, %ymm8

// Mask to 5 bits
vpand %ymm2, %ymm7, %ymm7
vpand %ymm2, %ymm8, %ymm8

// Pack 16-bit to 8-bit
vpackuswb %ymm8, %ymm7, %ymm7

// Combine pairs of 5-bit values: maddubs with shift2
vpmaddubsw %ymm3, %ymm7, %ymm7

// Combine again with shift3 (32-bit multiply-add)
vpmaddwd %ymm4, %ymm7, %ymm7

// Shift left by 12 bits per 32-bit element
vpsllvd %ymm5, %ymm7, %ymm7

// Shift right by 12 bits per 64-bit element
vpsrlvq %ymm5, %ymm7, %ymm7

// Shuffle bytes for output format
vpshufb %ymm6, %ymm7, %ymm7

// Extract low and high 128-bit lanes
vextracti128 $1, %ymm7, %xmm8

// Blend using shufbidx as mask (high bit of each byte selects source)
vpblendvb %xmm6, %xmm8, %xmm7, %xmm7

// Store 16 bytes
vmovdqu %xmm7, 0(%rdi)

// Store remaining 4 bytes from high lane
vmovd %xmm8, 16(%rdi)

// Advance pointers
addq $64, %rsi
addq $20, %rdi

decl %ecx
jnz poly_compress_d5_avx2_loop

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
