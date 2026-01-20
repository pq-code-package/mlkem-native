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
 * Name:        mlk_poly_decompress_d10_avx2
 *
 * Description: Decompression of a polynomial from 10 bits per coefficient.
 *
 * Arguments:   - int16_t *r:       pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D10)
 *              - const int8_t *data: pointer to shufbidx constant
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)
/* simpasm: header-end */

.text
.global MLK_ASM_NAMESPACE(poly_decompress_d10_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d10_avx2)

// Broadcast q = (MLKEM_Q << 16) + 4 * MLKEM_Q = 0x0D013404 to ymm0
movl $0x0D013404, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast sllvdidx = 4 to all 64-bit elements of ymm1
movl $4, %eax
vmovq %rax, %xmm1
vpbroadcastq %xmm1, %ymm1

// Broadcast mask = (32736 << 16) + 8184 = 0x7FE01FF8 to ymm2
movl $0x7FE01FF8, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

// Load shufbidx constant from 3rd argument
vmovdqa (%rdx), %ymm3

// Loop counter: 15 iterations (last one handled specially)
movl $15, %ecx

poly_decompress_d10_avx2_loop:
// Load 32 bytes (we only need 20, but this is safe for first 15 iterations)
vmovdqu (%rsi), %ymm4

// Permute 64-bit elements: 0x94 = 10 01 01 00 = [2,1,1,0]
vpermq $0x94, %ymm4, %ymm4

// Shuffle bytes
vpshufb %ymm3, %ymm4, %ymm4

// Shift left by 4 bits per 32-bit element
vpsllvd %ymm1, %ymm4, %ymm4

// Shift right by 1 bit per 16-bit element
vpsrlw $1, %ymm4, %ymm4

// Mask
vpand %ymm2, %ymm4, %ymm4

// Multiply-high-round-saturate by q
vpmulhrsw %ymm0, %ymm4, %ymm4

// Store 16 coefficients (32 bytes)
vmovdqu %ymm4, (%rdi)

// Advance pointers
addq $20, %rsi
addq $32, %rdi

decl %ecx
jnz poly_decompress_d10_avx2_loop

// Last iteration: load only 20 bytes to avoid buffer overflow
// Load 16 bytes + 4 bytes separately
vmovdqu (%rsi), %xmm4
vmovd 16(%rsi), %xmm5
vinserti128 $1, %xmm5, %ymm4, %ymm4

// Same processing as loop body
vpermq $0x94, %ymm4, %ymm4
vpshufb %ymm3, %ymm4, %ymm4
vpsllvd %ymm1, %ymm4, %ymm4
vpsrlw $1, %ymm4, %ymm4
vpand %ymm2, %ymm4, %ymm4
vpmulhrsw %ymm0, %ymm4, %ymm4
vmovdqu %ymm4, (%rdi)

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == \
          3) */
