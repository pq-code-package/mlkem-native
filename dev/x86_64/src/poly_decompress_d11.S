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
 * Name:        mlk_poly_decompress_d11_avx2
 *
 * Description: Decompression of a polynomial from 11 bits per coefficient.
 *
 * Arguments:   - int16_t *r:       pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D11)
 *              - const int8_t *data: pointer to constants
 *                                    (shufbidx, srlvdidx, srlvqidx, shift)
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)
/* simpasm: header-end */

.text
.global MLK_ASM_NAMESPACE(poly_decompress_d11_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d11_avx2)

// Broadcast q = 3329 to all 16-bit elements of ymm0
movl $0x0d010d01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast mask = 32752 (0x7FF0) to all 16-bit elements of ymm1
movl $0x7ff07ff0, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

// Load shufbidx from data[0:31]
vmovdqa (%rdx), %ymm2

// Load srlvdidx from data[32:63]
vmovdqa 32(%rdx), %ymm3

// Load srlvqidx from data[64:95]
vmovdqa 64(%rdx), %ymm4

// Load shift from data[96:127]
vmovdqa 96(%rdx), %ymm5

// Loop counter: 15 iterations (last one handled specially)
movl $15, %ecx

poly_decompress_d11_avx2_loop:
// Load 32 bytes (unaligned)
vmovdqu (%rsi), %ymm6

// f = permute4x64(f, 0x94)
vpermq $0x94, %ymm6, %ymm6

// f = shuffle_epi8(f, shufbidx)
vpshufb %ymm2, %ymm6, %ymm6

// f = srlv_epi32(f, srlvdidx)
vpsrlvd %ymm3, %ymm6, %ymm6

// f = srlv_epi64(f, srlvqidx)
vpsrlvq %ymm4, %ymm6, %ymm6

// f = mullo_epi16(f, shift)
vpmullw %ymm5, %ymm6, %ymm6

// f = srli_epi16(f, 1)
vpsrlw $1, %ymm6, %ymm6

// f = and(f, mask)
vpand %ymm1, %ymm6, %ymm6

// f = mulhrs_epi16(f, q)
vpmulhrsw %ymm0, %ymm6, %ymm6

// Store 32 bytes (unaligned)
vmovdqu %ymm6, (%rdi)

// Advance pointers
addq $22, %rsi
addq $32, %rdi

decl %ecx
jnz poly_decompress_d11_avx2_loop

// Last iteration: load only 22 bytes to avoid reading beyond buffer
// Load first 16 bytes into xmm6
vmovdqu (%rsi), %xmm6
// Load bytes 16-19 (4 bytes) into eax
movl 16(%rsi), %eax
// Load bytes 20-21 (2 bytes) into r8d
movzwl 20(%rsi), %r8d
// Create xmm7 with the remaining 6 bytes
vmovd %eax, %xmm7
vpinsrw $2, %r8d, %xmm7, %xmm7
// Combine xmm6 (low) and xmm7 (high) into ymm6
vinserti128 $1, %xmm7, %ymm6, %ymm6

// f = permute4x64(f, 0x94)
vpermq $0x94, %ymm6, %ymm6

// f = shuffle_epi8(f, shufbidx)
vpshufb %ymm2, %ymm6, %ymm6

// f = srlv_epi32(f, srlvdidx)
vpsrlvd %ymm3, %ymm6, %ymm6

// f = srlv_epi64(f, srlvqidx)
vpsrlvq %ymm4, %ymm6, %ymm6

// f = mullo_epi16(f, shift)
vpmullw %ymm5, %ymm6, %ymm6

// f = srli_epi16(f, 1)
vpsrlw $1, %ymm6, %ymm6

// f = and(f, mask)
vpand %ymm1, %ymm6, %ymm6

// f = mulhrs_epi16(f, q)
vpmulhrsw %ymm0, %ymm6, %ymm6

// Store 32 bytes (unaligned)
vmovdqu %ymm6, (%rdi)

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
