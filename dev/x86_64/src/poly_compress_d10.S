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
 * Name:        mlk_poly_compress_d10_avx2
 *
 * Description: Compression of a polynomial to 10 bits per coefficient.
 *
 * Arguments:   - uint8_t *r:       pointer to output byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D10)
 *              - const int16_t *a: pointer to input polynomial
 *              - const int8_t *data: pointer to shufbidx constant
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)
/* simpasm: header-end */

.text
.global MLK_ASM_NAMESPACE(poly_compress_d10_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d10_avx2)

// Broadcast v = 20159 (0x4EBF) to all 16-bit elements of ymm0
movl $0x4ebf4ebf, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Compute v8 = v << 3 in ymm1
vpsllw $3, %ymm0, %ymm1

// Broadcast off = 15 to all 16-bit elements of ymm2
movl $0x000f000f, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

// Broadcast shift1 = 4096 (1 << 12) to all 16-bit elements of ymm3
movl $0x10001000, %eax
vmovd %eax, %xmm3
vpbroadcastd %xmm3, %ymm3

// Broadcast mask = 1023 (0x03FF) to all 16-bit elements of ymm4
movl $0x03ff03ff, %eax
vmovd %eax, %xmm4
vpbroadcastd %xmm4, %ymm4

// Broadcast shift2 = (1024 << 48) + (1 << 32) + (1024 << 16) + 1 to ymm5
movabsq $0x0400000104000001, %rax
vmovq %rax, %xmm5
vpbroadcastq %xmm5, %ymm5

// Broadcast sllvdidx = 12 to all 64-bit elements of ymm6
movl $12, %eax
vmovq %rax, %xmm6
vpbroadcastq %xmm6, %ymm6

// Load shufbidx constant from 3rd argument
vmovdqa (%rdx), %ymm7

// Loop counter: 16 iterations for 256 coefficients / 16 per iteration
movl $16, %ecx

poly_compress_d10_avx2_loop:
// Load 16 coefficients (32 bytes)
vmovdqa (%rsi), %ymm8

// f1 = f0 * v8
vpmullw %ymm1, %ymm8, %ymm9

// f2 = f0 + off
vpaddw %ymm2, %ymm8, %ymm10

// f0 = f0 << 3
vpsllw $3, %ymm8, %ymm8

// f0 = mulhi(f0, v)
vpmulhw %ymm0, %ymm8, %ymm8

// f2 = f1 - f2
vpsubw %ymm10, %ymm9, %ymm10

// f1 = andnot(f1, f2)
vpandn %ymm10, %ymm9, %ymm9

// f1 = f1 >> 15
vpsrlw $15, %ymm9, %ymm9

// f0 = f0 - f1
vpsubw %ymm9, %ymm8, %ymm8

// f0 = mulhrs(f0, shift1)
vpmulhrsw %ymm3, %ymm8, %ymm8

// f0 = f0 & mask
vpand %ymm4, %ymm8, %ymm8

// f0 = madd(f0, shift2)
vpmaddwd %ymm5, %ymm8, %ymm8

// f0 = f0 << sllvdidx (per 32-bit)
vpsllvd %ymm6, %ymm8, %ymm8

// f0 = f0 >> 12 (per 64-bit)
vpsrlq $12, %ymm8, %ymm8

// f0 = shuffle bytes
vpshufb %ymm7, %ymm8, %ymm8

// Extract low and high 128-bit lanes
vextracti128 $1, %ymm8, %xmm9

// Blend: t0 = blend_epi16(t0, t1, 0xE0) - take words 5-7 from t1
vpblendw $0xE0, %xmm9, %xmm8, %xmm8

// Store 16 bytes
vmovdqu %xmm8, (%rdi)

// Store remaining 4 bytes from high lane
vmovd %xmm9, 16(%rdi)

// Advance pointers
addq $32, %rsi
addq $20, %rdi

decl %ecx
jnz poly_compress_d10_avx2_loop

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == \
          3) */
