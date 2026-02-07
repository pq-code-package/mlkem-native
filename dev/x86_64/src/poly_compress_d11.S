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
 * Name:        mlk_poly_compress_d11_avx2
 *
 * Description: Compression of a polynomial to 11 bits per coefficient.
 *
 * Arguments:   - uint8_t *r:       pointer to output byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D11)
 *              - const int16_t *a: pointer to input polynomial
 *              - const uint8_t *data: pointer to constants
 *                                  (srlvqidx[0:32], shufbidx[32:64])
 **************************************************/

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)
/* simpasm: header-end */

.text
.global MLK_ASM_NAMESPACE(poly_compress_d11_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d11_avx2)

// Broadcast v = 20159 (0x4EBF) to all 16-bit elements of ymm0
movl $0x4ebf4ebf, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Compute v8 = v << 3 in ymm1
vpsllw $3, %ymm0, %ymm1

// Broadcast off = 36 to all 16-bit elements of ymm2
movl $0x00240024, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

// Broadcast shift1 = 8192 (1 << 13) to all 16-bit elements of ymm3
movl $0x20002000, %eax
vmovd %eax, %xmm3
vpbroadcastd %xmm3, %ymm3

// Broadcast mask = 2047 (0x07FF) to all 16-bit elements of ymm4
movl $0x07ff07ff, %eax
vmovd %eax, %xmm4
vpbroadcastd %xmm4, %ymm4

// Broadcast shift2 = (2048 << 48) + (1 << 32) + (2048 << 16) + 1 to ymm5
movabsq $0x0800000108000001, %rax
vmovq %rax, %xmm5
vpbroadcastq %xmm5, %ymm5

// Broadcast sllvdidx = 10 to all 64-bit elements of ymm6
movl $10, %eax
vmovq %rax, %xmm6
vpbroadcastq %xmm6, %ymm6

// Load srlvqidx from data[0:31]
vmovdqa (%rdx), %ymm7

// Load shufbidx from data[32:63]
vmovdqa 32(%rdx), %ymm8

// Fully unrolled: 16 iterations for 256 coefficients / 16 per iteration
// Each iteration stores exactly 22 bytes (vmovdqu 16B + vmovd 4B + vpextrw 2B)
.macro compress_d11_iter src_off, dst_off
    vmovdqa \src_off(%rsi), %ymm9
    vpmullw %ymm1, %ymm9, %ymm10
    vpaddw %ymm2, %ymm9, %ymm11
    vpsllw $3, %ymm9, %ymm9
    vpmulhw %ymm0, %ymm9, %ymm9
    vpsubw %ymm11, %ymm10, %ymm11
    vpandn %ymm11, %ymm10, %ymm10
    vpsrlw $15, %ymm10, %ymm10
    vpsubw %ymm10, %ymm9, %ymm9
    vpmulhrsw %ymm3, %ymm9, %ymm9
    vpand %ymm4, %ymm9, %ymm9
    vpmaddwd %ymm5, %ymm9, %ymm9
    vpsllvd %ymm6, %ymm9, %ymm9
    vpsrldq $8, %ymm9, %ymm10
    vpsrlvq %ymm7, %ymm9, %ymm9
    vpsllq $34, %ymm10, %ymm10
    vpaddq %ymm10, %ymm9, %ymm9
    vpshufb %ymm8, %ymm9, %ymm9
    vextracti128 $1, %ymm9, %xmm10
    vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
    vmovdqu %xmm9, \dst_off(%rdi)
    vmovd %xmm10, \dst_off+16(%rdi)
    vpextrw $2, %xmm10, \dst_off+20(%rdi)
.endm

compress_d11_iter 0, 0
compress_d11_iter 32, 22
compress_d11_iter 64, 44
compress_d11_iter 96, 66
compress_d11_iter 128, 88
compress_d11_iter 160, 110
compress_d11_iter 192, 132
compress_d11_iter 224, 154
compress_d11_iter 256, 176
compress_d11_iter 288, 198
compress_d11_iter 320, 220
compress_d11_iter 352, 242
compress_d11_iter 384, 264
compress_d11_iter 416, 286
compress_d11_iter 448, 308
compress_d11_iter 480, 330

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
