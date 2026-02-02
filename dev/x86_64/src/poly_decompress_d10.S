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
 *              - const uint8_t *data: pointer to shufbidx constant
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

// Fully unrolled: 16 iterations for 256 coefficients / 16 per iteration
// Macro for one iteration with explicit offsets
.macro decompress_d10_iter src_off, dst_off
vmovdqu \src_off(%rsi), %xmm4
vmovd \src_off+16(%rsi), %xmm5
vinserti128 $1, %xmm5, %ymm4, %ymm4
vpermq $0x94, %ymm4, %ymm4
vpshufb %ymm3, %ymm4, %ymm4
vpsllvd %ymm1, %ymm4, %ymm4
vpsrlw $1, %ymm4, %ymm4
vpand %ymm2, %ymm4, %ymm4
vpmulhrsw %ymm0, %ymm4, %ymm4
vmovdqu %ymm4, \dst_off(%rdi)
.endm

decompress_d10_iter 0, 0
decompress_d10_iter 20, 32
decompress_d10_iter 40, 64
decompress_d10_iter 60, 96
decompress_d10_iter 80, 128
decompress_d10_iter 100, 160
decompress_d10_iter 120, 192
decompress_d10_iter 140, 224
decompress_d10_iter 160, 256
decompress_d10_iter 180, 288
decompress_d10_iter 200, 320
decompress_d10_iter 220, 352
decompress_d10_iter 240, 384
decompress_d10_iter 260, 416
decompress_d10_iter 280, 448
decompress_d10_iter 300, 480

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == \
          3) */
