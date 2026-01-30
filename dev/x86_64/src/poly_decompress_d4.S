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
 * Name:        mlk_poly_decompress_d4_avx2
 *
 * Description: Decompression of a polynomial from 4 bits per coefficient.
 *
 * Arguments:   - int16_t *r:       pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D4)
 *              - const int8_t *data: pointer to shufbidx constant
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)
/* simpasm: header-end */

.text
.global MLK_ASM_NAMESPACE(poly_decompress_d4_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d4_avx2)

// Broadcast q = 3329 (0x0D01) to all 16-bit elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast mask = 0x00F0000F to all 32-bit elements of ymm1
movl $0x00F0000F, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

// Broadcast shift = (128 << 16) + 2048 = 0x00800800 to all 32-bit elements
movl $0x00800800, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

// Load shufbidx constant from 3rd argument
vmovdqa (%rdx), %ymm3

// Fully unrolled: 16 iterations for 256 coefficients / 16 per iteration
// Macro for one iteration with explicit offsets
.macro decompress_d4_iter src_off, dst_off
vmovq \src_off(%rsi), %xmm4
vinserti128 $1, %xmm4, %ymm4, %ymm4
vpshufb %ymm3, %ymm4, %ymm4
vpand %ymm1, %ymm4, %ymm4
vpmullw %ymm2, %ymm4, %ymm4
vpmulhrsw %ymm0, %ymm4, %ymm4
vmovdqu %ymm4, \dst_off(%rdi)
.endm

decompress_d4_iter 0, 0
decompress_d4_iter 8, 32
decompress_d4_iter 16, 64
decompress_d4_iter 24, 96
decompress_d4_iter 32, 128
decompress_d4_iter 40, 160
decompress_d4_iter 48, 192
decompress_d4_iter 56, 224
decompress_d4_iter 64, 256
decompress_d4_iter 72, 288
decompress_d4_iter 80, 320
decompress_d4_iter 88, 352
decompress_d4_iter 96, 384
decompress_d4_iter 104, 416
decompress_d4_iter 112, 448
decompress_d4_iter 120, 480

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == \
          3) */
