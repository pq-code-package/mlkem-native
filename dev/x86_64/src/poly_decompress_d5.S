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
 * Name:        mlk_poly_decompress_d5_avx2
 *
 * Description: Decompression of a polynomial from 5 bits per coefficient.
 *
 * Arguments:   - int16_t *r:       pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D5)
 *              - const int8_t *data: pointer to constants (shufbidx, mask, shift)
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)
/* simpasm: header-end */

.text
.global MLK_ASM_NAMESPACE(poly_decompress_d5_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d5_avx2)

// Broadcast q = 3329 (0x0D01) to all 16-bit elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Load constants from data pointer
// data[0:31] = shufbidx, data[32:63] = mask, data[64:95] = shift
vmovdqa 0(%rdx), %ymm1
vmovdqa 32(%rdx), %ymm2
vmovdqa 64(%rdx), %ymm3

// Fully unrolled: 16 iterations for 256 coefficients / 16 per iteration
// Macro for one iteration with explicit offsets
.macro decompress_d5_iter src_off, dst_off
vmovq \src_off(%rsi), %xmm4
vpinsrw $4, \src_off+8(%rsi), %xmm4, %xmm4
vinserti128 $1, %xmm4, %ymm4, %ymm4
vpshufb %ymm1, %ymm4, %ymm4
vpand %ymm2, %ymm4, %ymm4
vpmullw %ymm3, %ymm4, %ymm4
vpmulhrsw %ymm0, %ymm4, %ymm4
vmovdqu %ymm4, \dst_off(%rdi)
.endm

decompress_d5_iter 0, 0
decompress_d5_iter 10, 32
decompress_d5_iter 20, 64
decompress_d5_iter 30, 96
decompress_d5_iter 40, 128
decompress_d5_iter 50, 160
decompress_d5_iter 60, 192
decompress_d5_iter 70, 224
decompress_d5_iter 80, 256
decompress_d5_iter 90, 288
decompress_d5_iter 100, 320
decompress_d5_iter 110, 352
decompress_d5_iter 120, 384
decompress_d5_iter 130, 416
decompress_d5_iter 140, 448
decompress_d5_iter 150, 480

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
