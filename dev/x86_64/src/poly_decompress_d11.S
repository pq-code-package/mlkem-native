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
 *              - const uint8_t *data: pointer to constants
 *                                  (shufbidx[0:32], srlvdidx[32:64],
 *                                   srlvqidx[64:96], shift[96:128])
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

// Broadcast q = 3329 (0x0D01) to all 16-bit elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast mask = 32752 (0x7FF0) to all 16-bit elements of ymm1
movl $0x7FF07FF0, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

// Load constants from data pointer
// data[0:31] = shufbidx, data[32:63] = srlvdidx,
// data[64:95] = srlvqidx, data[96:127] = shift
vmovdqa (%rdx), %ymm2
vmovdqa 32(%rdx), %ymm3
vmovdqa 64(%rdx), %ymm4
vmovdqa 96(%rdx), %ymm5

// Fully unrolled: 16 iterations for 256 coefficients / 16 per iteration
// Macro for one iteration with explicit offsets
.macro decompress_d11_iter src_off, dst_off
vmovdqu \src_off(%rsi), %xmm6
vmovd \src_off+16(%rsi), %xmm7
vpinsrw $2, \src_off+20(%rsi), %xmm7, %xmm7
vinserti128 $1, %xmm7, %ymm6, %ymm6
vpermq $0x94, %ymm6, %ymm6
vpshufb %ymm2, %ymm6, %ymm6
vpsrlvd %ymm3, %ymm6, %ymm6
vpsrlvq %ymm4, %ymm6, %ymm6
vpmullw %ymm5, %ymm6, %ymm6
vpsrlw $1, %ymm6, %ymm6
vpand %ymm1, %ymm6, %ymm6
vpmulhrsw %ymm0, %ymm6, %ymm6
vmovdqu %ymm6, \dst_off(%rdi)
.endm

decompress_d11_iter 0, 0
decompress_d11_iter 22, 32
decompress_d11_iter 44, 64
decompress_d11_iter 66, 96
decompress_d11_iter 88, 128
decompress_d11_iter 110, 160
decompress_d11_iter 132, 192
decompress_d11_iter 154, 224
decompress_d11_iter 176, 256
decompress_d11_iter 198, 288
decompress_d11_iter 220, 320
decompress_d11_iter 242, 352
decompress_d11_iter 264, 384
decompress_d11_iter 286, 416
decompress_d11_iter 308, 448
decompress_d11_iter 330, 480

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
