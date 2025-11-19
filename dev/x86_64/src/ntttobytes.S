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

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "consts.h"
#include "fq.inc"
#include "shuffle.inc"

.macro ntttobytes_128_coefficients offset_in, offset_out
#load
vmovdqa (\offset_in +   0)(%rsi), %ymm5
vmovdqa (\offset_in +  32)(%rsi), %ymm6
vmovdqa (\offset_in +  64)(%rsi), %ymm7
vmovdqa (\offset_in +  96)(%rsi), %ymm8
vmovdqa (\offset_in + 128)(%rsi), %ymm9
vmovdqa (\offset_in + 160)(%rsi), %ymm10
vmovdqa (\offset_in + 192)(%rsi), %ymm11
vmovdqa (\offset_in + 224)(%rsi), %ymm12

#bitpack
vpsllw		$12,%ymm6,%ymm4
vpor		%ymm4,%ymm5,%ymm4

vpsrlw		$4,%ymm6,%ymm5
vpsllw		$8,%ymm7,%ymm6
vpor		%ymm5,%ymm6,%ymm5

vpsrlw		$8,%ymm7,%ymm6
vpsllw		$4,%ymm8,%ymm7
vpor		%ymm6,%ymm7,%ymm6

vpsllw		$12,%ymm10,%ymm7
vpor		%ymm7,%ymm9,%ymm7

vpsrlw		$4,%ymm10,%ymm8
vpsllw		$8,%ymm11,%ymm9
vpor		%ymm8,%ymm9,%ymm8

vpsrlw		$8,%ymm11,%ymm9
vpsllw		$4,%ymm12,%ymm10
vpor		%ymm9,%ymm10,%ymm9

shuffle1	4,5,3,5
shuffle1	6,7,4,7
shuffle1	8,9,6,9

shuffle2	3,4,8,4
shuffle2	6,5,3,5
shuffle2	7,9,6,9

shuffle4	8,3,7,3
shuffle4	6,4,8,4
shuffle4	5,9,6,9

shuffle8	7,8,5,8
shuffle8	6,3,7,3
shuffle8	4,9,6,9

#store
vmovdqu	%ymm5, (\offset_out +  0)(%rdi)
vmovdqu	%ymm7, (\offset_out + 32)(%rdi)
vmovdqu	%ymm6, (\offset_out + 64)(%rdi)
vmovdqu	%ymm8, (\offset_out + 96)(%rdi)
vmovdqu	%ymm3, (\offset_out +128)(%rdi)
vmovdqu	%ymm9, (\offset_out +160)(%rdi)
.endm


.text
.global MLK_ASM_NAMESPACE(ntttobytes_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(ntttobytes_avx2)

// Broadcast 3329 (0x0D01) to all elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

ntttobytes_128_coefficients 0, 0
ntttobytes_128_coefficients 256, 192

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
