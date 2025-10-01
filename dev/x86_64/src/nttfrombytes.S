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

.macro nttfrombytes_128_coefficients offset_in offset_out
#load
vmovdqu	(\offset_in +  0)(%rsi), %ymm4
vmovdqu	(\offset_in + 32)(%rsi), %ymm5
vmovdqu	(\offset_in + 64)(%rsi), %ymm6
vmovdqu	(\offset_in + 96)(%rsi), %ymm7
vmovdqu	(\offset_in +128)(%rsi), %ymm8
vmovdqu	(\offset_in +160)(%rsi), %ymm9

shuffle8	4,7,3,7
shuffle8	5,8,4,8
shuffle8	6,9,5,9

shuffle4	3,8,6,8
shuffle4	7,5,3,5
shuffle4	4,9,7,9

shuffle2	6,5,4,5
shuffle2	8,7,6,7
shuffle2	3,9,8,9

shuffle1	4,7,10,7
shuffle1	5,8,4,8
shuffle1	6,9,5,9

#bitunpack
vpsrlw		$12,%ymm10,%ymm11
vpsllw		$4,%ymm7,%ymm12
vpor		%ymm11,%ymm12,%ymm11
vpand		%ymm0,%ymm10,%ymm10
vpand		%ymm0,%ymm11,%ymm11

vpsrlw		$8,%ymm7,%ymm12
vpsllw		$8,%ymm4,%ymm13
vpor		%ymm12,%ymm13,%ymm12
vpand		%ymm0,%ymm12,%ymm12

vpsrlw		$4,%ymm4,%ymm13
vpand		%ymm0,%ymm13,%ymm13

vpsrlw		$12,%ymm8,%ymm14
vpsllw		$4,%ymm5,%ymm15
vpor		%ymm14,%ymm15,%ymm14
vpand		%ymm0,%ymm8,%ymm8
vpand		%ymm0,%ymm14,%ymm14

vpsrlw		$8,%ymm5,%ymm15
vpsllw		$8,%ymm9,%ymm1
vpor		%ymm15,%ymm1,%ymm15
vpand		%ymm0,%ymm15,%ymm15

vpsrlw		$4,%ymm9,%ymm1
vpand		%ymm0,%ymm1,%ymm1

#store
vmovdqa	%ymm10, (\offset_out +  0)(%rdi)
vmovdqa	%ymm11, (\offset_out + 32)(%rdi)
vmovdqa	%ymm12, (\offset_out + 64)(%rdi)
vmovdqa	%ymm13, (\offset_out + 96)(%rdi)
vmovdqa	%ymm8,  (\offset_out +128)(%rdi)
vmovdqa	%ymm14, (\offset_out +160)(%rdi)
vmovdqa	%ymm15, (\offset_out +192)(%rdi)
vmovdqa	%ymm1,  (\offset_out +224)(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(nttfrombytes_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(nttfrombytes_avx2)

// Broadcast 0xFFF to all elements of ymm0
movl $0x0FFF0FFF, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

nttfrombytes_128_coefficients 0 0
nttfrombytes_128_coefficients 192 256

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
