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

.macro nttunpack_128_coefficients offset
#load
vmovdqa	(\offset +   0)(%rdi), %ymm4
vmovdqa	(\offset +  32)(%rdi), %ymm5
vmovdqa	(\offset +  64)(%rdi), %ymm6
vmovdqa	(\offset +  96)(%rdi), %ymm7
vmovdqa	(\offset + 128)(%rdi), %ymm8
vmovdqa	(\offset + 160)(%rdi), %ymm9
vmovdqa	(\offset + 192)(%rdi), %ymm10
vmovdqa	(\offset + 224)(%rdi), %ymm11

shuffle8	4,8,3,8
shuffle8	5,9,4,9
shuffle8	6,10,5,10
shuffle8	7,11,6,11

shuffle4	3,5,7,5
shuffle4	8,10,3,10
shuffle4	4,6,8,6
shuffle4	9,11,4,11

shuffle2	7,8,9,8
shuffle2	5,6,7,6
shuffle2	3,4,5,4
shuffle2	10,11,3,11

shuffle1	9,5,10,5
shuffle1	8,4,9,4
shuffle1	7,3,8,3
shuffle1	6,11,7,11

#store
vmovdqa	%ymm10, (\offset +  0)(%rdi)
vmovdqa	%ymm5,  (\offset + 32)(%rdi)
vmovdqa	%ymm9,  (\offset + 64)(%rdi)
vmovdqa	%ymm4,  (\offset + 96)(%rdi)
vmovdqa	%ymm8,  (\offset +128)(%rdi)
vmovdqa	%ymm3,  (\offset +160)(%rdi)
vmovdqa	%ymm7,  (\offset +192)(%rdi)
vmovdqa	%ymm11, (\offset +224)(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(nttunpack_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(nttunpack_avx2)

nttunpack_128_coefficients 0
nttunpack_128_coefficients 2*128

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
