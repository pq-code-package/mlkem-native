/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "consts.h"

.macro mulcache_compute_iter i
vmovdqa (64*\i+16)*2(%rsi), %ymm2
vmovdqa (64*\i+48)*2(%rsi), %ymm3
vmovdqa (MLK_AVX2_BACKEND_DATA_OFFSET_MULCACHE_TWIDDLES + 16*\i)*2(%rdx), %ymm4
vmovdqa (MLK_AVX2_BACKEND_DATA_OFFSET_MULCACHE_TWIDDLES + 64 + 16*\i)*2(%rdx), %ymm1

vpmullw %ymm2, %ymm1, %ymm5
vpmullw %ymm3, %ymm1, %ymm6

vpmulhw %ymm2, %ymm4, %ymm7
vpmulhw %ymm3, %ymm4, %ymm8
vpmulhw %ymm5, %ymm0, %ymm9
vpmulhw %ymm6, %ymm0, %ymm10

vpsubw %ymm9, %ymm7, %ymm7
vpsubw %ymm10, %ymm8, %ymm8

vmovdqa %ymm7, (32*\i)*2(%rdi)
vmovdqa %ymm8, (32*\i+16)*2(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(poly_mulcache_compute_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(poly_mulcache_compute_avx2)
.cfi_startproc
vmovdqa MLK_AVX2_BACKEND_DATA_OFFSET_16XQ*2(%rdx),%ymm0

mulcache_compute_iter 0
mulcache_compute_iter 1
mulcache_compute_iter 2
mulcache_compute_iter 3

ret
.cfi_endproc

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
