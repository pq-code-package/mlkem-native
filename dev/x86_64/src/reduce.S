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
 *
 * Changes:
 * - Add call to csub in reduce128_avx to produce outputs
 *   in [0,1,...,q-1] rather than [0,1,...,q], matching the
 *   semantics of mlk_poly_reduce(),
 * - Use a macro instead of a local function call.
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "consts.h"
#include "fq.inc"

.macro reduce_128_coefficients offset
vmovdqa (\offset +   0)(%rdi), %ymm2
vmovdqa (\offset +  32)(%rdi), %ymm3
vmovdqa (\offset +  64)(%rdi), %ymm4
vmovdqa (\offset +  96)(%rdi), %ymm5
vmovdqa (\offset + 128)(%rdi), %ymm6
vmovdqa (\offset + 160)(%rdi), %ymm7
vmovdqa (\offset + 192)(%rdi), %ymm8
vmovdqa (\offset + 224)(%rdi), %ymm9

red16 2
red16 3
red16 4
red16 5
red16 6
red16 7
red16 8
red16 9

csubq 2
csubq 3
csubq 4
csubq 5
csubq 6
csubq 7
csubq 8
csubq 9

vmovdqa	%ymm2, (\offset +   0)(%rdi)
vmovdqa	%ymm3, (\offset +  32)(%rdi)
vmovdqa	%ymm4, (\offset +  64)(%rdi)
vmovdqa	%ymm5, (\offset +  96)(%rdi)
vmovdqa	%ymm6, (\offset + 128)(%rdi)
vmovdqa	%ymm7, (\offset + 160)(%rdi)
vmovdqa	%ymm8, (\offset + 192)(%rdi)
vmovdqa	%ymm9, (\offset + 224)(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(reduce_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(reduce_avx2)

// Broadcast 3329 (0x0D01) to all elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast 20159 (0x4EBF) to all elements of ymm1
movl $0x4ebf4ebf, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

reduce_128_coefficients 0
reduce_128_coefficients 128*2

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
