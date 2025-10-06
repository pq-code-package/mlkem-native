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
 * Implementation from Kyber reference repository @[REF_AVX2]
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

.macro tomont_128_coefficients offset
#load
vmovdqa	(\offset +  0)(%rdi), %ymm3
vmovdqa	(\offset + 32)(%rdi), %ymm4
vmovdqa	(\offset + 64)(%rdi), %ymm5
vmovdqa	(\offset + 96)(%rdi), %ymm6
vmovdqa	(\offset +128)(%rdi), %ymm7
vmovdqa	(\offset +160)(%rdi), %ymm8
vmovdqa	(\offset +192)(%rdi), %ymm9
vmovdqa	(\offset +224)(%rdi), %ymm10

fqmulprecomp	1,2,3,11
fqmulprecomp	1,2,4,12
fqmulprecomp	1,2,5,13
fqmulprecomp	1,2,6,14
fqmulprecomp	1,2,7,15
fqmulprecomp	1,2,8,11
fqmulprecomp	1,2,9,12
fqmulprecomp	1,2,10,13

#store
vmovdqa	%ymm3,  (\offset +  0)(%rdi)
vmovdqa	%ymm4,  (\offset + 32)(%rdi)
vmovdqa	%ymm5,  (\offset + 64)(%rdi)
vmovdqa	%ymm6,  (\offset + 96)(%rdi)
vmovdqa	%ymm7,  (\offset +128)(%rdi)
vmovdqa	%ymm8,  (\offset +160)(%rdi)
vmovdqa	%ymm9,  (\offset +192)(%rdi)
vmovdqa	%ymm10, (\offset +224)(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(tomont_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(tomont_avx2)

// Broadcast 3329 (0x0D01) to all elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

// Broadcast 20553 (0x5049) to all elements of ymm1
movl $0x50495049, %eax
vmovd %eax, %xmm1
vpbroadcastd %xmm1, %ymm1

// Broadcast 1353 (0x0549) to all elements of ymm2
movl $0x05490549, %eax
vmovd %eax, %xmm2
vpbroadcastd %xmm2, %ymm2

tomont_128_coefficients 0
tomont_128_coefficients 2*128

ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
