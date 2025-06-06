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
 * The main difference is the use of a mulcache.
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "consts.h"

/* Polynomials to be multiplied are denoted a+bX (rsi arg) and c+dX (rdx arg).
 * The mulcache for c + dX (that is, the precomputed values of d * zeta)
 * is passed in rcx. */
.macro schoolbook off
vmovdqa   MLK_AVX2_BACKEND_DATA_OFFSET_16XQINV*2(%r8),%ymm0
vmovdqa   (64*\off+ 0)*2(%rsi),%ymm1    /* a0        */
vmovdqa   (64*\off+16)*2(%rsi),%ymm2    /* b0        */
vmovdqa   (64*\off+32)*2(%rsi),%ymm3    /* a1        */
vmovdqa   (64*\off+48)*2(%rsi),%ymm4    /* b1        */

/* Prepare Montgomery twists */
vpmullw   %ymm0,%ymm1,%ymm9             /* a0.lo     */
vpmullw   %ymm0,%ymm2,%ymm10            /* b0.lo     */
vpmullw   %ymm0,%ymm3,%ymm11            /* a1.lo     */
vpmullw   %ymm0,%ymm4,%ymm12            /* b1.lo     */

vmovdqa   (64*\off+ 0)*2(%rdx),%ymm5    /* c0        */
vmovdqa   (64*\off+16)*2(%rdx),%ymm6    /* d0        */

/* Compute high-parts of monomials in (a0+b0*X)*(c0+d0*X) */

vpmulhw   %ymm5,%ymm1,%ymm13            /* a0c0.hi   */
vpmulhw   %ymm6,%ymm1,%ymm1             /* a0d0.hi   */
vpmulhw   %ymm5,%ymm2,%ymm14            /* b0c0.hi   */

vmovdqa   (64*\off+32)*2(%rdx),%ymm7    /* c1        */
vmovdqa   (64*\off+48)*2(%rdx),%ymm8    /* d1        */

/* Compute high-parts of monomials in (a1+b1*X)*(c1+d1*X).
 * Don't yet accumulate nor reduce X^2 */

vpmulhw   %ymm7,%ymm3,%ymm15            /* a1c1.hi   */
vpmulhw   %ymm8,%ymm3,%ymm3             /* a1d1.hi   */
vpmulhw   %ymm7,%ymm4,%ymm0             /* b1c1.hi   */

vmovdqa   %ymm13,(%rsp)

/* Compute low-parts of monomials in (a0+b0*X)*(c0+d0*X),
 * using Montgomery twists calculated before */

vpmullw   %ymm5,%ymm9,%ymm13            /* a0c0.lo   */
vpmullw   %ymm6,%ymm9,%ymm9             /* a0d0.lo   */
vpmullw   %ymm5,%ymm10,%ymm5            /* b0c0.lo   */

/* Compute low-parts of monomials in (a1+b1*X)*(c1+d1*X),
 * using Montgomery twists calculated before */

vpmullw   %ymm7,%ymm11,%ymm6            /* a1c1.lo   */
vpmullw   %ymm8,%ymm11,%ymm11           /* a1d1.lo   */
vpmullw   %ymm7,%ymm12,%ymm7            /* b1c1.lo   */

/* Use cached (d * zeta) to compute the high part of (b*d) terms */

vmovdqa   (32*\off+ 0)*2(%rcx),%ymm8    /* d0z       */
vpmulhw   %ymm8,%ymm2,%ymm2             /* b0d0z.hi  */
vpmullw   %ymm8,%ymm10,%ymm10           /* b0d0z.lo  */
vmovdqa   (32*\off+16)*2(%rcx),%ymm8    /* -d1z      */
vpmulhw   %ymm8,%ymm4,%ymm4             /* -b1d1z.hi */
vpmullw   %ymm8,%ymm12,%ymm12           /* -b1d1z.lo */

/* Compute 2nd high multiplication in Montgomery multiplication */

vmovdqa   MLK_AVX2_BACKEND_DATA_OFFSET_16XQ*2(%r8),%ymm8
vpmulhw   %ymm8,%ymm13,%ymm13           /* (a0c0.lo   * Q).hi */
vpmulhw   %ymm8,%ymm9,%ymm9             /* (a0d0.lo   * Q).hi */
vpmulhw   %ymm8,%ymm5,%ymm5             /* (b0c0.lo   * Q).hi */
vpmulhw   %ymm8,%ymm10,%ymm10           /* (b0d0z.lo  * Q).hi */
vpmulhw   %ymm8,%ymm6,%ymm6             /* (a1c1.lo   * Q).hi */
vpmulhw   %ymm8,%ymm11,%ymm11           /* (a1d1.lo   * Q).hi */
vpmulhw   %ymm8,%ymm7,%ymm7             /* (b1c1.lo   * Q).hi */
vpmulhw   %ymm8,%ymm12,%ymm12           /* (-b1d1z.lo * Q).hi */

/* Finish Montgomery multiplications */

vpsubw    (%rsp),%ymm13,%ymm13          /* -a0c0        */
vpsubw    %ymm9,%ymm1,%ymm9             /*  a0d0        */
vpsubw    %ymm5,%ymm14,%ymm5            /*  b0c0        */
vpsubw    %ymm10,%ymm2,%ymm10           /*  b0d0z       */

vpsubw    %ymm6,%ymm15,%ymm6            /*  a1c1        */
vpsubw    %ymm11,%ymm3,%ymm11           /*  a1d1        */
vpsubw    %ymm7,%ymm0,%ymm7             /*  b1c1        */
vpsubw    %ymm12,%ymm4,%ymm12           /* -b1d1z       */

vpaddw    %ymm5,%ymm9,%ymm9             /* a0d0 + b0c0  */
vpaddw    %ymm7,%ymm11,%ymm11           /* a1d1 + b1c1  */
vpsubw    %ymm13,%ymm10,%ymm13          /* a0c0 + b0d0z */
vpsubw    %ymm12,%ymm6,%ymm6            /* a1c1 + b1d1z */

/* Bounds: Since we are multiplying with signed canonical twiddles,
 * each Montgomery multiplication has absolute value < q,
 * and hence the coefficients of the output have absolute value < 2q. */

vmovdqa   %ymm13,(64*\off+ 0)*2(%rdi)
vmovdqa   %ymm9,(64*\off+16)*2(%rdi)
vmovdqa   %ymm6,(64*\off+32)*2(%rdi)
vmovdqa   %ymm11,(64*\off+48)*2(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(basemul_avx2)
.balign 4
MLK_ASM_FN_SYMBOL(basemul_avx2)
mov   %rsp,%r11
and   $-32,%rsp
sub   $32,%rsp

schoolbook  0
schoolbook  1
schoolbook  2
schoolbook  3

mov   %r11,%rsp
ret

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
