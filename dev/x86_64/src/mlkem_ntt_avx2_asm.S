/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [AVX2_NTT]
 *   Faster AVX2 optimized NTT multiplication for Ring-LWE lattice cryptography.
 *   Gregor Seiler
 *   https://eprint.iacr.org/2018/039
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
 * The core ideas behind the implementation are described in @[AVX2_NTT].
 */

#include "../../../common.h"
#if defined(MLK_SYS_X86_64_AVX2) && \
    defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/*yaml
  Name: ntt_avx2_asm
  Description: x86_64 AVX2 forward NTT
  Signature: void mlk_ntt_avx2_asm(int16_t *r, const int16_t *qdata)
  ABI:
    Architecture: x86_64
    CallingConvention: SysV
    Features: [AVX2]
    rdi:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t *r
      description: Input/output polynomial (256 x int16_t)
    rsi:
      type: buffer
      size_bytes: 1248
      permissions: read-only
      c_parameter: const int16_t *qdata
      description: Precomputed constants (624 x int16_t)
*/

/* simpasm: header-end */

#include "consts.h"
#include "shuffle.inc"

/*
 * Note on operand order: if a commutative VEX instruction such as vpaddw
 * has one source register in ymm8-15 and the other in ymm0-7, the one in
 * ymm8-15 comes second. Only then do all assemblers emit the same bytes:
 * clang's assembler would swap the operands itself to use the 2-byte VEX
 * prefix, while GNU as keeps the order. The HOL Light proofs are about
 * these bytes. Where the registers are macro parameters, .if chooses.
 */

/* Compute steps 1,2 / 3 of Montgomery multiplication */
.macro mul rh0, rh1, rh2, rh3, zl0=15, zl1=15, zh0=2, zh1=2
.if \zl0 >= 8 && \rh0 < 8 /* see the note on operand order */
vpmullw %ymm\rh0,%ymm\zl0,%ymm12
.else
vpmullw %ymm\zl0,%ymm\rh0,%ymm12
.endif
.if \zl0 >= 8 && \rh1 < 8 /* see the note on operand order */
vpmullw %ymm\rh1,%ymm\zl0,%ymm13
.else
vpmullw %ymm\zl0,%ymm\rh1,%ymm13
.endif

.if \zl1 >= 8 && \rh2 < 8 /* see the note on operand order */
vpmullw %ymm\rh2,%ymm\zl1,%ymm14
.else
vpmullw %ymm\zl1,%ymm\rh2,%ymm14
.endif
.if \zl1 >= 8 && \rh3 < 8 /* see the note on operand order */
vpmullw %ymm\rh3,%ymm\zl1,%ymm15
.else
vpmullw %ymm\zl1,%ymm\rh3,%ymm15
.endif

.if \zh0 >= 8 && \rh0 < 8 /* see the note on operand order */
vpmulhw %ymm\rh0,%ymm\zh0,%ymm\rh0
.else
vpmulhw %ymm\zh0,%ymm\rh0,%ymm\rh0
.endif
.if \zh0 >= 8 && \rh1 < 8 /* see the note on operand order */
vpmulhw %ymm\rh1,%ymm\zh0,%ymm\rh1
.else
vpmulhw %ymm\zh0,%ymm\rh1,%ymm\rh1
.endif

.if \zh1 >= 8 && \rh2 < 8 /* see the note on operand order */
vpmulhw %ymm\rh2,%ymm\zh1,%ymm\rh2
.else
vpmulhw %ymm\zh1,%ymm\rh2,%ymm\rh2
.endif
.if \zh1 >= 8 && \rh3 < 8 /* see the note on operand order */
vpmulhw %ymm\rh3,%ymm\zh1,%ymm\rh3
.else
vpmulhw %ymm\zh1,%ymm\rh3,%ymm\rh3
.endif
.endm

/* Compute step 3 / 3 of Montgomery multiplication */
/* Multiply-high is signed; outputs are bound by 2^15 * q in abs value */
.macro reduce
vpmulhw %ymm0,%ymm12,%ymm12
vpmulhw %ymm0,%ymm13,%ymm13

vpmulhw %ymm0,%ymm14,%ymm14
vpmulhw %ymm0,%ymm15,%ymm15
.endm

/* Finish Montgomery multiplication and compute add/sub steps in NTT butterfly
 *
 * At this point, the two high-products of 4 ongoing Montgomery multiplications
 * are in %ymm{12,13,14,15} and %ymm{rh{0,1,2,3}}, respectively.
 * The NTT coefficients that the results of the Montgomery multiplications should
 * be add/sub-ed with, are in %ymm{rl{0,1,2,3}}.
 *
 * What's interesting, here, is that rather than completing the Montgomery
 * multiplications by computing `%ymm{12+i} + %ymm{rh{i}}`, and then add/sub'ing
 * the result into %ymm{rl{0,1,2,3}}, we add/sub both `%ymm{12+i}` and
 * %ymm{rh{i}} to %ymm{rl{0,1,2,3}}, and then add the results.
 *
 * Functionally, though, this is still a signed Montgomery multiplication
 * followed by an add/sub.
 *
 * Since the result of the Montgomery multiplication is bounded
 * by q in absolute value, the coefficients overall grow by not
 * more than q in absolute value per layer. */
.macro update rln, rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3
.if \rh0 >= 8 && \rl0 < 8 /* see the note on operand order */
vpaddw %ymm\rl0,%ymm\rh0,%ymm\rln /* rln = rl0 + rh0 */
.else
vpaddw %ymm\rh0,%ymm\rl0,%ymm\rln /* rln = rl0 + rh0 */
.endif
vpsubw %ymm\rh0,%ymm\rl0,%ymm\rh0 /* rh0 = rl0 - rh0 */
.if \rh1 >= 8 && \rl1 < 8 /* see the note on operand order */
vpaddw %ymm\rl1,%ymm\rh1,%ymm\rl0 /* rl0 = rl1 + rh1 */
.else
vpaddw %ymm\rh1,%ymm\rl1,%ymm\rl0 /* rl0 = rl1 + rh1 */
.endif
vpsubw %ymm\rh1,%ymm\rl1,%ymm\rh1 /* rh1 = rl1 - rh1 */
.if \rh2 >= 8 && \rl2 < 8 /* see the note on operand order */
vpaddw %ymm\rl2,%ymm\rh2,%ymm\rl1 /* rl1 = rl2 + rh2 */
.else
vpaddw %ymm\rh2,%ymm\rl2,%ymm\rl1 /* rl1 = rl2 + rh2 */
.endif
vpsubw %ymm\rh2,%ymm\rl2,%ymm\rh2 /* rh2 = rl2 - rh2 */
.if \rh3 >= 8 && \rl3 < 8 /* see the note on operand order */
vpaddw %ymm\rl3,%ymm\rh3,%ymm\rl2 /* rl2 = rl3 + rh3 */
.else
vpaddw %ymm\rh3,%ymm\rl3,%ymm\rl2 /* rl2 = rl3 + rh3 */
.endif
vpsubw %ymm\rh3,%ymm\rl3,%ymm\rh3 /* rh3 = rl3 - rh3 */

vpsubw %ymm12,%ymm\rln,%ymm\rln /* rln = rh0 + rl0 - ymm12 = rl0 + (rh0 - ymm12) */
.if 12 >= 8 && \rh0 < 8 /* see the note on operand order */
vpaddw %ymm\rh0,%ymm12,%ymm\rh0 /* rh0 = rl0 - rh0 + ymm12 = rl0 - (rh0 - ymm12) */
.else
vpaddw %ymm12,%ymm\rh0,%ymm\rh0 /* rh0 = rl0 - rh0 + ymm12 = rl0 - (rh0 - ymm12) */
.endif
vpsubw %ymm13,%ymm\rl0,%ymm\rl0 /* rl0 = rl1 + rh1 - ymm13 = rl1 + (rh1 - ymm13) */
.if 13 >= 8 && \rh1 < 8 /* see the note on operand order */
vpaddw %ymm\rh1,%ymm13,%ymm\rh1 /* rh1 = rl1 - rh1 + ymm13 = rl1 - (rh1 - ymm13) */
.else
vpaddw %ymm13,%ymm\rh1,%ymm\rh1 /* rh1 = rl1 - rh1 + ymm13 = rl1 - (rh1 - ymm13) */
.endif
vpsubw %ymm14,%ymm\rl1,%ymm\rl1 /* rl1 = rh2 + rl2 - ymm14 = rl2 + (rh2 - ymm14) */
.if 14 >= 8 && \rh2 < 8 /* see the note on operand order */
vpaddw %ymm\rh2,%ymm14,%ymm\rh2 /* rh2 = rl2 - rh2 + ymm14 = rl2 - (rh2 - ymm14) */
.else
vpaddw %ymm14,%ymm\rh2,%ymm\rh2 /* rh2 = rl2 - rh2 + ymm14 = rl2 - (rh2 - ymm14) */
.endif
vpsubw %ymm15,%ymm\rl2,%ymm\rl2 /* rl2 = rh3 + rl3 - ymm15 = rl3 + (rh3 - ymm15) */
.if 15 >= 8 && \rh3 < 8 /* see the note on operand order */
vpaddw %ymm\rh3,%ymm15,%ymm\rh3 /* rh3 = rl3 - rh3 + ymm15 = rl3 - (rh3 - ymm15) */
.else
vpaddw %ymm15,%ymm\rh3,%ymm\rh3 /* rh3 = rl3 - rh3 + ymm15 = rl3 - (rh3 - ymm15) */
.endif
.endm

.macro level0 off
vpbroadcastq (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+0)*2(%rsi),%ymm15
vmovdqa  (64*\off+128)*2(%rdi),%ymm8
vmovdqa  (64*\off+144)*2(%rdi),%ymm9
vmovdqa  (64*\off+160)*2(%rdi),%ymm10
vmovdqa  (64*\off+176)*2(%rdi),%ymm11
vpbroadcastq (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+4)*2(%rsi),%ymm2

mul  8, 9, 10, 11

vmovdqa  (64*\off+  0)*2(%rdi),%ymm4
vmovdqa  (64*\off+ 16)*2(%rdi),%ymm5
vmovdqa  (64*\off+ 32)*2(%rdi),%ymm6
vmovdqa  (64*\off+ 48)*2(%rdi),%ymm7

reduce
update  3, 4, 5, 6, 7, 8, 9, 10, 11

vmovdqa %ymm3,(64*\off+  0)*2(%rdi)
vmovdqa %ymm4,(64*\off+ 16)*2(%rdi)
vmovdqa %ymm5,(64*\off+ 32)*2(%rdi)
vmovdqa %ymm6,(64*\off+ 48)*2(%rdi)
vmovdqa %ymm8,(64*\off+128)*2(%rdi)
vmovdqa %ymm9,(64*\off+144)*2(%rdi)
vmovdqa %ymm10,(64*\off+160)*2(%rdi)
vmovdqa %ymm11,(64*\off+176)*2(%rdi)
.endm

.macro levels1t6 off
/* level 1 */
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+16)*2(%rsi),%ymm15
vmovdqa  (128*\off+ 64)*2(%rdi),%ymm8
vmovdqa  (128*\off+ 80)*2(%rdi),%ymm9
vmovdqa  (128*\off+ 96)*2(%rdi),%ymm10
vmovdqa  (128*\off+112)*2(%rdi),%ymm11
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+32)*2(%rsi),%ymm2

mul  8, 9, 10, 11

vmovdqa  (128*\off+  0)*2(%rdi),%ymm4
vmovdqa   (128*\off+ 16)*2(%rdi),%ymm5
vmovdqa  (128*\off+ 32)*2(%rdi),%ymm6
vmovdqa  (128*\off+ 48)*2(%rdi),%ymm7

reduce
update  3, 4, 5, 6, 7, 8, 9, 10, 11

/* level 2 */
shuffle8 5,10,7,10
shuffle8 6,11,5,11

vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+48)*2(%rsi),%ymm15
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+64)*2(%rsi),%ymm2

mul  7, 10, 5, 11

shuffle8 3,8,6,8
shuffle8 4,9,3,9

reduce
update  4, 6, 8, 3, 9, 7, 10, 5, 11

/* level 3 */
shuffle4 8,5,9,5
shuffle4 3,11,8,11

vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+80)*2(%rsi),%ymm15
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+96)*2(%rsi),%ymm2

mul  9, 5, 8, 11

shuffle4 4,7,3,7
shuffle4 6,10,4,10

reduce
update  6, 3, 7, 4, 10, 9, 5, 8, 11

/* level 4 */
shuffle2 7,8,10,8
shuffle2 4,11,7,11

vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+112)*2(%rsi),%ymm15
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+128)*2(%rsi),%ymm2

mul  10, 8, 7, 11

shuffle2 6,9,4,9
shuffle2 3,5,6,5

reduce
update  3, 4, 9, 6, 5, 10, 8, 7, 11

/* level 5 */
shuffle1 9,7,5,7
shuffle1 6,11,9,11

vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+144)*2(%rsi),%ymm15
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+160)*2(%rsi),%ymm2

mul  5, 7, 9, 11

shuffle1 3,10,6,10
shuffle1 4,8,3,8

reduce
update  4, 6, 10, 3, 8, 5, 7, 9, 11

/* level 6 */
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+176)*2(%rsi),%ymm14
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+208)*2(%rsi),%ymm15
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+192)*2(%rsi),%ymm8
vmovdqa  (MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP+224*\off+224)*2(%rsi),%ymm2

mul  10, 3, 9, 11, 14, 15, 8, 2

reduce
update  8, 4, 6, 5, 7, 10, 3, 9, 11

vmovdqa %ymm8,(128*\off+  0)*2(%rdi)
vmovdqa %ymm4,(128*\off+ 16)*2(%rdi)
vmovdqa %ymm10,(128*\off+ 32)*2(%rdi)
vmovdqa %ymm3,(128*\off+ 48)*2(%rdi)
vmovdqa %ymm6,(128*\off+ 64)*2(%rdi)
vmovdqa %ymm5,(128*\off+ 80)*2(%rdi)
vmovdqa %ymm9,(128*\off+ 96)*2(%rdi)
vmovdqa %ymm11,(128*\off+112)*2(%rdi)
.endm

.text
.global MLK_ASM_NAMESPACE(ntt_avx2_asm)
.balign 4
MLK_ASM_FN_SYMBOL(ntt_avx2_asm)

// Broadcast 3329 (0x0D01) to all elements of ymm0
movl $0x0D010D01, %eax
vmovd %eax, %xmm0
vpbroadcastd %xmm0, %ymm0

level0  0
level0  1

levels1t6 0
levels1t6 1

/* Clear upper halves of YMM registers to avoid a performance
 * penalty when switching to SSE. */
vzeroupper
ret

/* simpasm: footer-start */
#endif /* MLK_SYS_X86_64_AVX2 && MLK_ARITH_BACKEND_X86_64_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
