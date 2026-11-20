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
 *
 * - [ShortLimb]
 *   Short-Limb Modular Multiplication Techniques: Barrett, Montgomery,
 *   Plantard, and the Explicit CRT
 *   Bo-Yin Yang
 *   https://eprint.iacr.org/2026/1743
 */

/*
 * This file is derived from the public domain
 * AVX2 Kyber implementation @[REF_AVX2].
 */

/*
 * Note on operand order: if a commutative VEX instruction such as vpaddw
 * has one source register in ymm8-15 and the other in ymm0-7, the one in
 * ymm8-15 comes second. Only then do all assemblers emit the same bytes:
 * clang's assembler would swap the operands itself to use the 2-byte VEX
 * prefix, while GNU as keeps the order. The HOL Light proofs are about
 * these bytes. Where the registers are macro parameters, .if chooses.
 */


.macro red16 r, rs=0, x=12
vpmulhw %ymm1,%ymm\r,%ymm\x
.if \rs
vpmulhrsw %ymm\rs,%ymm\x,%ymm\x
.else
vpsraw $10,%ymm\x,%ymm\x
.endif
vpmullw %ymm0,%ymm\x,%ymm\x
vpsubw %ymm\x,%ymm\r,%ymm\r
.endm

.macro csubq r, x=12
vpsubw %ymm0,%ymm\r,%ymm\r
vpsraw $15,%ymm\r,%ymm\x
vpand %ymm0,%ymm\x,%ymm\x
.if \x >= 8 && \r < 8 /* see the note on operand order */
vpaddw %ymm\r,%ymm\x,%ymm\r
.else
vpaddw %ymm\x,%ymm\r,%ymm\r
.endif
.endm

.macro caddq r, x=12
vpsraw $15,%ymm\r,%ymm\x
vpand %ymm0,%ymm\x,%ymm\x
.if \x >= 8 && \r < 8 /* see the note on operand order */
vpaddw %ymm\r,%ymm\x,%ymm\r
.else
vpaddw %ymm\x,%ymm\r,%ymm\r
.endif
.endm

/* Multiplication of a signed 16-bit r by a constant w modulo q, giving the
 * canonical representative in [0, q-1], using the AVX2 sequence of
 * @[ShortLimb, Remark 5.9]. L and H are the signed 16-bit halves of
 * W = ((-2^32 * w) mod q) * q^-1 mod 2^32, and the bias s must satisfy
 * 2 <= s and q * (s + 1) <= 2^16.
 * Expects ymm0 = q, ymm1 = L, ymm2 = H, ymm3 = s. */
.macro plantard_red16 r, x=12
vpmulhw %ymm1,%ymm\r,%ymm\x
vpmullw %ymm2,%ymm\r,%ymm\r
.if \x >= 8 && \r < 8 /* see the note on operand order */
vpaddw %ymm\r,%ymm\x,%ymm\r
.else
vpaddw %ymm\x,%ymm\r,%ymm\r
.endif
vpaddw %ymm3,%ymm\r,%ymm\r
vpmulhuw %ymm0,%ymm\r,%ymm\r
.endm

/* Montgomery multiplication between b and ah,
 * with Montgomery twist of ah in al. */
.macro fqmulprecomp al, ah, b, x=12
.if \al >= 8 && \b < 8 /* see the note on operand order */
vpmullw %ymm\b,%ymm\al,%ymm\x
.else
vpmullw %ymm\al,%ymm\b,%ymm\x
.endif
.if \ah >= 8 && \b < 8 /* see the note on operand order */
vpmulhw %ymm\b,%ymm\ah,%ymm\b
.else
vpmulhw %ymm\ah,%ymm\b,%ymm\b
.endif
vpmulhw %ymm0,%ymm\x,%ymm\x
vpsubw %ymm\x,%ymm\b,%ymm\b
.endm
