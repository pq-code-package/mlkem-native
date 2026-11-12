/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
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
