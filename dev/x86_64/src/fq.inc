/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * This file is derived from the public domain
 * AVX2 Kyber implementation @[REF_AVX2].
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
vpaddw %ymm\x,%ymm\r,%ymm\r
.endm

.macro caddq r, x=12
vpsraw $15,%ymm\r,%ymm\x
vpand %ymm0,%ymm\x,%ymm\x
vpaddw %ymm\x,%ymm\r,%ymm\r
.endm

/* Modular reduction to [0, q-1] by the multiplier encoded in H, L, using
 * the AVX2 sequence suggested by Bo-Yin Yang.
 * Expects ymm0 = q, ymm1 = L, ymm2 = H, ymm3 = bias. */
.macro plantard_red16 r, x=12
vpmulhw %ymm1,%ymm\r,%ymm\x
vpmullw %ymm2,%ymm\r,%ymm\r
vpaddw %ymm\x,%ymm\r,%ymm\r
vpaddw %ymm3,%ymm\r,%ymm\r
vpmulhuw %ymm0,%ymm\r,%ymm\r
.endm

/* Montgomery multiplication between b and ah,
 * with Montgomery twist of ah in al. */
.macro fqmulprecomp al, ah, b, x=12
vpmullw %ymm\al,%ymm\b,%ymm\x
vpmulhw %ymm\ah,%ymm\b,%ymm\b
vpmulhw %ymm0,%ymm\x,%ymm\x
vpsubw %ymm\x,%ymm\b,%ymm\b
.endm
