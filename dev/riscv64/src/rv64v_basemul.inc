/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Scalar product of length-k polynomial vectors in NTT domain, using the
 * multiplication cache of b.
 *
 * Vector-length agnostic: works for any VLEN.
 *
 * In NTT domain, a polynomial is a sequence of 128 pairs (x0, x1), each
 * representing x0 + x1*X in Z_q[X]/(X^2 - zeta_i). The product of two
 * pairs is
 *
 *   c0 = a0*b0 + zeta_i*a1*b1,   c1 = a0*b1 + a1*b0.
 *
 * The multiplication cache holds zeta_i*b1 mod q for each pair of b (see
 * mlkem_poly_mulcache_compute_riscv64_asm.S). Segment loads (vlseg2e16)
 * split each polynomial into a vector of first and a vector of second
 * components, so that all arithmetic is element-wise. Per pair, the products
 * are accumulated over the k polynomials in 32 bits,
 *
 *   c0' = sum_j (a0*b0 + a1*cache),   c1' = sum_j (a0*b1 + a1*b0),
 *
 * and then Montgomery-reduced to 16 bits, giving c0' * 2^-16 and
 * c1' * 2^-16 mod q. The results are stored interleaved (vsseg2e16).
 *
 * The accumulators cannot overflow: with a in [0, 4096) and b and the cache
 * arbitrary 16-bit values, each accumulator is bounded by
 * k * 2 * 4096 * 2^15 <= 2^30 in absolute value.
 *
 * All arithmetic is at SEW=16: widening multiply-accumulates write the
 * 32-bit accumulators, and the reduction reads them with narrowing shifts.
 * Hence a single vsetvli suffices. Uses register groups of 2 (LMUL=2) for
 * 16-bit and 4 for 32-bit values. VLMAX for e16,m2 is a power of 2, so it
 * either divides 128 or exceeds it, and the VL is the same in every
 * iteration.
 */

#define out             a0
#define in_a            a1
#define in_b            a2
#define in_cache        a3
#define count           a4
#define vl              t0
#define modulus         t1
#define qinv            t2
#define stride          t3
#define cache_stride    t4
#define addr_a          t5
#define addr_b          t6
#define addr_cache      a5

/* First and second components of a and b (register groups of 2); each
 * pair must be consecutive groups for the segment loads. */
#define a0v             v8
#define a1v             v10
#define b0v             v12
#define b1v             v14
#define cachev          v16
#define tmp             v20
/* 32-bit accumulators (register groups of 4) */
#define c0w             v24
#define c1w             v28
/* Reduced results; must be consecutive groups for the segment store.
 * They reuse the registers of a, which are dead at that point. */
#define r0v             v8
#define r1v             v10

/* Montgomery reduction of the 32-bit accumulator \w to 16 bits:
 * \r = \w * 2^-16 mod q, using \t as temporary.
 * With t = lo16(w) * q^-1 mod 2^16, w - t*q is divisible by 2^16, and
 * (w - t*q) / 2^16 = hi16(w) - hi16(t*q). */
.macro mont_reduce_wide r, w, t
        vnsrl.wi    \t, \w, 0
        vnsra.wi    \r, \w, 16
        vmul.vx     \t, \t, qinv
        vmulh.vx    \t, \t, modulus
        vsub.vv     \r, \r, \t
.endm

/* Multiply-accumulate the j-th polynomial pair of a and b into c0w, c1w.
 * If \first is 1, initialize the accumulators instead. */
.macro basemul_poly j, first
        addi        addr_a, in_a, (2 * MLKEM_N * \j)
        addi        addr_b, in_b, (2 * MLKEM_N * \j)
        addi        addr_cache, in_cache, (MLKEM_N * \j)
        vlseg2e16.v a0v, (addr_a)
        vlseg2e16.v b0v, (addr_b)
        vle16.v     cachev, (addr_cache)

.if \first
        vwmul.vv    c0w, a0v, b0v
        vwmul.vv    c1w, a0v, b1v
.else
        vwmacc.vv   c0w, a0v, b0v
        vwmacc.vv   c1w, a0v, b1v
.endif
        vwmacc.vv   c0w, a1v, cachev
        vwmacc.vv   c1w, a1v, b0v
.endm

.macro polyvec_basemul k, loop
        li          modulus, MLKEM_Q
        li          qinv, -3327           // q^-1 mod 2^16 (signed)
        li          count, (MLKEM_N / 2)  // number of pairs

        vsetvli     vl, count, e16, m2, ta, ma
        slli        stride, vl, 2         // bytes per VL pairs
        slli        cache_stride, vl, 1   // bytes per VL cache entries

\loop:
        basemul_poly 0, 1
        basemul_poly 1, 0
.if \k > 2
        basemul_poly 2, 0
.endif
.if \k > 3
        basemul_poly 3, 0
.endif

        mont_reduce_wide r0v, c0w, tmp
        mont_reduce_wide r1v, c1w, tmp
        vsseg2e16.v r0v, (out)

        add         out, out, stride
        add         in_a, in_a, stride
        add         in_b, in_b, stride
        add         in_cache, in_cache, cache_stride
        sub         count, count, vl
        bnez        count, \loop
.endm
