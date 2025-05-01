/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

/* Montgomery multiplication, with precomputed Montgomery twist
 * Expects modulus in consts.h[0]. */
.macro mulmod dst, src, const, const_twisted
        sqrdmulh tmp0.8h,    \src\().8h, \const_twisted\().8h
        mul      \dst\().8h, \src\().8h, \const\().8h
        mls      \dst\().8h, tmp0.8h,    modulus.h[0]
.endm

/********************************************
 *      mlk_poly_mulcache_compute()         *
 ********************************************/

        cache_ptr         .req x0
        data_ptr          .req x1
        zeta_ptr          .req x2
        zeta_twisted_ptr  .req x3
        count             .req x4
        wtmp              .req w5

        data_odd          .req v0
        zeta              .req v1
        q_zeta            .req q1
        zeta_twisted      .req v2
        q_zeta_twisted    .req q2

        tmp0              .req v3
        q_tmp0            .req q3
        tmp1              .req v4
        q_tmp1            .req q4
        dst               .req v5
        q_dst             .req q5

        modulus           .req v6
        modulus_twisted   .req v7

        .global MLK_ASM_NAMESPACE(poly_mulcache_compute_asm)
        .text
        .balign 4
MLK_ASM_FN_SYMBOL(poly_mulcache_compute_asm)
        mov wtmp, #3329
        dup modulus.8h, wtmp

        mov wtmp, #20159
        dup modulus_twisted.8h, wtmp

        mov count, #16
mulcache_compute_loop_start:
        ldr q_tmp0, [data_ptr], #32
        ldr q_tmp1, [data_ptr, #-16]
        ldr q_zeta, [zeta_ptr], #16
        ldr q_zeta_twisted, [zeta_twisted_ptr], #16

        // The mulcache of a polynomial a + b*X in Fq[X^2-zeta] is b*zeta;
        // Since tmp0 || tmp1 represents multiple such polynomails as
        // (a0,b0,a1,b1,...), extract only the odd elements.
        uzp2 data_odd.8h, tmp0.8h, tmp1.8h
        mulmod dst, data_odd, zeta, zeta_twisted

        str q_dst, [cache_ptr], #16

        subs count, count, #1
        cbnz count, mulcache_compute_loop_start

        ret

        .unreq cache_ptr
        .unreq data_ptr
        .unreq zeta_ptr
        .unreq zeta_twisted_ptr
        .unreq count
        .unreq wtmp

        .unreq data_odd
        .unreq zeta
        .unreq q_zeta
        .unreq zeta_twisted
        .unreq q_zeta_twisted

        .unreq tmp0
        .unreq q_tmp0
        .unreq tmp1
        .unreq q_tmp1
        .unreq dst
        .unreq q_dst

        .unreq modulus
        .unreq modulus_twisted

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
