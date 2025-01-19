/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "../../../common.h"
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN)

/* Montgomery multiplication, with precomputed Montgomery twist
 * Expects modulus in consts.h[0]. */
.macro mulmod dst, src, const, const_twisted
        sqrdmulh tmp0.8h,    \src\().8h, \const_twisted\().8h
        mul      \dst\().8h, \src\().8h, \const\().8h
        mls      \dst\().8h, tmp0.8h,    modulus.h[0]
.endm

/**********************************
 *          poly_tomont()         *
 **********************************/

        src               .req x0
        count             .req x1
        wtmp              .req w2

        data              .req v0
        q_data            .req q0
        res               .req v1
        q_res             .req q1

        factor            .req v2
        factor_t          .req v3
        modulus           .req v4
        modulus_twisted   .req v5

        tmp0              .req v6

        .text
        .global MLKEM_ASM_NAMESPACE(poly_tomont_asm_clean)
        .balign 4
MLKEM_ASM_NAMESPACE(poly_tomont_asm_clean):

        mov wtmp, #3329 // ML-KEM modulus
        dup modulus.8h, wtmp

        mov wtmp, #20159 // Barrett twist of 1 wrt 2^27
        dup modulus_twisted.8h, wtmp

        mov wtmp, #-1044 // 2^16 % 3329
        dup factor.8h, wtmp

        mov wtmp, #-10276 // Barrett twist of -1044 (wrt 2^16)
        dup factor_t.8h, wtmp

        mov count, #8
poly_tomont_asm_loop:

        ldr q_data, [src], #64
        mulmod res, data, factor, factor_t
        str q_res, [src, #-64]

        ldr q_data, [src, #-48]
        mulmod res, data, factor, factor_t
        str q_res, [src, #-48]

        ldr q_data, [src, #-32]
        mulmod res, data, factor, factor_t
        str q_res, [src, #-32]

        ldr q_data, [src, #-16]
        mulmod res, data, factor, factor_t
        str q_res, [src, #-16]

        sub count, count, #1
        cbnz count, poly_tomont_asm_loop

        ret

        .unreq src
        .unreq count
        .unreq wtmp

        .unreq data
        .unreq q_data
        .unreq res
        .unreq q_res

        .unreq factor
        .unreq factor_t
        .unreq modulus
        .unreq modulus_twisted

        .unreq tmp0

#endif /* MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN */
