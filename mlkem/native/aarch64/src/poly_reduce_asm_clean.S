/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "../../../common.h"
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN)

/* Barrett reduction */
.macro barrett_reduce a
        sqdmulh tmp.8h,   \a\().8h, modulus_twisted.h[0]
        srshr   tmp.8h,   tmp.8h,   #11
        mls     \a\().8h, tmp.8h,   modulus.h[0]
.endm

/* Turns signed-canonical to unsigned canonical representative
 * through conditional addition of the modulus.
 *
 * Expected modulus in `modulus`. */
.macro scalar_signed_to_unsigned a
        sshr mask.8h, \a\().8h, #15
        and mask.16b, modulus.16b, mask.16b
        add \a\().8h, \a\().8h, mask.8h
.endm

/**********************************
 *          poly_reduce()         *
 **********************************/

        ptr               .req x0
        count             .req x1
        wtmp              .req w2

        data              .req v0
        q_data            .req q0

        tmp               .req v1
        mask              .req v2
        modulus           .req v3
        modulus_twisted   .req v4

        .text
        .global MLKEM_ASM_NAMESPACE(poly_reduce_asm_clean)
        .balign 4
MLKEM_ASM_NAMESPACE(poly_reduce_asm_clean):

        mov wtmp, #3329 // ML-KEM modulus
        dup modulus.8h, wtmp

        mov wtmp, #20159 // Barrett twist of 1 wrt 2^27
        dup modulus_twisted.8h, wtmp

        mov count, #8
loop_start:
        ldr q_data, [ptr], #64
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-64]

        ldr q_data, [ptr, #-48]
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-48]

        ldr q_data, [ptr, #-32]
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-32]

        ldr q_data, [ptr, #-16]
        barrett_reduce data
        scalar_signed_to_unsigned data
        str q_data, [ptr, #-16]

        subs count, count, #1
        cbnz count, loop_start

        ret

        .unreq ptr
        .unreq count
        .unreq wtmp

        .unreq data
        .unreq q_data

        .unreq tmp
        .unreq mask
        .unreq modulus
        .unreq modulus_twisted

#endif /* MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN */
