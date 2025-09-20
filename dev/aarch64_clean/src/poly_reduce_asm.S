/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: poly_reduce_asm
  Description: Barrett reduction of polynomial coefficients
  Signature: void mlk_poly_reduce_asm(int16_t p[256])
  ABI:
    x0:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t p[256]
      description: Input/output polynomial
  Stack:
    bytes: 0
*/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

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
        .global MLK_ASM_NAMESPACE(poly_reduce_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_reduce_asm)

        mov wtmp, #3329 // ML-KEM modulus
        dup modulus.8h, wtmp

        mov wtmp, #20159 // Barrett twist of 1 wrt 2^27
        dup modulus_twisted.8h, wtmp

        mov count, #8
poly_reduce_loop_start:
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
        cbnz count, poly_reduce_loop_start

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

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
