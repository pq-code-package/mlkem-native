/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: poly_tomont_asm
  Description: Convert polynomial to Montgomery domain
  Signature: void mlk_poly_tomont_asm(int16_t p[256])
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

/* Montgomery multiplication, with precomputed Montgomery twist
 * Expects modulus in consts.h[0]. */
.macro mulmod dst, src, const, const_twisted
        sqrdmulh tmp0.8h,    \src\().8h, \const_twisted\().8h
        mul      \dst\().8h, \src\().8h, \const\().8h
        mls      \dst\().8h, tmp0.8h,    modulus.h[0]
.endm

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
        .global MLK_ASM_NAMESPACE(poly_tomont_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_tomont_asm)
        .cfi_startproc
        mov wtmp, #3329 // ML-KEM modulus
        dup modulus.8h, wtmp

        mov wtmp, #20159 // Barrett twist of 1 wrt 2^27
        dup modulus_twisted.8h, wtmp

        mov wtmp, #-1044 // 2^16 % 3329
        dup factor.8h, wtmp

        mov wtmp, #-10276 // Barrett twist of -1044 (wrt 2^16)
        dup factor_t.8h, wtmp

        mov count, #8
Lpoly_tomont_loop:

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
        cbnz count, Lpoly_tomont_loop

        ret
        .cfi_endproc

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

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
