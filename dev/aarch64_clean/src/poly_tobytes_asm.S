/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

.macro ld2_wrap a, ptr
        ldr q_tmp0, [\ptr\()], #32
        ldr q_tmp1, [\ptr\(), #-16]
        uzp1 \a\()0.8h, tmp0.8h, tmp1.8h
        uzp2 \a\()1.8h, tmp0.8h, tmp1.8h
.endm

/********************************************
 *         mlk_poly_tobytes()               *
 ********************************************/

        data0  .req v0
        data1  .req v1
        out0   .req v2
        out1   .req v3
        out2   .req v4
        tmp0   .req v5
        tmp1   .req v6
        q_tmp0 .req q5
        q_tmp1 .req q6

        dst   .req x0
        src   .req x1
        count .req x2

        .text
        .global MLK_ASM_NAMESPACE(poly_tobytes_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_tobytes_asm)

        mov count, #16
poly_tobytes_asm_asm_loop_start:
        ld2_wrap data, src

        // r[3 * i + 0] = (t0 >> 0);
        xtn out0.8b, data0.8h

        // r[3 * i + 1] = (t0 >> 8);
        shrn out1.8b, data0.8h, #8
        xtn tmp0.8b, data1.8h
        // r[3 * i + 1] = (t0 >> 8) | (t1 << 4);
        sli out1.8b, tmp0.8b, #4

        // r[3 * i + 2] = (t1 >> 4);
        shrn out2.8b, data1.8h, #4

        st3 {out0.8b, out1.8b, out2.8b}, [dst], #24

        subs count, count, #1
        cbnz count, poly_tobytes_asm_asm_loop_start
        ret

        .unreq data0
        .unreq data1
        .unreq out0
        .unreq out1
        .unreq out2
        .unreq tmp0
        .unreq tmp1
        .unreq q_tmp0
        .unreq q_tmp1
        .unreq dst
        .unreq src
        .unreq count

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
