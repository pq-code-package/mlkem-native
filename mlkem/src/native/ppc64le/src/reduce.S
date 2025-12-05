/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Copyright 2025- IBM Corp.
 *
 * ===================================================================================
 * Written by Danny Tsen <dtsen@us.ibm.com>
 */

/*
 * poly_reduce: Applies Barrett reduction to all coefficients of a polynomial
 *              for details of the Barrett reduction
 *
 * Arguments: *r: pointer to input/output polynomial
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include "consts.h"

# Barrett reduce constatnts
#define V20159  0
#define V_25    1
#define V_26    2
#define V_MKQ   3

.machine "any"
.text

.macro BREDUCE_4X _v0 _v1 _v2 _v3
        lxvd2x  32+v8, 0, r3
        lxvd2x  32+v12, r14, r3
        lxvd2x  32+v16, r15, r3
        lxvd2x  32+v20, r16, r3
        addi    r3, r3, 64
        vmulosh v6, v8, V20159
        vmulesh v5, v8, V20159
        vmulosh v11, v12, V20159
        vmulesh v10, v12, V20159
        vmulosh v15, v16, V20159
        vmulesh v14, v16, V20159
        vmulosh v19, v20, V20159
        vmulesh v18, v20, V20159
        xxmrglw 32+v4, 32+v5, 32+v6
        xxmrghw 32+v5, 32+v5, 32+v6
        xxmrglw 32+v9, 32+v10, 32+v11
        xxmrghw 32+v10, 32+v10, 32+v11
        xxmrglw 32+v13, 32+v14, 32+v15
        xxmrghw 32+v14, 32+v14, 32+v15
        xxmrglw 32+v17, 32+v18, 32+v19
        xxmrghw 32+v18, 32+v18, 32+v19
        vadduwm v4, v4, V_25
        vadduwm v5, v5, V_25
        vadduwm v9, v9, V_25
        vadduwm v10, v10, V_25
        vadduwm v13, v13, V_25
        vadduwm v14, v14, V_25
        vadduwm v17, v17, V_25
        vadduwm v18, v18, V_25
        vsraw   v4, v4, V_26
        vsraw   v5, v5, V_26
        vsraw   v9, v9, V_26
        vsraw   v10, v10, V_26
        vsraw   v13, v13, V_26
        vsraw   v14, v14, V_26
        vsraw   v17, v17, V_26
        vsraw   v18, v18, V_26
        vpkuwum v4, v5, v4
        vsubuhm v4, v7, v4
        vpkuwum v9, v10, v9
        vsubuhm v9, v7, v9
        vpkuwum v13, v14, v13
        vsubuhm v13, v7, v13
        vpkuwum v17, v18, v17
        vsubuhm v17, v7, v17
        vmladduhm \_v0, v4, V_MKQ, v8
        vmladduhm \_v1, v9, V_MKQ, v12
        vmladduhm \_v2, v13, V_MKQ, v16
        vmladduhm \_v3, v17, V_MKQ, v20
.endm

.macro Write_8X
        stxvd2x 32+v21, r4, r3
        stxvd2x 32+v22, r5, r3
        stxvd2x 32+v23, r6, r3
        stxvd2x 32+v24, r7, r3
        stxvd2x 32+v4, r8, r3
        stxvd2x 32+v9, r9, r3
        stxvd2x 32+v13, r10, r3
        stxvd2x 32+v17, r11, r3
.endm

/*
 * Conditional addition to get unsigned canonical representative
 */
.macro To_unsigned_16
        lxvd2x    32+v12, 0, r3
        lxvd2x    32+v13, r14, r3
        lxvd2x    32+v14, r15, r3
        lxvd2x    32+v15, r16, r3
        addi    r3, r3, 64
        vsrh    v1, v12, v10
        vsrh    v0, v13, v10
        vsrh    v3, v14, v10
        vsrh    v2, v15, v10
        vadduhm v7, v12, v11
        vadduhm v8, v13, v11
        vadduhm v5, v14, v11
        vadduhm v6, v15, v11
        vcmpequh v1, v1, v9
        vcmpequh v0, v0, v9
        vcmpequh v3, v3, v9
        vcmpequh v2, v2, v9
        xxsel   32+v1, 32+v7,32+v12, 32+v1
        xxsel   32+v0, 32+v8,32+v13, 32+v0
        xxsel   32+v3, 32+v5,32+v14, 32+v3
        xxsel   32+v2, 32+v6,32+v15, 32+v2
        stxvd2x 32+v3, r10, r3
        stxvd2x 32+v2, r11, r3
        stxvd2x 32+v1, r8, r3
        stxvd2x 32+v0, r9, r3
.endm

.align 4
.globl MLK_ASM_NAMESPACE(reduce_ppc)
MLK_ASM_FN_SYMBOL(reduce_ppc)
        stdu    r1, -224(r1)
        mflr    r0
        std     r14, 96(r1)
        std     r15, 104(r1)
        std     r16, 112(r1)
        li      r6, 128
        li      r7, 144
        li      r8, 160
        li      r9, 176
        li      r10, 192
        stxvx   32+v20, r6, r1
        stxvx   32+v21, r7, r1
        stxvx   32+v22, r8, r1
        stxvx   32+v23, r9, r1
        stxvx   32+v24, r10, r1

        vxor    v7, v7, v7

        li      r6, Q_OFFSET
        li      r7, C20159_OFFSET
        lxvx    32+V_MKQ, r6, r4
        lxvx    32+V20159, r7, r4

        vspltisw V_26, 13
        vadduwm V_26, V_26, V_26
        vspltisw v4, 1
        vsubuwm v5, V_26, v4
        vslw    V_25, v4, v5

        li      r4, -128
        li      r5, -112
        li      r6, -96
        li      r7, -80
        li      r8, -64
        li      r9, -48
        li      r10, -32
        li      r11, -16

        li      r14, 16
        li      r15, 32
        li      r16, 48

        BREDUCE_4X v21, v22, v23, v24
        BREDUCE_4X v4, v9, v13, v17
        Write_8X

        BREDUCE_4X v21, v22, v23, v24
        BREDUCE_4X v4, v9, v13, v17
        Write_8X

        BREDUCE_4X v21, v22, v23, v24
        BREDUCE_4X v4, v9, v13, v17
        Write_8X

        BREDUCE_4X v21, v22, v23, v24
        BREDUCE_4X v4, v9, v13, v17
        Write_8X

        /*
         * To unsigned canonical
         */
.align 4
        addi    r3, r3, -512
        vxor    v9, v9, v9
        vspltish v10, 15
        vmr     v11, V_MKQ

        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16

        ld      r14, 96(r1)
        ld      r15, 104(r1)
        ld      r16, 112(r1)
        li      r6, 128
        li      r7, 144
        li      r8, 160
        li      r9, 176
        li      r10, 192
        lxvx    32+v20, r6, r1
        lxvx    32+v21, r7, r1
        lxvx    32+v22, r8, r1
        lxvx    32+v23, r9, r1
        lxvx    32+v24, r10, r1
        mtlr    r0
        addi    r1, r1, 224
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V20159
#undef V_25
#undef V_26
#undef V_MKQ

#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V20159
#undef V_25
#undef V_26
#undef V_MKQ
