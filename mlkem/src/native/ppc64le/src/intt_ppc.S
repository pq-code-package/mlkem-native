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

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include "consts.h"

.machine "any"
.text

/* Barrett reduce constatnts */
#define V20159  0
#define V_25    1
#define V_26    2
#define V_MKQ   3

/* Montgomery reduce constatnts */
#define V_QINV  2
#define V_NMKQ  5
#define V_Z0    7
#define V_Z1    8
#define V_Z2    9
#define V_Z3    10
#define V_ZETA  10
#define V1441   10

.macro SAVE_REGS
        stdu    r1, -352(r1)
        mflr    r0
        std     r14, 56(r1)
        std     r15, 64(r1)
        std     r16, 72(r1)
        std     r17, 80(r1)
        std     r18, 88(r1)
        std     r19, 96(r1)
        std     r20, 104(r1)
        std     r21, 112(r1)
        li      r10, 128
        li      r11, 144
        li      r12, 160
        li      r14, 176
        li      r15, 192
        li      r16, 208
        stxvx   32+v20, r10, r1
        stxvx   32+v21, r11, r1
        stxvx   32+v22, r12, r1
        stxvx   32+v23, r14, r1
        stxvx   32+v24, r15, r1
        stxvx   32+v25, r16, r1
        li      r10, 224
        li      r11, 240
        li      r12, 256
        li      r14, 272
        li      r15, 288
        li      r16, 304
        stxvx   32+v26, r10, r1
        stxvx   32+v27, r11, r1
        stxvx   32+v28, r12, r1
        stxvx   32+v29, r14, r1
        stxvx   32+v30, r15, r1
        stxvx   32+v31, r16, r1
.endm

.macro RESTORE_REGS
        li      r10, 128
        li      r11, 144
        li      r12, 160
        li      r14, 176
        li      r15, 192
        li      r16, 208
        lxvx    32+v20, r10, r1
        lxvx    32+v21, r11, r1
        lxvx    32+v22, r12, r1
        lxvx    32+v23, r14, r1
        lxvx    32+v24, r15, r1
        lxvx    32+v25, r16, r1
        li      r10, 224
        li      r11, 240
        li      r12, 256
        li      r14, 272
        li      r15, 288
        li      r16, 304
        lxvx    32+v26, r10, r1
        lxvx    32+v27, r11, r1
        lxvx    32+v28, r12, r1
        lxvx    32+v29, r14, r1
        lxvx    32+v30, r15, r1
        lxvx    32+v31, r16, r1
        ld      r14, 56(r1)
        ld      r15, 64(r1)
        ld      r16, 72(r1)
        ld      r17, 80(r1)
        ld      r18, 88(r1)
        ld      r19, 96(r1)
        ld      r20, 104(r1)
        ld      r21, 112(r1)

        mtlr    r0
        addi    r1, r1, 352
.endm

/*
 * Compute final final r[j] and r[j+len]
 *  final r[j+len]: V8, V12, V16, V20
 *  final r[j]: V21, V22, V23, V24
 */
.macro Compute_4Coeffs
        /* Since the result of the Montgomery multiplication is bounded
           by q in absolute value.
           Finally to complete the final update of the results with add/sub
           r[j] = r[j] + t.
           r[j+len] = r[j] - t
         */
        vsubuhm v25, v8, v21
        vsubuhm v26, v12, v22
        vsubuhm v30, v16, v23
        vsubuhm v31, v20, v24
        vadduhm v8, v8, v21
        vadduhm v12, v12, v22
        vadduhm v16, v16, v23
        vadduhm v20, v20, v24
.endm

/*
 * Init_Coeffs_offset: initial offset setup for the coeeficient array.
 *
 * start: beginning of the offset to the coefficient array.
 * next: Next offset.
 * len: Index difference between coefficients.
 *
 * r7: len * 2, each coefficient component is 2 bytes.
 *
 * register used for offset to coefficients, r[j] and r[j+len]
 * R9: offset to r0 = j
 * R16: offset to r1 = r0 + next
 * R18: offset to r2 = r1 + next
 * R20: offset to r3 = r2 + next
 *
 * R10: offset to r'0 = r0 + len*2
 * R17: offset to r'1 = r'0 + step
 * R19: offset to r'2 = r'1 + step
 * R21: offset to r'3 = r'2 + step
 *
 */
.macro Init_Coeffs_offset start next
        li      r9, \start       /* first offset to j */
        add     r10, r7, r9        /* J + len*2 */
        addi    r16, r9, \next
        addi    r17, r10, \next
        addi    r18, r16, \next
        addi    r19, r17, \next
        addi    r20, r18, \next
        addi    r21, r19, \next
.endm

/*
 * Load coefficient vectors for r[j] (r) and r[j+len] (r'):
 *   Load coefficient in r' vectors from offset, R10, R17, R19 and R21
 *   Load coefficient in r vectors from offset, R9, R16, R18 and R20
 *
 *  r[j+len]: V8, V12, V16, V20
 *  r[j]: V21, V22, V23, V24
 */
.macro Load_4Rjp
        lxvd2x  32+v8, r3, r10     /* V8: vector r'0 */
        lxvd2x  32+v12, r3, r17    /* V12: vector for r'1 */
        lxvd2x  32+v16, r3, r19    /* V16: vector for r'2 */
        lxvd2x  32+v20, r3, r21    /* V20: vector for r'3 */

        lxvd2x  32+v21, r3, r9     /* V21: vector r0 */
        lxvd2x  32+v22, r3, r16    /* V22: vector r1 */
        lxvd2x  32+v23, r3, r18    /* V23: vector r2 */
        lxvd2x  32+v24, r3, r20    /* V24: vector r3 */
.endm

/*
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *  rjlen0, rjlen1, rjlen2, rjlen3, rjlen4, rjlen5, rjlen6, rjlen7
 */
.macro Load_4Coeffs start next
        Init_Coeffs_offset \start \next
        Load_4Rjp
        Compute_4Coeffs
.endm

/*
 * Load 2 - 2 - 2 - 2 layout
 *
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *    rj0, rj1, rjlen2, rjlen3, rj4, rj5, rjlen6, arlen7
 *    rj8, rj9, rjlen10, rjlen11, rj12, rj13, rjlen14, rjlen15
 *  Each vmrgew and vmrgow will transpose vectors as,
 *  r[j]=      rj0, rj1, rj8, rj9, rj4, rj5, rj12, rj13
 *  r[j+len]=  rjlen2, rjlen3, rjlen10, rjlen11, rjlen6, arlen7, rjlen14, rjlen15
 *
 *  r[j+len]: V8, V12, V16, V20
 *  r[j]: V21, V22, V23, V24
 *
 * In order to do the coefficient computation, zeta vector will arrange
 * in the proper order to match the multiplication.
 */
.macro Load_L24Coeffs
        lxvd2x     32+v25, 0, r5
        lxvd2x     32+v26, r10, r5
        vmrgew v8, v25, v26
        vmrgow v21, v25, v26
        lxvd2x     32+v25, r11, r5
        lxvd2x     32+v26, r12, r5
        vmrgew v12, v25, v26
        vmrgow v22, v25, v26
        lxvd2x     32+v25, r15, r5
        lxvd2x     32+v26, r16, r5
        vmrgew v16, v25, v26
        vmrgow v23, v25, v26
        lxvd2x     32+v25, r17, r5
        lxvd2x     32+v26, r18, r5
        vmrgew v20, v25, v26
        vmrgow v24, v25, v26
.endm

/*
 * Load 4 - 4 layout
 *
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *  rj0, rj1, rj2, rj3, rjlen4, rjlen5, rjlen6, rjlen7
 *  rj8, rj9, rj10, rj11, rjlen12, rjlen13, rjlen14, rjlen15
 *
 *  Each xxpermdi will transpose vectors as,
 *  rjlen4, rjlen5, rjlen6, rjlen7, rjlen12, rjlen13, rjlen14, rjlen15
 *  rj0, rj1, rj2, rj3, rj8, rj9, rj10, rj11
 *
 * In order to do the coefficients computation, zeta vector will arrange
 * in the proper order to match the multiplication.
 */
.macro Load_L44Coeffs
        lxvd2x     vs10, 0, r5
        lxvd2x     vs11, r10, r5
        xxpermdi 32+v8, vs11, vs10, 3
        xxpermdi 32+v21, vs11, vs10, 0
        lxvd2x     vs10, r11, r5
        lxvd2x     vs11, r12, r5
        xxpermdi 32+v12, vs11, vs10, 3
        xxpermdi 32+v22, vs11, vs10, 0
        lxvd2x     vs10, r15, r5
        lxvd2x     vs11, r16, r5
        xxpermdi 32+v16, vs11, vs10, 3
        xxpermdi 32+v23, vs11, vs10, 0
        lxvd2x     vs10, r17, r5
        lxvd2x     vs11, r18, r5
        xxpermdi 32+v20, vs11, vs10, 3
        xxpermdi 32+v24, vs11, vs10, 0
.endm

.macro BREDUCE_4X _v0 _v1 _v2 _v3
        /* Restore constant vectors
           V_MKQ, V_25 and V_26 */
        vxor    v7, v7, v7
        xxlor   32+v3, vs6, vs6
        xxlor   32+v1, vs7, vs7
        xxlor   32+v2, vs8, vs8
        /* Multify Odd/Even signed halfword;
           Results word bound by 2^32 in abs value. */
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
        /* Right shift and pack lower halfword,
           results bond to 2^16 in abs value */
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
        /* Modulo multify-Low unsigned halfword;
           results bond to 2^16 * q in abs value. */
        vmladduhm \_v0, v4, V_MKQ, v8
        vmladduhm \_v1, v9, V_MKQ, v12
        vmladduhm \_v2, v13, V_MKQ, v16
        vmladduhm \_v3, v17, V_MKQ, v20
.endm

/*
 * -----------------------------------
 * MREDUCE_4X(_vz0, _vz1, _vz2, _vz3, _vo0, _vo1, _vo2, _vo3)
 */
.macro MREDUCE_4X _vz0 _vz1 _vz2 _vz3 _vo0 _vo1 _vo2 _vo3
        /* Modular multification bond by 2^16 * q in abs value */
        vmladduhm v15, v25, \_vz0, v3
        vmladduhm v20, v26, \_vz1, v3
        vmladduhm v27, v30, \_vz2, v3
        vmladduhm v28, v31, \_vz3, v3

        /* Signed multiply-high-round; outputs are bound by 2^15 * q in abs value */
        vmhraddshs v14, v25, \_vz0, v3
        vmhraddshs v19, v26, \_vz1, v3
        vmhraddshs v24, v30, \_vz2, v3
        vmhraddshs v29, v31, \_vz3, v3

        vmladduhm v15, v15, V_QINV, v3
        vmladduhm v20, v20, V_QINV, v3
        vmladduhm v25, v27, V_QINV, v3
        vmladduhm v30, v28, V_QINV, v3

        vmhraddshs v15, v15, V_NMKQ, v14
        vmhraddshs v20, v20, V_NMKQ, v19
        vmhraddshs v25, v25, V_NMKQ, v24
        vmhraddshs v30, v30, V_NMKQ, v29

        /* Shift right 1 bit */
        vsrah \_vo0, v15, v4
        vsrah \_vo1, v20, v4
        vsrah \_vo2, v25, v4
        vsrah \_vo3, v30, v4
.endm

/*
 * setup constant vectors for Montgmery multiplication
 * V_NMKQ, V_QINV, Zero vector, One vector
 */
.macro Set_mont_consts
        xxlor   32+v5, vs0, vs0    /* V_NMKQ */
        xxlor   32+v2, vs2, vs2    /* V_QINV */
        xxlor   32+v3, vs3, vs3    /* all 0 */
        xxlor   32+v4, vs4, vs4    /* all 1 */
.endm

.macro Load_next_4zetas
        li      r8, 16
        li      r11, 32
        li      r12, 48
        lxvd2x    32+V_Z0, 0, r14
        lxvd2x    32+V_Z1, r8, r14
        lxvd2x    32+V_Z2, r11, r14
        lxvd2x    32+V_Z3, r12, r14
        addi    r14, r14, 64
.endm

/*
 * Re-ordering of the 4-4 layout zetas.
 * Swap double-words.
 */
.macro Perm_4zetas
        xxpermdi 32+V_Z0, 32+V_Z0, 32+V_Z0, 2
        xxpermdi 32+V_Z1, 32+V_Z1, 32+V_Z1, 2
        xxpermdi 32+V_Z2, 32+V_Z2, 32+V_Z2, 2
        xxpermdi 32+V_Z3, 32+V_Z3, 32+V_Z3, 2
.endm

.macro Write_B4C _vs0 _vs1 _vs2 _vs3
        stxvd2x \_vs0, r3, r9
        stxvd2x \_vs1, r3, r16
        stxvd2x \_vs2, r3, r18
        stxvd2x \_vs3, r3, r20
.endm

.macro Write_M4C _vs0 _vs1 _vs2 _vs3
        stxvd2x \_vs0, r3, r10
        stxvd2x \_vs1, r3, r17
        stxvd2x \_vs2, r3, r19
        stxvd2x \_vs3, r3, r21
.endm

.macro Reload_4coeffs
        lxvd2x  32+v25, 0, r3
        lxvd2x  32+v26, r10, r3
        lxvd2x  32+v30, r11, r3
        lxvd2x  32+v31, r12, r3
        addi    r3, r3, 64
.endm

.macro MWrite_8X _vs0 _vs1 _vs2 _vs3 _vs4 _vs5 _vs6 _vs7
        addi    r3, r3, -128
        stxvd2x \_vs0, 0, r3
        stxvd2x \_vs1, r10, r3
        stxvd2x \_vs2, r11, r3
        stxvd2x \_vs3, r12, r3
        stxvd2x \_vs4, r15, r3
        stxvd2x \_vs5, r16, r3
        stxvd2x \_vs6, r17, r3
        stxvd2x \_vs7, r18, r3
        addi    r3, r3, 128
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL44
        xxlor   32+v14, vs10, vs10
        xxlor   32+v19, vs11, vs11
        xxlor   32+v24, vs12, vs12
        xxlor   32+v29, vs13, vs13
        xxpermdi 32+v10, 32+v14, 32+v13, 3
        xxpermdi 32+v11, 32+v14, 32+v13, 0
        xxpermdi 32+v12, 32+v19, 32+v18, 3
        xxpermdi 32+v13, 32+v19, 32+v18, 0
        xxpermdi 32+v14, 32+v24, 32+v23, 3
        xxpermdi 32+v15, 32+v24, 32+v23, 0
        xxpermdi 32+v16, 32+v29, 32+v28, 3
        xxpermdi 32+v17, 32+v29, 32+v28, 0
        stxvd2x    32+v10, 0, r5
        stxvd2x    32+v11, r10, r5
        stxvd2x    32+v12, r11, r5
        stxvd2x    32+v13, r12, r5
        stxvd2x    32+v14, r15, r5
        stxvd2x    32+v15, r16, r5
        stxvd2x    32+v16, r17, r5
        stxvd2x    32+v17, r18, r5
.endm

/*
 * Transpose the final coefficients of 2-2-2-2 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL24
        xxlor   32+v14, vs10, vs10
        xxlor   32+v19, vs11, vs11
        xxlor   32+v24, vs12, vs12
        xxlor   32+v29, vs13, vs13
        vmrgew v10, v13, v14
        vmrgow v11, v13, v14
        vmrgew v12, v18, v19
        vmrgow v13, v18, v19
        vmrgew v14, v23, v24
        vmrgow v15, v23, v24
        vmrgew v16, v28, v29
        vmrgow v17, v28, v29
        stxvd2x    32+v10, 0, r5
        stxvd2x    32+v11, r10, r5
        stxvd2x    32+v12, r11, r5
        stxvd2x    32+v13, r12, r5
        stxvd2x    32+v14, r15, r5
        stxvd2x    32+v15, r16, r5
        stxvd2x    32+v16, r17, r5
        stxvd2x    32+v17, r18, r5
.endm

.macro INTT_REDUCE_L24
        Load_L24Coeffs
        Compute_4Coeffs
        BREDUCE_4X v4, v9, v13, v17
        xxlor   vs10, 32+v4, 32+v4
        xxlor   vs11, 32+v9, 32+v9
        xxlor   vs12, 32+v13, 32+v13
        xxlor   vs13, 32+v17, 32+v17
        Set_mont_consts
        Load_next_4zetas
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, v13, v18, v23, v28
        PermWriteL24
.endm

.macro INTT_REDUCE_L44
        Load_L44Coeffs
        Compute_4Coeffs
        BREDUCE_4X v4, v9, v13, v17
        xxlor   vs10, 32+v4, 32+v4
        xxlor   vs11, 32+v9, 32+v9
        xxlor   vs12, 32+v13, 32+v13
        xxlor   vs13, 32+v17, 32+v17
        Set_mont_consts
        Load_next_4zetas
        Perm_4zetas
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, v13, v18, v23, v28
        PermWriteL44
.endm

.macro INTT_REDUCE_4X start next
        Load_4Coeffs \start, \next
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        Load_next_4zetas
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28
.endm

/*
 * main operations for intt
 * t = r[j];
 * r[j] = barrett_reduce(t + r[j + len]);
 * r[j + len] = r[j + len] - t;
 * r[j + len] = fqmul(zeta, r[j + len]);
 */

/*
 * mlk_intt_ppc(r)
 */
.global MLK_ASM_NAMESPACE(intt_ppc)
.align 4
MLK_ASM_FN_SYMBOL(intt_ppc)

        SAVE_REGS

        /* init vectors and constants
           Setup for Montgomery reduce */
        lxvx    vs0, 0, r4

        li      r10, QINV_OFFSET
        lxvx    32+V_QINV, r10, r4
        xxlxor  32+v3, 32+v3, 32+v3
        vspltish v4, 1
        xxlor   vs2, 32+v2, 32+v2        /* QINV */
        xxlor   vs3, 32+v3, 32+v3        /* 0 vector */
        xxlor   vs4, 32+v4, 32+v4        /* 1 vector */

        /*  Setup for Barrett reduce */
        li      r10, Q_OFFSET
        li      r11, C20159_OFFSET
        lxvx    vs6, r10, r4             /* V_MKQ */
        lxvx    32+V20159, r11, r4       /* V20159 */

        vspltisw v8, 13
        vadduwm  v8, v8, v8
        xxlor   vs8, 32+v8, 32+v8   /* V_26 store at vs8 */

        vspltisw v9, 1
        vsubuwm v10, v8, v9        /* value 25 */
        vslw    v9, v9, v10
        xxlor   vs7, 32+v9, 32+v9   /* V_25 syore at vs7 */

        li      r10, 16
        li      r11, 32
        li      r12, 48
        li      r15, 64
        li      r16, 80
        li      r17, 96
        li      r18, 112

        /*
         * Montgomery reduce loops with constant 1441
         */
        addi    r14, r4, C1441_OFFSET
        lvx     V1441, 0, r14
        li      r8, 4
        mtctr   r8

        Set_mont_consts
intt_ppc__Loopf:
        Reload_4coeffs
        MREDUCE_4X V1441, V1441, V1441, V1441, v6, v7, v8, v9
        Reload_4coeffs
        MREDUCE_4X V1441, V1441, V1441, V1441, v13, v18, v23, v28
        MWrite_8X 32+v6, 32+v7, 32+v8, 32+v9, 32+v13, 32+v18, 32+v23, 32+v28
        bdnz    intt_ppc__Loopf

        addi    r3, r3, -512

.align 4
        /*
         * 1. len = 2, start = 0, 4, 8, 12,...244, 248, 252
         * Update zetas vectors, each vector has 2 zetas
         * Load zeta array in 2-2-2-2 layout
         */
        addi    r14, r4, ZETA_INTT_OFFSET
        li      r7, 4        /* len * 2 */
        li      r8, 4
        mtctr   r8
        mr      r5, r3
intt_ppc__Loop2:
        INTT_REDUCE_L24
        addi    r5, r5, 128
        bdnz    intt_ppc__Loop2

.align 4
        /*
         * 2. len = 4, start = 0, 8, 16, 24,...232, 240, 248
         * Load zeta array in 4-4 layout
         */
        mr      r5, r3
        li      r7, 8
        li      r8, 4
        mtctr   r8
intt_ppc__Loop4:
        INTT_REDUCE_L44
        addi    r5, r5, 128
        bdnz    intt_ppc__Loop4

.align 4
        /*
         * 3. len = 8, start = 0, 16, 32, 48,...208, 224, 240
         */
        li      r7, 16

        INTT_REDUCE_4X 0, 32
        INTT_REDUCE_4X 128, 32
        INTT_REDUCE_4X 256, 32
        INTT_REDUCE_4X 384, 32

.align 4
        /*
         * 4. len = 16, start = 0, 32, 64,,...160, 192, 224
         */
        li      r7, 32

        INTT_REDUCE_4X 0, 64

        addi    r14, r14, -64
        INTT_REDUCE_4X 16, 64

        INTT_REDUCE_4X 256, 64

        addi    r14, r14, -64
        INTT_REDUCE_4X 272, 64

.align 4
        /*
         * 5. len = 32, start = 0, 64, 128, 192
         */
        li      r7, 64

        Load_4Coeffs 0, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 128, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 256, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 384, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

.align 4
        /*
         * 6. len = 64, start = 0, 128
         */
        li      r7, 128
        Load_4Coeffs 0, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 64, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 256, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 320, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

.align 4
        /*
         * 7. len = 128, start = 0
         */
        li      r7, 256          /* len*2 */

        Load_4Coeffs 0, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        lvx     V_ZETA, 0, r14
        xxlor   vs9, 32+V_ZETA, 32+V_ZETA
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 64, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        xxlor   32+V_ZETA, vs9, vs9
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 128, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        xxlor   32+V_ZETA, vs9, vs9
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        Load_4Coeffs 192, 16
        BREDUCE_4X v4, v9, v13, v17
        Write_B4C 32+v4, 32+v9, 32+v13, 32+v17
        Set_mont_consts
        xxlor   32+V_ZETA, vs9, vs9
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, v13, v18, v23, v28
        Write_M4C 32+v13, 32+v18, 32+v23, 32+v28

        RESTORE_REGS
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V20159
#undef V_25
#undef V_26
#undef V_MKQ
#undef V_QINV
#undef V_NMKQ
#undef V_Z0
#undef V_Z1
#undef V_Z2
#undef V_Z3
#undef V_ZETA
#undef V1441

#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
