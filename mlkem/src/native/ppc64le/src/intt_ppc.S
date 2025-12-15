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
#define V2pw25  1
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

#define vdata_a1 21
#define vdata_a2 22
#define vdata_a3 23
#define vdata_a4 24
#define vdata_b1 8
#define vdata_b2 12
#define vdata_b3 16
#define vdata_b4 20

#define vdata_brt1 8
#define vdata_brt2 12
#define vdata_brt3 16
#define vdata_brt4 20

#define vdata_mont1 25
#define vdata_mont2 26
#define vdata_mont3 30
#define vdata_mont4 31

#define vresult_brt1 4
#define vresult_brt2 9
#define vresult_brt3 13
#define vresult_brt4 17
#define vresult_mont1 13
#define vresult_mont2 18
#define vresult_mont3 23
#define vresult_mont4 28

#define rinp      3
#define dup_rinp  5
#define qinp      4
#define len_2     7
#define zeta_inp  14
#define a1_offset 9
#define a2_offset 16
#define a3_offset 18
#define a4_offset 20
#define b1_offset 10
#define b2_offset 17
#define b3_offset 19
#define b4_offset 21

.macro SAVE_REGS
        stdu    1, -352(1)
        mflr    0
        std     14, 56(1)
        std     15, 64(1)
        std     16, 72(1)
        std     17, 80(1)
        std     18, 88(1)
        std     19, 96(1)
        std     20, 104(1)
        std     21, 112(1)
        li      10, 128
        li      11, 144
        li      12, 160
        li      14, 176
        li      15, 192
        li      16, 208
        stxvx   32+20, 10, 1
        stxvx   32+21, 11, 1
        stxvx   32+22, 12, 1
        stxvx   32+23, 14, 1
        stxvx   32+24, 15, 1
        stxvx   32+25, 16, 1
        li      10, 224
        li      11, 240
        li      12, 256
        li      14, 272
        li      15, 288
        li      16, 304
        stxvx   32+26, 10, 1
        stxvx   32+27, 11, 1
        stxvx   32+28, 12, 1
        stxvx   32+29, 14, 1
        stxvx   32+30, 15, 1
        stxvx   32+31, 16, 1
.endm

.macro RESTORE_REGS
        li      10, 128
        li      11, 144
        li      12, 160
        li      14, 176
        li      15, 192
        li      16, 208
        lxvx    32+20, 10, 1
        lxvx    32+21, 11, 1
        lxvx    32+22, 12, 1
        lxvx    32+23, 14, 1
        lxvx    32+24, 15, 1
        lxvx    32+25, 16, 1
        li      10, 224
        li      11, 240
        li      12, 256
        li      14, 272
        li      15, 288
        li      16, 304
        lxvx    32+26, 10, 1
        lxvx    32+27, 11, 1
        lxvx    32+28, 12, 1
        lxvx    32+29, 14, 1
        lxvx    32+30, 15, 1
        lxvx    32+31, 16, 1
        ld      14, 56(1)
        ld      15, 64(1)
        ld      16, 72(1)
        ld      17, 80(1)
        ld      18, 88(1)
        ld      19, 96(1)
        ld      20, 104(1)
        ld      21, 112(1)

        mtlr    0
        addi    1, 1, 352
.endm

/*
 * Compute r[j] and r[j+len] from computed coefficients
 *  r[j] + r[j+len] : V8, V12, V16, V20 (data for Barett reduce)
 *  r[j+len] - r[j]: V25, V26, V30, V31 (data for Montgomery reduce)
 */
.macro Compute_4Coeffs
        vsubuhm vdata_mont1, vdata_b1, vdata_a1
        vsubuhm vdata_mont2, vdata_b2, vdata_a2
        vsubuhm vdata_mont3, vdata_b3, vdata_a3
        vsubuhm vdata_mont4, vdata_b4, vdata_a4
        vadduhm vdata_brt1, vdata_b1, vdata_a1
        vadduhm vdata_brt2, vdata_b2, vdata_a2
        vadduhm vdata_brt3, vdata_b3, vdata_a3
        vadduhm vdata_brt4, vdata_b4, vdata_a4
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
        li      a1_offset, \start               /* first offset to j */
        add     b1_offset, len_2, a1_offset     /* J + len*2 */
        addi    a2_offset, a1_offset, \next
        addi    b2_offset, b1_offset, \next
        addi    a3_offset, a2_offset, \next
        addi    b3_offset, b2_offset, \next
        addi    a4_offset, a3_offset, \next
        addi    b4_offset, b3_offset, \next
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
        lxvd2x  32+vdata_b1, rinp, b1_offset    /* V8: vector r'0 */
        lxvd2x  32+vdata_b2, rinp, b2_offset    /* V12: vector for r'1 */
        lxvd2x  32+vdata_b3, rinp, b3_offset    /* V16: vector for r'2 */
        lxvd2x  32+vdata_b4, rinp, b4_offset    /* V20: vector for r'3 */

        lxvd2x  32+vdata_a1, rinp, a1_offset     /* V21: vector r0 */
        lxvd2x  32+vdata_a2, rinp, a2_offset    /* V22: vector r1 */
        lxvd2x  32+vdata_a3, rinp, a3_offset    /* V23: vector r2 */
        lxvd2x  32+vdata_a4, rinp, a4_offset    /* V24: vector r3 */
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
        lxvd2x     32+25, 0, dup_rinp
        lxvd2x     32+26, 10, dup_rinp
        vmrgew vdata_b1, 25, 26
        vmrgow vdata_a1, 25, 26
        lxvd2x     32+25, 11, dup_rinp
        lxvd2x     32+26, 12, dup_rinp
        vmrgew vdata_b2, 25, 26
        vmrgow vdata_a2, 25, 26
        lxvd2x     32+25, 15, dup_rinp
        lxvd2x     32+26, 16, dup_rinp
        vmrgew vdata_b3, 25, 26
        vmrgow vdata_a3, 25, 26
        lxvd2x     32+25, 17, dup_rinp
        lxvd2x     32+26, 18, dup_rinp
        vmrgew vdata_b4, 25, 26
        vmrgow vdata_a4, 25, 26
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
        lxvd2x     10, 0, dup_rinp
        lxvd2x     11, 10, dup_rinp
        xxpermdi 32+vdata_b1, 11, 10, 3
        xxpermdi 32+vdata_a1, 11, 10, 0
        lxvd2x     10, 11, dup_rinp
        lxvd2x     11, 12, dup_rinp
        xxpermdi 32+vdata_b2, 11, 10, 3
        xxpermdi 32+vdata_a2, 11, 10, 0
        lxvd2x     10, 15, dup_rinp
        lxvd2x     11, 16, dup_rinp
        xxpermdi 32+vdata_b3, 11, 10, 3
        xxpermdi 32+vdata_a3, 11, 10, 0
        lxvd2x     10, 17, dup_rinp
        lxvd2x     11, 18, dup_rinp
        xxpermdi 32+vdata_b4, 11, 10, 3
        xxpermdi 32+vdata_a4, 11, 10, 0
.endm

.macro BREDUCE_4X _v0 _v1 _v2 _v3
        /* Restore constant vectors
           V_MKQ, V2pw25 and V_26 */
        vxor    7, 7, 7
        xxlor   32+3, 6, 6
        xxlor   32+1, 7, 7
        xxlor   32+2, 8, 8
        /* Multify Odd/Even signed halfword;
           Results word bound by 2^32 in abs value. */
        vmulosh 6, vdata_brt1, V20159
        vmulesh 5, vdata_brt1, V20159
        vmulosh 11, vdata_brt2, V20159
        vmulesh 10, vdata_brt2, V20159
        vmulosh 15, vdata_brt3, V20159
        vmulesh 14, vdata_brt3, V20159
        vmulosh 19, vdata_brt4, V20159
        vmulesh 18, vdata_brt4, V20159
        xxmrglw 32+4, 32+5, 32+6
        xxmrghw 32+5, 32+5, 32+6
        xxmrglw 32+9, 32+10, 32+11
        xxmrghw 32+10, 32+10, 32+11
        xxmrglw 32+13, 32+14, 32+15
        xxmrghw 32+14, 32+14, 32+15
        xxmrglw 32+17, 32+18, 32+19
        xxmrghw 32+18, 32+18, 32+19
        vadduwm 4, 4, V2pw25
        vadduwm 5, 5, V2pw25
        vadduwm 9, 9, V2pw25
        vadduwm 10, 10, V2pw25
        vadduwm 13, 13, V2pw25
        vadduwm 14, 14, V2pw25
        vadduwm 17, 17, V2pw25
        vadduwm 18, 18, V2pw25
        /* Right shift and pack lower halfword,
           results bond to 2^16 in abs value */
        vsraw   4, 4, V_26
        vsraw   5, 5, V_26
        vsraw   9, 9, V_26
        vsraw   10, 10, V_26
        vsraw   13, 13, V_26
        vsraw   14, 14, V_26
        vsraw   17, 17, V_26
        vsraw   18, 18, V_26
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        /* Modulo multify-Low unsigned halfword;
           results bond to 2^16 * q in abs value. */
        vmladduhm \_v0, 4, V_MKQ, 8
        vmladduhm \_v1, 9, V_MKQ, 12
        vmladduhm \_v2, 13, V_MKQ, 16
        vmladduhm \_v3, 17, V_MKQ, 20
.endm

/*
 * -----------------------------------
 * MREDUCE_4X(_vz0, _vz1, _vz2, _vz3, _vo0, _vo1, _vo2, _vo3)
 */
.macro MREDUCE_4X _vz0 _vz1 _vz2 _vz3 _vo0 _vo1 _vo2 _vo3
        /* Modular multification bond by 2^16 * q in abs value */
        vmladduhm 15, vdata_mont1, \_vz0, rinp
        vmladduhm 20, vdata_mont2, \_vz1, rinp
        vmladduhm 27, vdata_mont3, \_vz2, rinp
        vmladduhm 28, vdata_mont4, \_vz3, rinp

        /* Signed multiply-high-round; outputs are bound by 2^15 * q in abs value */
        vmhraddshs 14, vdata_mont1, \_vz0, rinp
        vmhraddshs 19, vdata_mont2, \_vz1, rinp
        vmhraddshs 24, vdata_mont3, \_vz2, rinp
        vmhraddshs 29, vdata_mont4, \_vz3, rinp

        vmladduhm 15, 15, V_QINV, 3
        vmladduhm 20, 20, V_QINV, 3
        vmladduhm 25, 27, V_QINV, 3
        vmladduhm 30, 28, V_QINV, 3

        vmhraddshs 15, 15, V_NMKQ, 14
        vmhraddshs 20, 20, V_NMKQ, 19
        vmhraddshs 25, 25, V_NMKQ, 24
        vmhraddshs 30, 30, V_NMKQ, 29

        /* Shift right 1 bit */
        vsrah \_vo0, 15, 4
        vsrah \_vo1, 20, 4
        vsrah \_vo2, 25, 4
        vsrah \_vo3, 30, 4
.endm

/*
 * setup constant vectors for Montgmery multiplication
 * V_NMKQ, V_QINV, Zero vector, One vector
 */
.macro Set_mont_consts
        xxlor   32+5, 0, 0    /* V_NMKQ */
        xxlor   32+2, 2, 2    /* V_QINV */
        xxlor   32+3, 3, 3    /* all 0 */
        xxlor   32+4, 4, 4    /* all 1 */
.endm

.macro Load_next_4zetas
        li      8, 16
        li      11, 32
        li      12, 48
        lxvd2x    32+V_Z0, 0, zeta_inp
        lxvd2x    32+V_Z1, 8, zeta_inp
        lxvd2x    32+V_Z2, 11, zeta_inp
        lxvd2x    32+V_Z3, 12, zeta_inp
        addi    zeta_inp, zeta_inp, 64
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
        stxvd2x \_vs0, rinp, a1_offset
        stxvd2x \_vs1, rinp, a2_offset
        stxvd2x \_vs2, rinp, a3_offset
        stxvd2x \_vs3, rinp, a4_offset
.endm

.macro Write_M4C _vs0 _vs1 _vs2 _vs3
        stxvd2x \_vs0, rinp, b1_offset
        stxvd2x \_vs1, rinp, b2_offset
        stxvd2x \_vs2, rinp, b3_offset
        stxvd2x \_vs3, rinp, b4_offset
.endm

.macro Reload_4coeffs
        lxvd2x  32+vdata_mont1, 0, rinp
        lxvd2x  32+vdata_mont2, 10, rinp
        lxvd2x  32+vdata_mont3, 11, rinp
        lxvd2x  32+vdata_mont4, 12, rinp
        addi    rinp, rinp, 64
.endm

.macro MWrite_8X _vs0 _vs1 _vs2 _vs3 _vs4 _vs5 _vs6 _vs7
        addi    rinp, rinp, -128
        stxvd2x \_vs0, 0, rinp
        stxvd2x \_vs1, 10, rinp
        stxvd2x \_vs2, 11, rinp
        stxvd2x \_vs3, 12, rinp
        stxvd2x \_vs4, 15, rinp
        stxvd2x \_vs5, 16, rinp
        stxvd2x \_vs6, 17, rinp
        stxvd2x \_vs7, 18, rinp
        addi    rinp, rinp, 128
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL44
        xxlor   32+14, 10, 10
        xxlor   32+19, 11, 11
        xxlor   32+24, 12, 12
        xxlor   32+29, 13, 13
        xxpermdi 32+10, 32+14, 32+vresult_mont1, 3
        xxpermdi 32+11, 32+14, 32+vresult_mont1, 0
        xxpermdi 32+12, 32+19, 32+vresult_mont2, 3
        xxpermdi 32+13, 32+19, 32+vresult_mont2, 0
        xxpermdi 32+14, 32+24, 32+vresult_mont3, 3
        xxpermdi 32+15, 32+24, 32+vresult_mont3, 0
        xxpermdi 32+16, 32+29, 32+vresult_mont4, 3
        xxpermdi 32+17, 32+29, 32+vresult_mont4, 0
        stxvd2x    32+10, 0, dup_rinp
        stxvd2x    32+11, 10, dup_rinp
        stxvd2x    32+12, 11, dup_rinp
        stxvd2x    32+13, 12, dup_rinp
        stxvd2x    32+14, 15, dup_rinp
        stxvd2x    32+15, 16, dup_rinp
        stxvd2x    32+16, 17, dup_rinp
        stxvd2x    32+17, 18, dup_rinp
.endm

/*
 * Transpose the final coefficients of 2-2-2-2 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL24
        xxlor   32+14, 10, 10
        xxlor   32+19, 11, 11
        xxlor   32+24, 12, 12
        xxlor   32+29, 13, 13
        vmrgew 10, vresult_mont1, 14
        vmrgow 11, vresult_mont1, 14
        vmrgew 12, vresult_mont2, 19
        vmrgow 13, vresult_mont2, 19
        vmrgew 14, vresult_mont3, 24
        vmrgow 15, vresult_mont3, 24
        vmrgew 16, vresult_mont4, 29
        vmrgow 17, vresult_mont4, 29
        stxvd2x    32+10, 0, dup_rinp
        stxvd2x    32+11, 10, dup_rinp
        stxvd2x    32+12, 11, dup_rinp
        stxvd2x    32+13, 12, dup_rinp
        stxvd2x    32+14, 15, dup_rinp
        stxvd2x    32+15, 16, dup_rinp
        stxvd2x    32+16, 17, dup_rinp
        stxvd2x    32+17, 18, dup_rinp
.endm

/*
 * INTT layer Len=2.
 */
.macro INTT_REDUCE_L24
        Load_L24Coeffs
        Compute_4Coeffs
        BREDUCE_4X vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        xxlor   10, 32+vresult_brt1, 32+vresult_brt1
        xxlor   11, 32+vresult_brt2, 32+vresult_brt2
        xxlor   12, 32+vresult_brt3, 32+vresult_brt3
        xxlor   13, 32+vresult_brt4, 32+vresult_brt4
        Set_mont_consts
        Load_next_4zetas
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, vresult_mont1, vresult_mont2, vresult_mont3, vresult_mont4
        PermWriteL24
.endm

/*
 * INTT layer Len=4.
 */
.macro INTT_REDUCE_L44
        Load_L44Coeffs
        Compute_4Coeffs
        BREDUCE_4X vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        xxlor   10, 32+vresult_brt1, 32+vresult_brt1
        xxlor   11, 32+vresult_brt2, 32+vresult_brt2
        xxlor   12, 32+vresult_brt3, 32+vresult_brt3
        xxlor   13, 32+vresult_brt4, 32+vresult_brt4
        Set_mont_consts
        Load_next_4zetas
        Perm_4zetas
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, vresult_mont1, vresult_mont2, vresult_mont3, vresult_mont4
        PermWriteL44
.endm

/*
 * INTT layer Len=8 and 16.
 */
.macro INTT_REDUCE_4X start next
        Load_4Coeffs \start, \next
        BREDUCE_4X vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        Write_B4C 32+vresult_brt1, 32+vresult_brt2, 32+vresult_brt3, 32+vresult_brt4
        Set_mont_consts
        Load_next_4zetas
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, vresult_mont1, vresult_mont2, vresult_mont3, vresult_mont4
        Write_M4C 32+vresult_mont1, 32+vresult_mont2, 32+vresult_mont3, 32+vresult_mont4
.endm

/*
 * INTT layer Len=32, 64 and 128.
 */
.macro INTT_REDUCE_L567 start next
        Load_4Coeffs \start, \next
        BREDUCE_4X vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        Write_B4C 32+vresult_brt1, 32+vresult_brt2, 32+vresult_brt3, 32+vresult_brt4
        Set_mont_consts
        lvx     V_ZETA, 0, 14
        //addi    14, 14, 16
        MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, vresult_mont1, vresult_mont2, vresult_mont3, vresult_mont4
        Write_M4C 32+vresult_mont1, 32+vresult_mont2, 32+vresult_mont3, 32+vresult_mont4
.endm

/*
 * mlk_intt_ppc(int16_t *r, int16_t *qdata)
 *   Compute inverse NTT based on the following 7 layers -
 *     len = 2, 4, 8, 16, 32, 64, 128
 *
 *   Each layer compute the coeffients on 2 legs, start and start + len*2 offsets.
 *
 *   leg 1                        leg 2
 *   -----                        -----
 *   start                        start+len*2
 *   start+next                   start+len*2+next
 *   start+next+next              start+len*2+next+next
 *   start+next+next+next         start+len*2+next+next+next
 *
 *   Each computation loads 8 vectors, 4 for each leg.
 *   The final coefficient (t) from each vector of leg1 and leg2 then do the
 *   add/sub operations to obtain the final results.
 *
 *   -> leg1 = leg1 + t, leg2 = leg1 - t
 *
 *   The resulting coeffients then store back to each leg's offset.
 *
 *   Each vector has the same corresponding zeta except len=4 and len=2.
 *
 *   len=4 has 4-4 layout which means every 4 16-bit coeffients has the same zeta.
 *   and len=2 has 2-2-2-2 layout which means every 2 16-bit coeffients has the same zeta.
 *   e.g.
 *         coeff vector    a1   a2   a3  a4  a5  a6  a7  a8
 *         zeta  vector    z1   z1   z2  z2  z3  z3  z4  z4
 *
 *   For len=4 and len=2, each vector will get permuted to leg1 and leg2. Zeta is
 *   pre-arranged for the leg1 and leg2.  After the computation, each vector needs
 *   to transpose back to its original 4-4 or 2-2-2-2 layout.
 */
.global MLK_ASM_NAMESPACE(intt_ppc)
.align 4
MLK_ASM_FN_SYMBOL(intt_ppc)

        SAVE_REGS

        /* init vectors and constants
           Setup for Montgomery reduce */
        lxvx    0, 0, qinp

        li      10, QINV_OFFSET
        lxvx    32+V_QINV, 10, qinp
        xxlxor  32+3, 32+3, 32+3
        vspltish 4, 1
        xxlor   2, 32+2, 32+2        /* QINV */
        xxlor   3, 32+3, 32+3        /* 0 vector */
        xxlor   4, 32+4, 32+4        /* 1 vector */

        /*  Setup for Barrett reduce */
        li      10, Q_OFFSET
        li      11, C20159_OFFSET
        lxvx    6, 10, qinp             /* V_MKQ */
        lxvx    32+V20159, 11, qinp     /* V20159 */

        vspltisw 8, 13
        vadduwm  8, 8, 8
        xxlor   8, 32+8, 32+8   /* V_26 store at vs8 */

        vspltisw 9, 1
        vsubuwm 10, 8, 9        /* value 25 */
        vslw    9, 9, 10
        xxlor   7, 32+9, 32+9   /* V2pw25 store at vs7 */

        li      10, 16
        li      11, 32
        li      12, 48
        li      15, 64
        li      16, 80
        li      17, 96
        li      18, 112

        /*
         * Montgomery reduce loops with constant 1441
         */
        addi    zeta_inp, qinp, C1441_OFFSET
        lvx     V1441, 0, zeta_inp
        li      8, 4
        mtctr   8

        Set_mont_consts
intt_ppc__Loopf:
        Reload_4coeffs
        MREDUCE_4X V1441, V1441, V1441, V1441, 6, 7, 8, 9
        Reload_4coeffs
        MREDUCE_4X V1441, V1441, V1441, V1441, 13, 18, 23, 28
        MWrite_8X 32+6, 32+7, 32+8, 32+9, 32+13, 32+18, 32+23, 32+28
        bdnz    intt_ppc__Loopf

        addi    rinp, rinp, -512

.align 4
        /*
         * 1. len = 2, start = 0, 4, 8, 12,...244, 248, 252
         *    Update zetas vectors, each vector has 2 zetas
         *    Load zeta vectors in 2-2-2-2 layout
         *
         *    Compute coefficients of the NTT based on the following sequences,
         *      0, 1, 2, 3, 4, 5, 6, 7
         *      8, 9, 10, 11, 12, 13, 14, 15
         *            ...
         *      240, 241, 242, 243, 244, 245, 246, 247
         *      248, 249, 250, 251, 252, 253, 254, 255
         *
         *     These are indexes to the 16 bits array.  Each loads 4 vectors.
         */
        addi    zeta_inp, qinp, ZETA_INTT_OFFSET
        li      len_2, 4        /* len * 2 */
        mr      dup_rinp, rinp

        INTT_REDUCE_L24
        addi    dup_rinp, dup_rinp, 128
        INTT_REDUCE_L24
        addi    dup_rinp, dup_rinp, 128
        INTT_REDUCE_L24
        addi    dup_rinp, dup_rinp, 128
        INTT_REDUCE_L24
        addi    dup_rinp, dup_rinp, 128

.align 4
        /*
         * 2. len = 4, start = 0, 8, 16, 24,...232, 240, 248
         *    Load zeta vectors in 4-4 layout
         *
         *    Compute coefficients of the NTT based on the following sequences,
         *      0, 1, 2, 3, 4, 5, 6, 7
         *      8, 9, 10, 11, 12, 13, 14, 15
         *            ...
         *      240, 241, 242, 243, 244, 245, 246, 247
         *      248, 249, 250, 251, 252, 253, 254, 255
         *
         *     These are indexes to the 16 bits array.  Each loads 4 vectors.
         */
        mr      dup_rinp, rinp
        li      len_2, 8

        INTT_REDUCE_L44
        addi    dup_rinp, dup_rinp, 128
        INTT_REDUCE_L44
        addi    dup_rinp, dup_rinp, 128
        INTT_REDUCE_L44
        addi    dup_rinp, dup_rinp, 128
        INTT_REDUCE_L44
        addi    dup_rinp, dup_rinp, 128

.align 4
        /*
         * 3. len = 8, start = 0, 16, 32, 48,...208, 224, 240
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        8
         *       64        -       72
         *         128        -      136
         *            192        -     200
         *
         *     These are indexes to the 16 bits array
         */
        li      len_2, 16

        INTT_REDUCE_4X 0, 32
        INTT_REDUCE_4X 128, 32
        INTT_REDUCE_4X 256, 32
        INTT_REDUCE_4X 384, 32

.align 4
        /*
         * 4. len = 16, start = 0, 32, 64,,...160, 192, 224
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        16
         *        8        -       24
         *          128        -     144
         *            136        -    152
         *
         *     These are indexes to the 16 bits array
         */
        li      len_2, 32

        INTT_REDUCE_4X 0, 64

        addi    zeta_inp, zeta_inp, -64
        INTT_REDUCE_4X 16, 64

        INTT_REDUCE_4X 256, 64

        addi    zeta_inp, zeta_inp, -64
        INTT_REDUCE_4X 272, 64

.align 4
        /*
         * 5. len = 32, start = 0, 64, 128, 192
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        32
         *        64        -       96
         *          128        -      160
         *            192        -      224
         *
         *     These are indexes to the 16 bits array
         */
        li      len_2, 64

        INTT_REDUCE_L567 0, 16
        addi    zeta_inp, zeta_inp, 16
        INTT_REDUCE_L567 128, 16
        addi    zeta_inp, zeta_inp, 16
        INTT_REDUCE_L567 256, 16
        addi    zeta_inp, zeta_inp, 16
        INTT_REDUCE_L567 384, 16
        addi    zeta_inp, zeta_inp, 16

.align 4
        /*
         * 6. len = 64, start = 0, 128
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        64
         *        32        -       96
         *          128        -      192
         *            160        -      224
         *
         *     These are indexes to the 16 bits array
         */
        li      len_2, 128

        INTT_REDUCE_L567 0, 16
        INTT_REDUCE_L567 64, 16
        addi    zeta_inp, zeta_inp, 16
        INTT_REDUCE_L567 256, 16
        INTT_REDUCE_L567 320, 16
        addi    zeta_inp, zeta_inp, 16

.align 4
        /*
         * 7. len = 128, start = 0
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        128
         *        32        -        160
         *          64        -        192
         *            96        -        224
         *
         *     These are indexes to the 16 bits array
         */
        li      len_2, 256          /* len*2 */

        INTT_REDUCE_L567 0, 16
        INTT_REDUCE_L567 64, 16
        INTT_REDUCE_L567 128, 16
        INTT_REDUCE_L567 192, 16

        RESTORE_REGS
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V20159
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
