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

#define V_QINV  2
#define V_NMKQ  5
#define V_Z0    7
#define V_Z1    8
#define V_Z2    9
#define V_Z3    10
#define V_ZETA  10

#define vdata_a1 12
#define vdata_a2 17
#define vdata_a3 22
#define vdata_a4 27
#define vdata_b1 13
#define vdata_b2 18
#define vdata_b3 23
#define vdata_b4 28

#define vresult_a1 15
#define vresult_b1 16
#define vresult_a2 20
#define vresult_b2 21
#define vresult_a3 25
#define vresult_b3 26
#define vresult_a4 30
#define vresult_b4 31

.machine "any"
.text

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
 * Init_Coeffs_offset: initial offset setup for the coeeficient array.
 *
 * start: beginning of the offset to the coefficient array.
 * next: Next offset.
 * len: Index difference between coefficients.
 *
 * r7: len * 2, each coefficient component is 2 bytes.
 *
 * registers used for offset to coefficients, r[j] and r[j+len]
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
        li      9, \start       /* first offset to j */
        add     10, 7, 9        /* J + len*2 */
        addi    16, 9, \next
        addi    17, 10, \next
        addi    18, 16, \next
        addi    19, 17, \next
        addi    20, 18, \next
        addi    21, 19, \next
.endm

/*
 * Load coefficient in r[j+len] (r') vectors from offset, R10, R17, R19 and R21
 *  r[j+len]: V13, V18, V23, V28
 */
.macro Load_4Rjp
        lxvd2x  32+vdata_b1, 3, 10    /* V13: vector r'0 */
        lxvd2x  32+vdata_b2, 3, 17    /* V18: vector for r'1 */
        lxvd2x  32+vdata_b3, 3, 19    /* V23: vector for r'2 */
        lxvd2x  32+vdata_b4, 3, 21    /* V28: vector for r'3 */
.endm

/*
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *  rjlen0, rjlen1, rjlen2, rjlen3, rjlen4, rjlen5, rjlen6, rjlen7
 */
.macro Load_4Coeffs start next
        Init_Coeffs_offset \start \next
        Load_4Rjp
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
 *  r[j+len]: V13, V18, V23, V28
 *  r[j]: V12, V17, V22, V27
 *
 * In order to do the coefficients computation, zeta vector will arrange
 * in the proper order to match the multiplication.
 */
.macro Load_L24Coeffs
        lxvd2x     32+25, 0, 5
        lxvd2x     32+26, 10, 5
        vmrgew vdata_b1, 25, 26
        vmrgow vdata_a1, 25, 26
        lxvd2x     32+25, 11, 5
        lxvd2x     32+26, 12, 5
        vmrgew vdata_b2, 25, 26
        vmrgow vdata_a2, 25, 26
        lxvd2x     32+25, 15, 5
        lxvd2x     32+26, 16, 5
        vmrgew vdata_b3, 25, 26
        vmrgow vdata_a3, 25, 26
        lxvd2x     32+25, 17, 5
        lxvd2x     32+26, 18, 5
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
        lxvd2x     1, 0, 5
        lxvd2x     2, 10, 5
        xxpermdi 32+vdata_b1, 2, 1, 3
        xxpermdi 32+vdata_a1, 2, 1, 0
        lxvd2x     3, 11, 5
        lxvd2x     4, 12, 5
        xxpermdi 32+vdata_b2, 4, 3, 3
        xxpermdi 32+vdata_a2, 4, 3, 0
        lxvd2x     1, 15, 5
        lxvd2x     2, 16, 5
        xxpermdi 32+vdata_b3, 2, 1, 3
        xxpermdi 32+vdata_a3, 2, 1, 0
        lxvd2x     3, 17, 5
        lxvd2x     4, 18, 5
        xxpermdi 32+vdata_b4, 4, 3, 3
        xxpermdi 32+vdata_a4, 4, 3, 0
.endm

/*
 * montgomery_reduce
 * t = a * QINV
 * t = (a - (int32_t)t*_MLKEM_Q) >> 16
 *
 * -----------------------------------
 * MREDUCE_4X(_vz0, _vz1, _vz2, _vz3)
 */
.macro MREDUCE_4X _vz0 _vz1 _vz2 _vz3
        /* fqmul = zeta * coefficient
           Modular multification bond by 2^16 * q in abs value */
        vmladduhm 15, vdata_b1, \_vz0, 3
        vmladduhm 20, vdata_b2, \_vz1, 3
        vmladduhm 25, vdata_b3, \_vz2, 3
        vmladduhm 30, vdata_b4, \_vz3, 3

        /* Signed multiply-high-round; outputs are bound by 2^15 * q in abs value */
        vmhraddshs 14, vdata_b1, \_vz0, 3
        vmhraddshs 19, vdata_b2, \_vz1, 3
        vmhraddshs 24, vdata_b3, \_vz2, 3
        vmhraddshs 29, vdata_b4, \_vz3, 3

        vmladduhm 15, 15, V_QINV, 3
        vmladduhm 20, 20, V_QINV, 3
        vmladduhm 25, 25, V_QINV, 3
        vmladduhm 30, 30, V_QINV, 3

        vmhraddshs 15, 15, V_NMKQ, 14
        vmhraddshs 20, 20, V_NMKQ, 19
        vmhraddshs 25, 25, V_NMKQ, 24
        vmhraddshs 30, 30, V_NMKQ, 29

        /* Shift right 1 bit */
        vsrah vdata_b1, 15, 4
        vsrah vdata_b2, 20, 4
        vsrah vdata_b3, 25, 4
        vsrah vdata_b4, 30, 4
.endm

/*
 * Load 4 r[j] (r) coefficient vectors:
 *   Load coefficient in vectors from offset, R9, R16, R18 and R20
 *  r[j]: V12, V17, V22, V27
 */
.macro Load_4Rj
        lxvd2x  32+vdata_a1, 3, 9     /* V12: vector r0 */
        lxvd2x  32+vdata_a2, 3, 16    /* V17: vector r1 */
        lxvd2x  32+vdata_a3, 3, 18    /* V22: vector r2 */
        lxvd2x  32+vdata_a4, 3, 20    /* V27: vector r3 */
.endm

/*
 * Compute final final r[j] and r[j+len]
 *  final r[j+len]: V16, V21, V26, V31
 *  final r[j]: V15, V20, V25, V30
 */
.macro Compute_4Coeffs
        /* Since the result of the Montgomery multiplication is bounded
           by q in absolute value.
           Finally to complete the final update of the results with add/sub
           r[j] = r[j] + t.
           r[j+len] = r[j] - t
         */
        vsubuhm vresult_b1, vdata_a1, vdata_b1
        vadduhm vresult_a1, vdata_b1, vdata_a1
        vsubuhm vresult_b2, vdata_a2, vdata_b2
        vadduhm vresult_a2, vdata_b2, vdata_a2
        vsubuhm vresult_b3, vdata_a3, vdata_b3
        vadduhm vresult_a3, vdata_b3, vdata_a3
        vsubuhm vresult_b4, vdata_a4, vdata_b4
        vadduhm vresult_a4, vdata_b4, vdata_a4
.endm

.macro Write_One
        stxvd2x 32+vresult_a1, 3, 9
        stxvd2x 32+vresult_b1, 3, 10
        stxvd2x 32+vresult_a2, 3, 16
        stxvd2x 32+vresult_b2, 3, 17
        stxvd2x 32+vresult_a3, 3, 18
        stxvd2x 32+vresult_b3, 3, 19
        stxvd2x 32+vresult_a4, 3, 20
        stxvd2x 32+vresult_b4, 3, 21
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL44
        Compute_4Coeffs
        xxpermdi 0, 32+vresult_a1, 32+vresult_b1, 3
        xxpermdi 1, 32+vresult_a1, 32+vresult_b1, 0
        xxpermdi 2, 32+vresult_a2, 32+vresult_b2, 3
        xxpermdi 3, 32+vresult_a2, 32+vresult_b2, 0
        xxpermdi 4, 32+vresult_a3, 32+vresult_b3, 3
        xxpermdi 5, 32+vresult_a3, 32+vresult_b3, 0
        xxpermdi 6, 32+vresult_a4, 32+vresult_b4, 3
        xxpermdi 7, 32+vresult_a4, 32+vresult_b4, 0
        stxvd2x 0, 0, 5
        stxvd2x 1, 10, 5
        stxvd2x 2, 11, 5
        stxvd2x 3, 12, 5
        stxvd2x 4, 15, 5
        stxvd2x 5, 16, 5
        stxvd2x 6, 17, 5
        stxvd2x 7, 18, 5
.endm

/*
 * Transpose the final coefficients of 2-2-2-2 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL24
        Compute_4Coeffs
        vmrgew 10, vresult_b1, vresult_a1
        vmrgow 11, vresult_b1, vresult_a1
        vmrgew 12, vresult_b2, vresult_a2
        vmrgow 13, vresult_b2, vresult_a2
        vmrgew 14, vresult_b3, vresult_a3
        vmrgow 15, vresult_b3, vresult_a3
        vmrgew 16, vresult_b4, vresult_a4
        vmrgow 17, vresult_b4, vresult_a4
        stxvd2x 32+10, 0, 5
        stxvd2x 32+11, 10, 5
        stxvd2x 32+12, 11, 5
        stxvd2x 32+13, 12, 5
        stxvd2x 32+14, 15, 5
        stxvd2x 32+15, 16, 5
        stxvd2x 32+16, 17, 5
        stxvd2x 32+17, 18, 5
.endm

.macro Load_next_4zetas
        li      10, 16
        li      11, 32
        li      12, 48
        lxvd2x  32+V_Z0, 0, 14
        lxvd2x  32+V_Z1, 10, 14
        lxvd2x  32+V_Z2, 11, 14
        lxvd2x  32+V_Z3, 12, 14
        addi    14, 14, 64
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

.macro NTT_MREDUCE_4X start next _vz0 _vz1 _vz2 _vz3
        Load_4Coeffs \start, \next
        MREDUCE_4x \_vz0, \_vz1, \_vz2, \_vz3
        Load_4Rj
        Compute_4Coeffs
        Write_One
.endm

/*
 * mlk_ntt_ppc(int16_t *r, int16_t *qdata)
 *   Compute forward NTT based on the following 7 layers -
 *     len = 128, 64, 32, 16, 8, 4, 2.
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
 *
 */
.global MLK_ASM_NAMESPACE(ntt_ppc)
.align 4
MLK_ASM_FN_SYMBOL(ntt_ppc)

        SAVE_REGS

        /* load MLKEM_Q */
        lvx     V_NMKQ,0,4

        /* Register 14 as pointer to zetas array */
        addi    14, 4, ZETA_NTT_OFFSET

        vxor    3, 3, 3
        vspltish 4, 1

        li      10, QINV_OFFSET
        lvx     V_QINV, 10, 4

.align 4
        /*
         * 1. len = 128, start = 0
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        128
         *        32        -        160
         *          64        -        192
         *            96        -        224
         *
         *     These are indexes to the 16 bits array
         */
        li      7, 256          /* len * 2 */
        lvx     V_ZETA, 0, 14
        addi    14, 14, 16

        NTT_MREDUCE_4X 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 64, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 192, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

.align 4
        /*
         * 2. len = 64, start = 0, 128
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        64
         *        32        -       96
         *          128        -      192
         *            160        -      224
         *
         *     These are indexes to the 16 bits array
         */
        li      7, 128
        lvx     V_ZETA, 0, 14
        addi    14, 14, 16
        NTT_MREDUCE_4X 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 64, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, 14
        addi    14, 14, 16
        NTT_MREDUCE_4X 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 320, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

.align 4
        /*
         * 3. len = 32, start = 0, 64, 128, 192
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        32
         *        64        -       96
         *          128        -      160
         *            192        -      224
         *
         *     These are indexes to the 16 bits array
         */
        li      7, 64
        lvx     V_ZETA, 0, 14
        addi    14, 14, 16
        NTT_MREDUCE_4X 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, 14
        addi    14, 14, 16
        NTT_MREDUCE_4X 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, 14
        addi    14, 14, 16
        NTT_MREDUCE_4X 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, 14
        addi    14, 14, 16
        NTT_MREDUCE_4X 384, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

.align 4
        /*
         * 4. len = 16, start = 0, 8, 128, 136
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        16
         *        8        -       24
         *          128        -     144
         *            136        -    152
         *
         *     These are indexes to the 16 bits array
         */
        li      7, 32
        Load_next_4zetas
        NTT_MREDUCE_4X 0, 64, V_Z0, V_Z1, V_Z2, V_Z3
        NTT_MREDUCE_4X 16, 64, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 256, 64, V_Z0, V_Z1, V_Z2, V_Z3
        NTT_MREDUCE_4X  272, 64, V_Z0, V_Z1, V_Z2, V_Z3

.align 4
        /*
         * 5. len = 8, start = 0, 64, 128, 192
         *
         *    Compute coefficients of the NTT based on 2 legs,
         *      0        -        8
         *       64        -       72
         *         128        -      136
         *            192        -     200
         *
         *     These are indexes to the 16 bits array
         */
        li      7, 16
        Load_next_4zetas
        NTT_MREDUCE_4X 0, 32, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 128, 32, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 256, 32, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 384, 32, V_Z0, V_Z1, V_Z2, V_Z3

        /*
         * 6. len = 4, start = 0, 8, 16, 24,...232, 240, 248
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
        li      15, 4
        mtctr   15
        mr      5, 3                 /* Let r5 points to coefficient array */
        li      7, 8

        li      10, 16
        li      11, 32
        li      12, 48
        li      15, 64
        li      16, 80
        li      17, 96
        li      18, 112

.align 4
ntt_ppc__Len4:
        Load_next_4zetas
        Perm_4zetas
        Load_L44Coeffs
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3
        PermWriteL44
        addi    5, 5, 128

        bdnz    ntt_ppc__Len4

        /*
         * 7. len = 2, start = 0, 4, 8, 12,...244, 248, 252
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

        li      8, 4
        mtctr   8
        mr      5, 3                  /* Let r5 points to coefficient array */
        li      7, 4

.align 4
ntt_ppc__Len2:
        Load_next_4zetas
        Load_L24Coeffs
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3
        PermWriteL24
        addi    5, 5, 128

        bdnz    ntt_ppc__Len2

        RESTORE_REGS
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V_QINV
#undef V_NMKQ
#undef V_ZETA

#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
