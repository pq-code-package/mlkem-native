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
        lxvd2x  32+13, 3, 10    /* V13: vector r'0 */
        lxvd2x  32+18, 3, 17    /* V18: vector for r'1 */
        lxvd2x  32+23, 3, 19    /* V23: vector for r'2 */
        lxvd2x  32+28, 3, 21    /* V28: vector for r'3 */
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
        vmrgew 13, 25, 26
        vmrgow 12, 25, 26
        lxvd2x     32+25, 11, 5
        lxvd2x     32+26, 12, 5
        vmrgew 18, 25, 26
        vmrgow 17, 25, 26
        lxvd2x     32+25, 15, 5
        lxvd2x     32+26, 16, 5
        vmrgew 23, 25, 26
        vmrgow 22, 25, 26
        lxvd2x     32+25, 17, 5
        lxvd2x     32+26, 18, 5
        vmrgew 28, 25, 26
        vmrgow 27, 25, 26
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
        xxpermdi 32+13, 2, 1, 3
        xxpermdi 32+12, 2, 1, 0
        lxvd2x     3, 11, 5
        lxvd2x     4, 12, 5
        xxpermdi 32+18, 4, 3, 3
        xxpermdi 32+17, 4, 3, 0
        lxvd2x     1, 15, 5
        lxvd2x     2, 16, 5
        xxpermdi 32+23, 2, 1, 3
        xxpermdi 32+22, 2, 1, 0
        lxvd2x     3, 17, 5
        lxvd2x     4, 18, 5
        xxpermdi 32+28, 4, 3, 3
        xxpermdi 32+27, 4, 3, 0
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
        vmladduhm 15, 13, \_vz0, 3
        vmladduhm 20, 18, \_vz1, 3
        vmladduhm 25, 23, \_vz2, 3
        vmladduhm 30, 28, \_vz3, 3

        /* Signed multiply-high-round; outputs are bound by 2^15 * q in abs value */
        vmhraddshs 14, 13, \_vz0, 3
        vmhraddshs 19, 18, \_vz1, 3
        vmhraddshs 24, 23, \_vz2, 3
        vmhraddshs 29, 28, \_vz3, 3

        vmladduhm 15, 15, V_QINV, 3
        vmladduhm 20, 20, V_QINV, 3
        vmladduhm 25, 25, V_QINV, 3
        vmladduhm 30, 30, V_QINV, 3

        vmhraddshs 15, 15, V_NMKQ, 14
        vmhraddshs 20, 20, V_NMKQ, 19
        vmhraddshs 25, 25, V_NMKQ, 24
        vmhraddshs 30, 30, V_NMKQ, 29

        /* Shift right 1 bit */
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
.endm

/*
 * Load 4 r[j] (r) coefficient vectors:
 *   Load coefficient in vectors from offset, R9, R16, R18 and R20
 *  r[j]: V12, V17, V22, V27
 */
.macro Load_4Rj
        lxvd2x  32+12, 3, 9     /* V12: vector r0 */
        lxvd2x  32+17, 3, 16    /* V17: vector r1 */
        lxvd2x  32+22, 3, 18    /* V22: vector r2 */
        lxvd2x  32+27, 3, 20    /* V27: vector r3 */
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
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
.endm

.macro Write_One
        stxvd2x 32+15, 3, 9
        stxvd2x 32+16, 3, 10
        stxvd2x 32+20, 3, 16
        stxvd2x 32+21, 3, 17
        stxvd2x 32+25, 3, 18
        stxvd2x 32+26, 3, 19
        stxvd2x 32+30, 3, 20
        stxvd2x 32+31, 3, 21
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL44
        Compute_4Coeffs
        xxpermdi 0, 32+15, 32+16, 3
        xxpermdi 1, 32+15, 32+16, 0
        xxpermdi 2, 32+20, 32+21, 3
        xxpermdi 3, 32+20, 32+21, 0
        xxpermdi 4, 32+25, 32+26, 3
        xxpermdi 5, 32+25, 32+26, 0
        xxpermdi 6, 32+30, 32+31, 3
        xxpermdi 7, 32+30, 32+31, 0
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
        vmrgew 10, 16, 15
        vmrgow 11, 16, 15
        vmrgew 12, 21, 20
        vmrgow 13, 21, 20
        vmrgew 14, 26, 25
        vmrgow 15, 26, 25
        vmrgew 16, 31, 30
        vmrgow 17, 31, 30
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
 * mlk_ntt_ppc(int16_t *r)
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
         * Compute coefficients of the NTT based on the following loop.
         *   for (len = 128; len ≥ 2; len =  len/2)
         *
         * 1. len = 128, start = 0
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
         * k += 2
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
         * k += 4
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
         * 4. len = 16, start = 0, 32, 64,,...160, 192, 224
         * k += 8
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
         * 5. len = 8, start = 0, 16, 32, 48,...208, 224, 240
         * k += 16
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
         * k += 32
         * Load zeta vectors in 4-4 layout
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
         * k += 64
         * Load zeta vectors in 2-2-2-2 layout
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
