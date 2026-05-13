/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * Copyright IBM Corp. 2025, 2026
 *
 * ===================================================================================
 * Written by Danny Tsen <dtsen@us.ibm.com>
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && defined(__POWER8_VECTOR__)
/* simpasm: header-end */

#include "consts.h"

#define V_ZERO   3
#define V_NMKQ   5
#define V_Z0     7
#define V_Z1     8
#define V_Z2     9
#define V_Z3     10
#define V_ZETA   10
#define V_ZT0    0
#define V_ZT1    1
#define V_ZT2    6
#define V_ZT3    11
#define V_ZETATW 2

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

#define rinp      3
#define dup_rinp  5
#define qinp      4
#define len_2     7
#define zeta_inp     14
#define zeta_tw_inp  22
#define a1_offset 9
#define a2_offset 16
#define a3_offset 18
#define a4_offset 20
#define b1_offset 10
#define b2_offset 17
#define b3_offset 19
#define b4_offset 21

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
        std     22, 120(1)
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
        ld      22, 120(1)

        mtlr    0
        addi    1, 1, 352
.endm

/*
 * Init_Coeffs_offset: initial offset setup for the coefficient array.
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
.macro Init_Coeffs_offset start, next
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
 * Load coefficient in r[j+len] (r') vectors from offset, R10, R17, R19 and R21
 *  r[j+len]: V13, V18, V23, V28
 */
.macro Load_4Rjp
        lxvd2x  32+vdata_b1, rinp, b1_offset    /* V13: vector r'0 */
        lxvd2x  32+vdata_b2, rinp, b2_offset    /* V18: vector for r'1 */
        lxvd2x  32+vdata_b3, rinp, b3_offset    /* V23: vector for r'2 */
        lxvd2x  32+vdata_b4, rinp, b4_offset    /* V28: vector for r'3 */
.endm

/*
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *  rjlen0, rjlen1, rjlen2, rjlen3, rjlen4, rjlen5, rjlen6, rjlen7
 */
.macro Load_4Coeffs start, next
        Init_Coeffs_offset \start, \next
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
        lxvd2x     1, 0, dup_rinp
        lxvd2x     2, 10, dup_rinp
        xxpermdi 32+vdata_b1, 2, 1, 3
        xxpermdi 32+vdata_a1, 2, 1, 0
        lxvd2x     3, 11, dup_rinp
        lxvd2x     4, 12, dup_rinp
        xxpermdi 32+vdata_b2, 4, 3, 3
        xxpermdi 32+vdata_a2, 4, 3, 0
        lxvd2x     1, 15, dup_rinp
        lxvd2x     2, 16, dup_rinp
        xxpermdi 32+vdata_b3, 2, 1, 3
        xxpermdi 32+vdata_a3, 2, 1, 0
        lxvd2x     3, 17, dup_rinp
        lxvd2x     4, 18, dup_rinp
        xxpermdi 32+vdata_b4, 4, 3, 3
        xxpermdi 32+vdata_a4, 4, 3, 0
.endm

/*
 * Barrett multiplication (4 lanes).
 *   For each lane (b in vdata_b_i, z in _vz_i, zt in _vzt_i):
 *     t    = vmhraddshs(b, zt, 0)    = round(b*zt / 2^15)
 *     b_lo = vmladduhm(b, z, 0)      = (b*z) mod 2^16
 *     vdata_b_i = vmladduhm(t, -q, b_lo)  = b*z - t*q (mod 2^16)
 *
 *   Yields the signed canonical representative of (b*z) mod q,
 *   bounded by q/2.
 */
.macro barrett_fqmul_4x _vz0, _vz1, _vz2, _vz3, _vzt0, _vzt1, _vzt2, _vzt3
        vmhraddshs vresult_a1, vdata_b1, \_vzt0, V_ZERO
        vmhraddshs vresult_a2, vdata_b2, \_vzt1, V_ZERO
        vmhraddshs vresult_a3, vdata_b3, \_vzt2, V_ZERO
        vmhraddshs vresult_a4, vdata_b4, \_vzt3, V_ZERO

        vmladduhm vdata_b1, vdata_b1, \_vz0, V_ZERO
        vmladduhm vdata_b2, vdata_b2, \_vz1, V_ZERO
        vmladduhm vdata_b3, vdata_b3, \_vz2, V_ZERO
        vmladduhm vdata_b4, vdata_b4, \_vz3, V_ZERO

        vmladduhm vdata_b1, vresult_a1, V_NMKQ, vdata_b1
        vmladduhm vdata_b2, vresult_a2, V_NMKQ, vdata_b2
        vmladduhm vdata_b3, vresult_a3, V_NMKQ, vdata_b3
        vmladduhm vdata_b4, vresult_a4, V_NMKQ, vdata_b4
.endm

/*
 * Load 4 r[j] (r) coefficient vectors:
 *   Load coefficient in vectors from offset, R9, R16, R18 and R20
 *  r[j]: V12, V17, V22, V27
 */
.macro Load_4Rj
        lxvd2x  32+vdata_a1, rinp, a1_offset     /* V12: vector r0 */
        lxvd2x  32+vdata_a2, rinp, a2_offset    /* V17: vector r1 */
        lxvd2x  32+vdata_a3, rinp, a3_offset    /* V22: vector r2 */
        lxvd2x  32+vdata_a4, rinp, a4_offset    /* V27: vector r3 */
.endm

/*
 * Compute final final r[j] and r[j+len]
 *  final r[j+len]: V16, V21, V26, V31
 *  final r[j]: V15, V20, V25, V30
 */
.macro Compute_4Coeffs
        /* Since the result of the Barrett multiplication is bounded
           by q/2 in absolute value.
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
        stxvd2x 32+vresult_a1, rinp, a1_offset
        stxvd2x 32+vresult_b1, rinp, b1_offset
        stxvd2x 32+vresult_a2, rinp, a2_offset
        stxvd2x 32+vresult_b2, rinp, b2_offset
        stxvd2x 32+vresult_a3, rinp, a3_offset
        stxvd2x 32+vresult_b3, rinp, b3_offset
        stxvd2x 32+vresult_a4, rinp, a4_offset
        stxvd2x 32+vresult_b4, rinp, b4_offset
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the original
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
        stxvd2x 0, 0, dup_rinp
        stxvd2x 1, 10, dup_rinp
        stxvd2x 2, 11, dup_rinp
        stxvd2x 3, 12, dup_rinp
        stxvd2x 4, 15, dup_rinp
        stxvd2x 5, 16, dup_rinp
        stxvd2x 6, 17, dup_rinp
        stxvd2x 7, 18, dup_rinp
.endm

/*
 * Transpose the final coefficients of 2-2-2-2 layout to the original
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
        stxvd2x 32+10, 0, dup_rinp
        stxvd2x 32+11, 10, dup_rinp
        stxvd2x 32+12, 11, dup_rinp
        stxvd2x 32+13, 12, dup_rinp
        stxvd2x 32+14, 15, dup_rinp
        stxvd2x 32+15, 16, dup_rinp
        stxvd2x 32+16, 17, dup_rinp
        stxvd2x 32+17, 18, dup_rinp
.endm

.macro Load_next_4zetas
        li      10, 16
        li      11, 32
        li      12, 48
        lxvd2x  32+V_Z0, 0, zeta_inp
        lxvd2x  32+V_Z1, 10, zeta_inp
        lxvd2x  32+V_Z2, 11, zeta_inp
        lxvd2x  32+V_Z3, 12, zeta_inp
        lxvd2x  32+V_ZT0, 0, zeta_tw_inp
        lxvd2x  32+V_ZT1, 10, zeta_tw_inp
        lxvd2x  32+V_ZT2, 11, zeta_tw_inp
        lxvd2x  32+V_ZT3, 12, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 64
        addi    zeta_tw_inp, zeta_tw_inp, 64
.endm

/*
 * NTT layer 7, Len=2.
 */
.macro ntt_layer7
        Load_next_4zetas
        Load_L24Coeffs
        barrett_fqmul_4x V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        PermWriteL24
        addi    dup_rinp, dup_rinp, 128
.endm

/*
 * NTT layer 6, Len=4.
 */
.macro ntt_layer6
        Load_next_4zetas
        Load_L44Coeffs
        barrett_fqmul_4x V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        PermWriteL44
        addi    dup_rinp, dup_rinp, 128
.endm

/*
 * NTT other layers, 1, 2, 3, 4, 5.
 */
.macro ntt_layer12345 start, next, _vz0, _vz1, _vz2, _vz3, _vzt0, _vzt1, _vzt2, _vzt3
        Load_4Coeffs \start, \next
        barrett_fqmul_4x \_vz0, \_vz1, \_vz2, \_vz3, \_vzt0, \_vzt1, \_vzt2, \_vzt3
        Load_4Rj
        Compute_4Coeffs
        Write_One
.endm

/*
 * mlk_ntt_ppc_asm(int16_t *r, int16_t *qdata)
 *   Compute forward NTT based on the following 7 layers -
 *     len = 128, 64, 32, 16, 8, 4, 2.
 *
 *   Each layer compute the coefficients on 2 legs, start and start + len*2 offsets.
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
 *   The resulting coefficients then store back to each leg's offset.
 *
 *   Each vector has the same corresponding zeta except len=4 and len=2.
 *
 *   len=4 has 4-4 layout which means every 4 16-bit coefficients has the same zeta.
 *   and len=2 has 2-2-2-2 layout which means every 2 16-bit coefficients has the same zeta.
 *   e.g.
 *         coeff vector    a1   a2   a3  a4  a5  a6  a7  a8
 *         zeta  vector    z1   z1   z2  z2  z3  z3  z4  z4
 *
 *   For len=4 and len=2, each vector will get permuted to leg1 and leg2. Zeta is
 *   pre-arranged for the leg1 and leg2.  After the computation, each vector needs
 *   to transpose back to its original 4-4 or 2-2-2-2 layout. 
 *
 */
.global MLK_ASM_NAMESPACE(ntt_ppc_asm)
.balign 16
MLK_ASM_FN_SYMBOL(ntt_ppc_asm)

        SAVE_REGS

        /* load -MLKEM_Q */
        lvx     V_NMKQ,0,qinp

        /* zeta_inp: regular Barrett roots; zeta_tw_inp: twisted roots */
        addi    zeta_inp, qinp, MLK_PPC_ZETA_NTT_OFFSET
        addi    zeta_tw_inp, qinp, MLK_PPC_ZETA_NTT_TW_OFFSET

        vxor    V_ZERO, V_ZERO, V_ZERO

.balign 16
        /*
         * Layer 1. len = 128, start= 0, 64, 128, 192
         */
        li      len_2, 256          /* len * 2 */
        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16

        ntt_layer12345 0, 16,   V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        ntt_layer12345 64, 16,  V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        ntt_layer12345 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        ntt_layer12345 192, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

.balign 16
        /*
         * Layer 2. len = 64, start= 0, 64, 256, 320
         */
        li      len_2, 128
        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        ntt_layer12345 0, 16,  V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        ntt_layer12345 64, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        ntt_layer12345 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        ntt_layer12345 320, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

.balign 16
        /*
         * Layer 3. len = 32, start = 0, 128, 256, 384
         */
        li      len_2, 64
        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        ntt_layer12345 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        ntt_layer12345 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        ntt_layer12345 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        ntt_layer12345 384, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

.balign 16
        /*
         * Layer 4. len = 16, start = 0, 16, 256, 272
         */
        li      len_2, 32
        Load_next_4zetas
        ntt_layer12345 0, 64,  V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        ntt_layer12345 16, 64, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        ntt_layer12345 256, 64, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        ntt_layer12345 272, 64, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

.balign 16
        /*
         * Layer 5. len = 8, start= 0, 128, 256, 384
         */
        li      len_2, 16
        Load_next_4zetas
        ntt_layer12345 0, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        ntt_layer12345 128, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        ntt_layer12345 256, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        ntt_layer12345 384, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        /*
         * Layer 6. len = 4,
         *     leg1 offset - 0, 32, 64, 96
         *     leg2 offset - 16, 48, 80, 112
         *
         *    Load zeta vectors in 4-4 layout
         */
        mr      dup_rinp, rinp                 /* Let r5 points to coefficient array */
        li      len_2, 8

        li      10, 16
        li      11, 32
        li      12, 48
        li      15, 64
        li      16, 80
        li      17, 96
        li      18, 112

.balign 16
        ntt_layer6
        ntt_layer6
        ntt_layer6
        ntt_layer6

        /*
         * Layer 7. len = 2
         *     leg1 offset - 0, 32, 64, 96
         *     leg2 offset - 16, 48, 80, 112
         *
         *    Load zeta vectors in 2-2-2-2 layout
         */
        mr      dup_rinp, rinp                  /* Let r5 points to coefficient array */
        li      len_2, 4

.balign 16
        ntt_layer7
        ntt_layer7
        ntt_layer7
        ntt_layer7

        RESTORE_REGS
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V_ZERO
#undef V_NMKQ
#undef V_Z0
#undef V_Z1
#undef V_Z2
#undef V_Z3
#undef V_ZETA
#undef V_ZT0
#undef V_ZT1
#undef V_ZT2
#undef V_ZT3
#undef V_ZETATW
#undef vdata_a1
#undef vdata_a2
#undef vdata_a3
#undef vdata_a4
#undef vdata_b1
#undef vdata_b2
#undef vdata_b3
#undef vdata_b4
#undef vresult_a1
#undef vresult_b1
#undef vresult_a2
#undef vresult_b2
#undef vresult_a3
#undef vresult_b3
#undef vresult_a4
#undef vresult_b4
#undef rinp
#undef dup_rinp
#undef qinp
#undef len_2
#undef zeta_inp
#undef zeta_tw_inp
#undef a1_offset
#undef a2_offset
#undef a3_offset
#undef a4_offset
#undef b1_offset
#undef b2_offset
#undef b3_offset
#undef b4_offset

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */
