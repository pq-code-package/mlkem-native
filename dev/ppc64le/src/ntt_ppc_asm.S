/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * Copyright IBM Corp. 2025, 2026
 *
 * Written by Danny Tsen <dtsen@us.ibm.com>
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && defined(__POWER8_VECTOR__)
/* simpasm: header-end */

#include "consts.h"

#define V_NMKQ  5

#define V_ZL1    0
#define V_ZL1t   1
#define V_ZL2a   2
#define V_ZL2at  4
#define V_ZL2b   6
#define V_ZL2bt  11

#define V_ZL3a   7
#define V_ZL3at  8
#define V_ZL3b   9
#define V_ZL3bt  10
#define V_ZL3c   14
#define V_ZL3ct  19
#define V_ZL3d   24
#define V_ZL3dt  29

#define V_ZL4    0
#define V_ZL4t   1
#define V_ZL5a   2
#define V_ZL5at  4
#define V_ZL5b   6
#define V_ZL5bt  11

#define d0 12
#define d1 13
#define d2 17
#define d3 18
#define d4 22
#define d5 23
#define d6 27
#define d7 28

#define rinp        3
#define qinp        4
#define zeta_inp    14
#define zeta_tw_inp 8

.text

.macro push_stack
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

.macro pop_stack
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

.macro mulmod dst, src, z, zt
        vmhraddshs 15, \src, \zt, rinp
        vmladduhm  \dst, \src, \z, rinp
        vmladduhm  \dst, 15, V_NMKQ, \dst
.endm

.macro ct_butterfly a, b, z, zt
        mulmod 16, \b, \z, \zt
        vsubuhm \b, \a, 16
        vadduhm \a, \a, 16
.endm

.macro transpose4 data0, data1, data2, data3, t0, t1, t2, t3
        vmrgew  \t0, \data1, \data0
        vmrgow  \t1, \data1, \data0
        vmrgew  \t2, \data3, \data2
        vmrgow  \t3, \data3, \data2

        xxpermdi 32+\data0, 32+\t3, 32+\t1, 3
        xxpermdi 32+\data1, 32+\t2, 32+\t0, 3
        xxpermdi 32+\data2, 32+\t3, 32+\t1, 0
        xxpermdi 32+\data3, 32+\t2, 32+\t0, 0
.endm

.global MLK_ASM_NAMESPACE(ntt_ppc_asm)
.balign 16
MLK_ASM_FN_SYMBOL(ntt_ppc_asm)

        push_stack

        lvx     V_NMKQ, 0, qinp

        addi    zeta_inp,    qinp, MLK_PPC_ZETA_NTT_OFFSET
        addi    zeta_tw_inp, qinp, MLK_PPC_ZETA_NTT_TW_OFFSET

        vxor    3, 3, 3

        lvx     V_ZL1,    0,  zeta_inp
        lvx     V_ZL1t,   0,  zeta_tw_inp
        li      10, 16
        lvx     V_ZL2a,   10, zeta_inp
        lvx     V_ZL2at,  10, zeta_tw_inp
        li      11, 32
        lvx     V_ZL2b,   11, zeta_inp
        lvx     V_ZL2bt,  11, zeta_tw_inp
        li      12, 48
        lvx     V_ZL3a,   12, zeta_inp
        lvx     V_ZL3at,  12, zeta_tw_inp
        li      10, 64
        lvx     V_ZL3b,   10, zeta_inp
        lvx     V_ZL3bt,  10, zeta_tw_inp
        li      11, 80
        lvx     V_ZL3c,   11, zeta_inp
        lvx     V_ZL3ct,  11, zeta_tw_inp
        li      12, 96
        lvx     V_ZL3d,   12, zeta_inp
        lvx     V_ZL3dt,  12, zeta_tw_inp
        addi    zeta_inp,    zeta_inp,    112
        addi    zeta_tw_inp, zeta_tw_inp, 112

        li      9,  0
        li      10, 64
        li      11, 128
        li      12, 192
        li      16, 256
        li      17, 320
        li      18, 384
        li      19, 448

        li      6,  4
        mtctr   6

ntt_ppc_layer123_start:
        lxvd2x  32+d0, 9,  rinp
        lxvd2x  32+d1, 10, rinp
        lxvd2x  32+d2, 11, rinp
        lxvd2x  32+d3, 12, rinp
        lxvd2x  32+d4, 16, rinp
        lxvd2x  32+d5, 17, rinp
        lxvd2x  32+d6, 18, rinp
        lxvd2x  32+d7, 19, rinp

        ct_butterfly d0, d4, V_ZL1, V_ZL1t
        ct_butterfly d1, d5, V_ZL1, V_ZL1t
        ct_butterfly d2, d6, V_ZL1, V_ZL1t
        ct_butterfly d3, d7, V_ZL1, V_ZL1t

        ct_butterfly d0, d2, V_ZL2a, V_ZL2at
        ct_butterfly d1, d3, V_ZL2a, V_ZL2at
        ct_butterfly d4, d6, V_ZL2b, V_ZL2bt
        ct_butterfly d5, d7, V_ZL2b, V_ZL2bt

        ct_butterfly d0, d1, V_ZL3a, V_ZL3at
        ct_butterfly d2, d3, V_ZL3b, V_ZL3bt
        ct_butterfly d4, d5, V_ZL3c, V_ZL3ct
        ct_butterfly d6, d7, V_ZL3d, V_ZL3dt

        stxvd2x 32+d0, 9,  rinp
        stxvd2x 32+d1, 10, rinp
        stxvd2x 32+d2, 11, rinp
        stxvd2x 32+d3, 12, rinp
        stxvd2x 32+d4, 16, rinp
        stxvd2x 32+d5, 17, rinp
        stxvd2x 32+d6, 18, rinp
        stxvd2x 32+d7, 19, rinp

        addi    rinp, rinp, 16
        bdnz    ntt_ppc_layer123_start

        addi    rinp, rinp, -64

#define zeta_l5_ptr    6
#define zeta_l5_tw_ptr 20
#define zeta_l67_ptr   15

        addi    zeta_l5_ptr,    zeta_inp,    128
        addi    zeta_l5_tw_ptr, zeta_tw_inp, 128
        addi    zeta_l67_ptr,   qinp,        MLK_PPC_ZETA_NTT_LAYER67_OFFSET

        li      9,  0
        li      10, 16
        li      11, 32
        li      12, 48

        li      16, 8
        mtctr   16

        li      16, 64
        li      17, 80

ntt_ppc_layer4567_start:
        lvx     d0, 9,  rinp
        lvx     d1, 10, rinp
        lvx     d2, 11, rinp
        lvx     d3, 12, rinp

        lvx     V_ZL4,   0,  zeta_inp
        lvx     V_ZL4t,  0,  zeta_tw_inp
        lvx     V_ZL5a,  0,  zeta_l5_ptr
        lvx     V_ZL5at, 0,  zeta_l5_tw_ptr
        lvx     V_ZL5b,  10, zeta_l5_ptr
        lvx     V_ZL5bt, 10, zeta_l5_tw_ptr

        addi    zeta_inp,       zeta_inp,       16
        addi    zeta_tw_inp,    zeta_tw_inp,    16
        addi    zeta_l5_ptr,    zeta_l5_ptr,    32
        addi    zeta_l5_tw_ptr, zeta_l5_tw_ptr, 32

        ct_butterfly d0, d2, V_ZL4, V_ZL4t
        ct_butterfly d1, d3, V_ZL4, V_ZL4t

        ct_butterfly d0, d1, V_ZL5a, V_ZL5at
        ct_butterfly d2, d3, V_ZL5b, V_ZL5bt

        transpose4 d0, d1, d2, d3, 22, 23, 27, 28

        lvx     V_ZL4,   0,  zeta_l67_ptr
        lvx     V_ZL4t,  10, zeta_l67_ptr
        lvx     V_ZL5a,  11, zeta_l67_ptr
        lvx     V_ZL5at, 12, zeta_l67_ptr
        lvx     V_ZL5b,  16, zeta_l67_ptr
        lvx     V_ZL5bt, 17, zeta_l67_ptr

        addi    zeta_l67_ptr, zeta_l67_ptr, 96

        ct_butterfly d0, d2, V_ZL4,  V_ZL4t
        ct_butterfly d1, d3, V_ZL4,  V_ZL4t

        ct_butterfly d0, d1, V_ZL5a, V_ZL5at
        ct_butterfly d2, d3, V_ZL5b, V_ZL5bt

        transpose4 d0, d1, d2, d3, 22, 23, 27, 28

        stvx    d0, 9,  rinp
        stvx    d1, 10, rinp
        stvx    d2, 11, rinp
        stvx    d3, 12, rinp

        addi    rinp, rinp, 64
        bdnz    ntt_ppc_layer4567_start

        addi    rinp, rinp, -512

#undef zeta_l5_ptr
#undef zeta_l5_tw_ptr
#undef zeta_l67_ptr

        pop_stack
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V_NMKQ
#undef V_ZL1
#undef V_ZL1t
#undef V_ZL2a
#undef V_ZL2at
#undef V_ZL2b
#undef V_ZL2bt
#undef V_ZL3a
#undef V_ZL3at
#undef V_ZL3b
#undef V_ZL3bt
#undef V_ZL3c
#undef V_ZL3ct
#undef V_ZL3d
#undef V_ZL3dt
#undef V_ZL4
#undef V_ZL4t
#undef V_ZL5a
#undef V_ZL5at
#undef V_ZL5b
#undef V_ZL5bt
#undef d0
#undef d1
#undef d2
#undef d3
#undef d4
#undef d5
#undef d6
#undef d7
#undef rinp
#undef qinp
#undef zeta_inp
#undef zeta_tw_inp
#undef zeta_l5_ptr
#undef zeta_l5_tw_ptr
#undef zeta_l67_ptr

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */
