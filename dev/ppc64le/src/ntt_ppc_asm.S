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

.macro mulmod_2x dst0, dst1, src0, src1, z0, zt0, z1, zt1, t0, t1
        vmhraddshs \t0, \src0, \zt0, rinp
        vmhraddshs \t1, \src1, \zt1, rinp
        vmladduhm  \dst0, \src0, \z0,  rinp
        vmladduhm  \dst1, \src1, \z1,  rinp
        vmladduhm  \dst0, \t0, V_NMKQ, \dst0
        vmladduhm  \dst1, \t1, V_NMKQ, \dst1
.endm

.macro ct_butterfly_2x a0, b0, a1, b1, z0, zt0, z1, zt1, m0, m1, t0, t1
        mulmod_2x \m0, \m1, \b0, \b1, \z0, \zt0, \z1, \zt1, \t0, \t1
        vsubuhm \b0, \a0, \m0
        vsubuhm \b1, \a1, \m1
        vadduhm \a0, \a0, \m0
        vadduhm \a1, \a1, \m1
.endm

.macro mulmod_4x dst0, dst1, dst2, dst3, src0, src1, src2, src3, z0, zt0, z1, zt1, z2, zt2, z3, zt3, t0, t1, t2, t3
        vmhraddshs \t0, \src0, \zt0, rinp
        vmhraddshs \t1, \src1, \zt1, rinp
        vmhraddshs \t2, \src2, \zt2, rinp
        vmhraddshs \t3, \src3, \zt3, rinp
        vmladduhm  \dst0, \src0, \z0,  rinp
        vmladduhm  \dst1, \src1, \z1,  rinp
        vmladduhm  \dst2, \src2, \z2,  rinp
        vmladduhm  \dst3, \src3, \z3,  rinp
        vmladduhm  \dst0, \t0, V_NMKQ, \dst0
        vmladduhm  \dst1, \t1, V_NMKQ, \dst1
        vmladduhm  \dst2, \t2, V_NMKQ, \dst2
        vmladduhm  \dst3, \t3, V_NMKQ, \dst3
.endm

.macro ct_butterfly_4x a0, b0, a1, b1, a2, b2, a3, b3, z0, zt0, z1, zt1, z2, zt2, z3, zt3, m0, m1, m2, m3, t0, t1, t2, t3
        mulmod_4x \m0, \m1, \m2, \m3, \b0, \b1, \b2, \b3, \z0, \zt0, \z1, \zt1, \z2, \zt2, \z3, \zt3, \t0, \t1, \t2, \t3
        vsubuhm \b0, \a0, \m0
        vsubuhm \b1, \a1, \m1
        vsubuhm \b2, \a2, \m2
        vsubuhm \b3, \a3, \m3
        vadduhm \a0, \a0, \m0
        vadduhm \a1, \a1, \m1
        vadduhm \a2, \a2, \m2
        vadduhm \a3, \a3, \m3
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

        ct_butterfly_4x d0, d4, d1, d5, d2, d6, d3, d7, \
                        V_ZL1, V_ZL1t, V_ZL1, V_ZL1t, V_ZL1, V_ZL1t, V_ZL1, V_ZL1t, \
                        21, 26, 30, 31, 15, 16, 20, 25

        ct_butterfly_4x d0, d2, d1, d3, d4, d6, d5, d7, \
                        V_ZL2a, V_ZL2at, V_ZL2a, V_ZL2at, V_ZL2b, V_ZL2bt, V_ZL2b, V_ZL2bt, \
                        21, 26, 30, 31, 15, 16, 20, 25

        ct_butterfly_4x d0, d1, d2, d3, d4, d5, d6, d7, \
                        V_ZL3a, V_ZL3at, V_ZL3b, V_ZL3bt, V_ZL3c, V_ZL3ct, V_ZL3d, V_ZL3dt, \
                        21, 26, 30, 31, 15, 16, 20, 25

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

#define off96  5
#define off112 7
        li      off96,  4
        mtctr   off96

        li      16, 64
        li      17, 80
        li      off96,  96
        li      off112, 112

#define z4a   0
#define z4at  1
#define z4b   2
#define z4bt  4
#define z5a   7
#define z5at  8
#define z5b   9
#define z5bt  10
#define z5c   11
#define z5ct  14
#define z5d   19
#define z5dt  24

ntt_ppc_layer4567_start:
        lvx     d0, 9,   rinp
        lvx     d1, 10,  rinp
        lvx     d2, 11,  rinp
        lvx     d3, 12,  rinp
        lvx     d4, 16,  rinp
        lvx     d5, 17,  rinp
        lvx     d6, off96,  rinp
        lvx     d7, off112, rinp

        // Layer 4: 4 butterflies with 2 broadcast zetas (block A and block B)
        lvx     z4a,  0,  zeta_inp
        lvx     z4at, 0,  zeta_tw_inp
        lvx     z4b,  10, zeta_inp
        lvx     z4bt, 10, zeta_tw_inp
        addi    zeta_inp,    zeta_inp,    32
        addi    zeta_tw_inp, zeta_tw_inp, 32

        ct_butterfly_4x d0, d2, d1, d3, d4, d6, d5, d7, \
                        z4a, z4at, z4a, z4at, z4b, z4bt, z4b, z4bt, \
                        21, 26, 30, 31, 15, 16, 20, 25

        // Layer 5: 4 butterflies, 4 distinct broadcast zetas
        lvx     z5a,  0,  zeta_l5_ptr
        lvx     z5at, 0,  zeta_l5_tw_ptr
        lvx     z5b,  10, zeta_l5_ptr
        lvx     z5bt, 10, zeta_l5_tw_ptr
        lvx     z5c,  11, zeta_l5_ptr
        lvx     z5ct, 11, zeta_l5_tw_ptr
        lvx     z5d,  12, zeta_l5_ptr
        lvx     z5dt, 12, zeta_l5_tw_ptr
        addi    zeta_l5_ptr,    zeta_l5_ptr,    64
        addi    zeta_l5_tw_ptr, zeta_l5_tw_ptr, 64

        ct_butterfly_4x d0, d1, d2, d3, d4, d5, d6, d7, \
                        z5a, z5at, z5b, z5bt, z5c, z5ct, z5d, z5dt, \
                        21, 26, 30, 31, 15, 16, 20, 25

        // transpose4 each 4-vec block independently
        transpose4 d0, d1, d2, d3, z4a, z4at, z4b, z4bt
        transpose4 d4, d5, d6, d7, z5a, z5at, z5b, z5bt

        // Layer 6: 4 butterflies, 2 root0 vectors (one per block)
        lvx     z4a,  0,  zeta_l67_ptr      // root0 block A
        lvx     z4at, 10, zeta_l67_ptr      // root0_tw block A
        lvx     z4b,  off96, zeta_l67_ptr   // root0 block B (offset 96 = block-B start)
        lvx     z4bt, off112, zeta_l67_ptr  // root0_tw block B
        ct_butterfly_4x d0, d2, d1, d3, d4, d6, d5, d7, \
                        z4a, z4at, z4a, z4at, z4b, z4bt, z4b, z4bt, \
                        21, 26, 30, 31, 15, 16, 20, 25

        // Layer 7: 4 butterflies, 4 distinct root vectors (root1/2 for each block)
        lvx     z5a,  11, zeta_l67_ptr   // root1 block A (offset 32)
        lvx     z5at, 12, zeta_l67_ptr   // root1_tw block A (offset 48)
        lvx     z5b,  16, zeta_l67_ptr   // root2 block A (offset 64)
        lvx     z5bt, 17, zeta_l67_ptr   // root2_tw block A (offset 80)
        addi    zeta_l67_ptr, zeta_l67_ptr, 96
        lvx     z5c,  11, zeta_l67_ptr   // root1 block B
        lvx     z5ct, 12, zeta_l67_ptr   // root1_tw block B
        lvx     z5d,  16, zeta_l67_ptr   // root2 block B
        lvx     z5dt, 17, zeta_l67_ptr   // root2_tw block B
        addi    zeta_l67_ptr, zeta_l67_ptr, 96

        ct_butterfly_4x d0, d1, d2, d3, d4, d5, d6, d7, \
                        z5a, z5at, z5b, z5bt, z5c, z5ct, z5d, z5dt, \
                        21, 26, 30, 31, 15, 16, 20, 25

        transpose4 d0, d1, d2, d3, z4a, z4at, z4b, z4bt
        transpose4 d4, d5, d6, d7, z5a, z5at, z5b, z5bt

        stvx    d0, 9,   rinp
        stvx    d1, 10,  rinp
        stvx    d2, 11,  rinp
        stvx    d3, 12,  rinp
        stvx    d4, 16,  rinp
        stvx    d5, 17,  rinp
        stvx    d6, off96,  rinp
        stvx    d7, off112, rinp

        addi    rinp, rinp, 128
        bdnz    ntt_ppc_layer4567_start

        addi    rinp, rinp, -512

#undef off96
#undef off112
#undef z4a
#undef z4at
#undef z4b
#undef z4bt
#undef z5a
#undef z5at
#undef z5b
#undef z5bt
#undef z5c
#undef z5ct
#undef z5d
#undef z5dt

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
#undef off96
#undef off112
#undef z4a
#undef z4at
#undef z4b
#undef z4bt
#undef z5a
#undef z5at
#undef z5b
#undef z5bt
#undef z5c
#undef z5ct
#undef z5d
#undef z5dt

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */
