/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Copyright 2025- IBM Corp.
 *
 *===================================================================================
 * Written by Danny Tsen <dtsen@us.ibm.com>
 *
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/ppc64le/src/ntt_ppc.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 16
.global MLK_ASM_NAMESPACE(ntt_ppc)
MLK_ASM_FN_SYMBOL(ntt_ppc)

        .cfi_startproc
        stdu 1, -352(1)
        mflr 0
        std 14, 56(1)
        std 15, 64(1)
        std 16, 72(1)
        std 17, 80(1)
        std 18, 88(1)
        std 19, 96(1)
        std 20, 104(1)
        std 21, 112(1)
        li 10, 128
        li 11, 144
        li 12, 160
        li 14, 176
        li 15, 192
        li 16, 208
        stxvx 52, 10, 1
        stxvx 53, 11, 1
        stxvx 54, 12, 1
        stxvx 55, 14, 1
        stxvx 56, 15, 1
        stxvx 57, 16, 1
        li 10, 224
        li 11, 240
        li 12, 256
        li 14, 272
        li 15, 288
        li 16, 304
        stxvx 58, 10, 1
        stxvx 59, 11, 1
        stxvx 60, 12, 1
        stxvx 61, 14, 1
        stxvx 62, 15, 1
        stxvx 63, 16, 1
        lvx 5, 0, 4
        addi 14, 4, 96
        vxor 3, 3, 3
        vspltish 4, 1
        li 10, 16
        lvx 2, 10, 4
        li 5, 0
        li 7, 256
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 128
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 192
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        ori 2, 2, 0
        li 5, 0
        li 7, 128
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 256
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 320
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        nop
        nop
        ori 2, 2, 0
        li 5, 0
        li 7, 64
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 128
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 256
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 384
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 10, 3
        vmladduhm 20, 18, 10, 3
        vmladduhm 25, 23, 10, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 10, 3
        vmhraddshs 19, 18, 10, 3
        vmhraddshs 24, 23, 10, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        nop
        nop
        ori 2, 2, 0
        li 5, 0
        li 7, 32
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        li 5, 256
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 272
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        nop
        nop
        ori 2, 2, 0
        li 5, 0
        li 7, 16
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 128
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 256
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 384
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 45, 3, 10
        lxvd2x 50, 3, 17
        lxvd2x 55, 3, 19
        lxvd2x 60, 3, 21
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        lxvd2x 44, 3, 9
        lxvd2x 49, 3, 16
        lxvd2x 54, 3, 18
        lxvd2x 59, 3, 20
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 15, 4
        mtctr 15
        mr	5, 3
        li 7, 8
        li 10, 16
        li 11, 32
        li 12, 48
        li 15, 64
        li 16, 80
        li 17, 96
        li 18, 112

Lntt_ppc__Len4:
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        xxswapd	39, 39
        xxswapd	40, 40
        xxswapd	41, 41
        xxswapd	42, 42
        lxvd2x 1, 0, 5
        lxvd2x 2, 10, 5
        xxmrgld	45, 2, 1
        xxmrghd	44, 2, 1
        lxvd2x 3, 11, 5
        lxvd2x 4, 12, 5
        xxmrgld	50, 4, 3
        xxmrghd	49, 4, 3
        lxvd2x 1, 15, 5
        lxvd2x 2, 16, 5
        xxmrgld	55, 2, 1
        xxmrghd	54, 2, 1
        lxvd2x 3, 17, 5
        lxvd2x 4, 18, 5
        xxmrgld	60, 4, 3
        xxmrghd	59, 4, 3
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        xxmrgld	0, 47, 48
        xxmrghd	1, 47, 48
        xxmrgld	2, 52, 53
        xxmrghd	3, 52, 53
        xxmrgld	4, 57, 58
        xxmrghd	5, 57, 58
        xxmrgld	6, 62, 63
        xxmrghd	7, 62, 63
        stxvd2x 0, 0, 5
        stxvd2x 1, 10, 5
        stxvd2x 2, 11, 5
        stxvd2x 3, 12, 5
        stxvd2x 4, 15, 5
        stxvd2x 5, 16, 5
        stxvd2x 6, 17, 5
        stxvd2x 7, 18, 5
        addi 5, 5, 128
        bdnz Lntt_ppc__Len4
        li 8, 4
        mtctr 8
        mr	5, 3
        li 7, 4
        nop
        ori 2, 2, 0

Lntt_ppc__Len2:
        li 10, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 10, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        lxvd2x 57, 0, 5
        lxvd2x 58, 10, 5
        vmrgew 13, 25, 26
        vmrgow 12, 25, 26
        lxvd2x 57, 11, 5
        lxvd2x 58, 12, 5
        vmrgew 18, 25, 26
        vmrgow 17, 25, 26
        lxvd2x 57, 15, 5
        lxvd2x 58, 16, 5
        vmrgew 23, 25, 26
        vmrgow 22, 25, 26
        lxvd2x 57, 17, 5
        lxvd2x 58, 18, 5
        vmrgew 28, 25, 26
        vmrgow 27, 25, 26
        vmladduhm 15, 13, 7, 3
        vmladduhm 20, 18, 8, 3
        vmladduhm 25, 23, 9, 3
        vmladduhm 30, 28, 10, 3
        vmhraddshs 14, 13, 7, 3
        vmhraddshs 19, 18, 8, 3
        vmhraddshs 24, 23, 9, 3
        vmhraddshs 29, 28, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 30, 30, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        vmrgew 10, 16, 15
        vmrgow 11, 16, 15
        vmrgew 12, 21, 20
        vmrgow 13, 21, 20
        vmrgew 14, 26, 25
        vmrgow 15, 26, 25
        vmrgew 16, 31, 30
        vmrgow 17, 31, 30
        stxvd2x 42, 0, 5
        stxvd2x 43, 10, 5
        stxvd2x 44, 11, 5
        stxvd2x 45, 12, 5
        stxvd2x 46, 15, 5
        stxvd2x 47, 16, 5
        stxvd2x 48, 17, 5
        stxvd2x 49, 18, 5
        addi 5, 5, 128
        bdnz Lntt_ppc__Len2
        li 10, 128
        li 11, 144
        li 12, 160
        li 14, 176
        li 15, 192
        li 16, 208
        lxvx 52, 10, 1
        lxvx 53, 11, 1
        lxvx 54, 12, 1
        lxvx 55, 14, 1
        lxvx 56, 15, 1
        lxvx 57, 16, 1
        li 10, 224
        li 11, 240
        li 12, 256
        li 14, 272
        li 15, 288
        li 16, 304
        lxvx 58, 10, 1
        lxvx 59, 11, 1
        lxvx 60, 12, 1
        lxvx 61, 14, 1
        lxvx 62, 15, 1
        lxvx 63, 16, 1
        ld 14, 56(1)
        ld 15, 64(1)
        ld 16, 72(1)
        ld 17, 80(1)
        ld 18, 88(1)
        ld 19, 96(1)
        ld 20, 104(1)
        ld 21, 112(1)
        mtlr 0
        addi 1, 1, 352
        blr
        .cfi_endproc

#endif /* MLK_ARITH_BACKEND_PPC64LE && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
