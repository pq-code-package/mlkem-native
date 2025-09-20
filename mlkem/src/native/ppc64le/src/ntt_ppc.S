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
        stxv 52, 128(1)
        stxv 53, 144(1)
        stxv 54, 160(1)
        stxv 55, 176(1)
        stxv 56, 192(1)
        stxv 57, 208(1)
        stxv 58, 224(1)
        stxv 59, 240(1)
        stxv 60, 256(1)
        stxv 61, 272(1)
        stxv 62, 288(1)
        stxv 63, 304(1)
        lvx 5, 0, 4
        addi 14, 4, 96
        vxor 3, 3, 3
        vspltish 4, 1
        lxv 34, 16(4)
        ori 2, 2, 0
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
        nop
        nop
        ori 2, 2, 0
        li 5, 0
        li 7, 32
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
        ori 2, 2, 0
        li 5, 0
        li 7, 16
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
        li 5, 128
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
        li 5, 256
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
        li 5, 384
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        stxvx 47, 3, 9
        stxvx 48, 3, 10
        stxvx 52, 3, 16
        stxvx 53, 3, 17
        stxvx 57, 3, 18
        stxvx 58, 3, 19
        stxvx 62, 3, 20
        stxvx 63, 3, 21
        li 15, 4
        mtctr 15
        li 5, 0
        li 7, 8
        nop
        nop
        ori 2, 2, 0

Lntt_ppc__Len4:
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        xxmrgld	49, 48, 47
        xxmrgld	54, 53, 52
        xxmrgld	59, 58, 57
        xxmrgld	61, 63, 62
        stxvx 49, 3, 9
        stxvx 54, 3, 16
        stxvx 59, 3, 18
        stxvx 61, 3, 20
        addi 5, 5, 64
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        xxmrgld	49, 48, 47
        xxmrgld	54, 53, 52
        xxmrgld	59, 58, 57
        xxmrgld	61, 63, 62
        stxvx 49, 3, 9
        stxvx 54, 3, 16
        stxvx 59, 3, 18
        stxvx 61, 3, 20
        addi 5, 5, 64
        bdnz Lntt_ppc__Len4
        addi 14, 4, 1104
        li 15, 4
        mtctr 15
        li 5, 0
        li 7, 4
        nop
        ori 2, 2, 0

Lntt_ppc__Len2:
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        xxmrglw 46, 48, 47
        xxmrghw 45, 48, 47
        xxmrgld	49, 45, 46
        xxmrglw 51, 53, 52
        xxmrghw 50, 53, 52
        xxmrgld	54, 50, 51
        xxmrglw 46, 58, 57
        xxmrghw 45, 58, 57
        xxmrgld	59, 45, 46
        xxmrglw 56, 63, 62
        xxmrghw 55, 63, 62
        xxmrgld	61, 55, 56
        stxvx 49, 3, 9
        stxvx 54, 3, 16
        stxvx 59, 3, 18
        stxvx 61, 3, 20
        addi 5, 5, 64
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
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
        xxswapd	45, 45
        xxswapd	50, 50
        xxswapd	55, 55
        xxswapd	60, 60
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
        xxswapd	44, 44
        xxswapd	49, 49
        xxswapd	54, 54
        xxswapd	59, 59
        vsubuhm 16, 12, 13
        vadduhm 15, 13, 12
        vsubuhm 21, 17, 18
        vadduhm 20, 18, 17
        vsubuhm 26, 22, 23
        vadduhm 25, 23, 22
        vsubuhm 31, 27, 28
        vadduhm 30, 28, 27
        xxmrglw 46, 48, 47
        xxmrghw 45, 48, 47
        xxmrgld	49, 45, 46
        xxmrglw 51, 53, 52
        xxmrghw 50, 53, 52
        xxmrgld	54, 50, 51
        xxmrglw 46, 58, 57
        xxmrghw 45, 58, 57
        xxmrgld	59, 45, 46
        xxmrglw 56, 63, 62
        xxmrghw 55, 63, 62
        xxmrgld	61, 55, 56
        stxvx 49, 3, 9
        stxvx 54, 3, 16
        stxvx 59, 3, 18
        stxvx 61, 3, 20
        addi 5, 5, 64
        bdnz Lntt_ppc__Len2
        lxv 52, 128(1)
        lxv 53, 144(1)
        lxv 54, 160(1)
        lxv 55, 176(1)
        lxv 56, 192(1)
        lxv 57, 208(1)
        lxv 58, 224(1)
        lxv 59, 240(1)
        lxv 60, 256(1)
        lxv 61, 272(1)
        lxv 62, 288(1)
        lxv 63, 304(1)
        ld 14, 56(1)
        ld 15, 64(1)
        ld 16, 72(1)
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
