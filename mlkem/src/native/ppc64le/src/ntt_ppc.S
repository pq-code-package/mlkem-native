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
#if defined(MLK_ARITH_BACKEND_PPC64LE)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/ppc64le/src/ntt_ppc.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
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
        addis 8, 2, 0
        addi 8, 8, 0
        lvx 5, 0, 8
        addis 14, 2, 0
        addi 14, 14, 0
        vxor 3, 3, 3
        vspltish 4, 1
        lxv 34, 16(8)

Lntt_ppc_Len128:
        li 5, 0
        li 4, 256
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 4, 9
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
        add 10, 4, 9
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
        add 10, 4, 9
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
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21

Lntt_ppc_Len64:
        li 5, 0
        li 4, 128
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 4, 9
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
        add 10, 4, 9
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
        add 10, 4, 9
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
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21

Lntt_ppc_Len32:
        li 5, 0
        li 4, 64
        lvx 10, 0, 14
        addi 14, 14, 16
        mr	9, 5
        add 10, 4, 9
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
        add 10, 4, 9
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
        add 10, 4, 9
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
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21

Lntt_ppc_Len16:
        li 5, 0
        li 4, 32
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        li 5, 256
        mr	9, 5
        add 10, 4, 9
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
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21

Lntt_ppc_Len8:
        li 5, 0
        li 4, 16
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 128
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 256
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 47, 3, 9
        stxvd2x 48, 3, 10
        stxvd2x 52, 3, 16
        stxvd2x 53, 3, 17
        stxvd2x 57, 3, 18
        stxvd2x 58, 3, 19
        stxvd2x 62, 3, 20
        stxvd2x 63, 3, 21
        li 5, 384
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        li 5, 0
        li 4, 8

Lntt_ppc_Len4:
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 49, 3, 9
        stxvd2x 54, 3, 16
        stxvd2x 59, 3, 18
        stxvd2x 61, 3, 20
        addi 5, 5, 64
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 49, 3, 9
        stxvd2x 54, 3, 16
        stxvd2x 59, 3, 18
        stxvd2x 61, 3, 20
        addi 5, 5, 64
        bdnz Lntt_ppc_Len4
        addis 14, 2, 0
        addi 14, 14, 0
        li 15, 4
        mtctr 15
        li 5, 0
        li 4, 4

Lntt_ppc_Len2:
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 49, 3, 9
        stxvd2x 54, 3, 16
        stxvd2x 59, 3, 18
        stxvd2x 61, 3, 20
        addi 5, 5, 64
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 49, 3, 9
        stxvd2x 54, 3, 16
        stxvd2x 59, 3, 18
        stxvd2x 61, 3, 20
        addi 5, 5, 64
        bdnz Lntt_ppc_Len2

Lntt_ppc_ntt_out:
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

.data
// -MLKEM_Q
.nmkq:
.short  -3329, -3329, -3329, -3329, -3329, -3329, -3329, -3329
// QINV
.short  -3327, -3327, -3327, -3327, -3327, -3327, -3327, -3327

// zetas
.K1:
.short -758, -758, -758, -758, -758, -758, -758, -758
.short -359, -359, -359, -359, -359, -359, -359, -359
.short -1517, -1517, -1517, -1517, -1517, -1517, -1517, -1517
.short 1493, 1493, 1493, 1493, 1493, 1493, 1493, 1493
.short 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422
.short 287, 287, 287, 287, 287, 287, 287, 287
.short 202, 202, 202, 202, 202, 202, 202, 202
.short -171, -171, -171, -171, -171, -171, -171, -171
.short 622, 622, 622, 622, 622, 622, 622, 622
.short 1577, 1577, 1577, 1577, 1577, 1577, 1577, 1577
.short 182, 182, 182, 182, 182, 182, 182, 182
.short 962, 962, 962, 962, 962, 962, 962, 962
.short -1202, -1202, -1202, -1202, -1202, -1202, -1202, -1202
.short -1474, -1474, -1474, -1474, -1474, -1474, -1474, -1474
.short 1468, 1468, 1468, 1468, 1468, 1468, 1468, 1468
.short 573, 573, 573, 573, 573, 573, 573, 573
.short -1325, -1325, -1325, -1325, -1325, -1325, -1325, -1325
.short 264, 264, 264, 264, 264, 264, 264, 264
.short 383, 383, 383, 383, 383, 383, 383, 383
.short -829, -829, -829, -829, -829, -829, -829, -829
.short 1458, 1458, 1458, 1458, 1458, 1458, 1458, 1458
.short -1602, -1602, -1602, -1602, -1602, -1602, -1602, -1602
.short -130, -130, -130, -130, -130, -130, -130, -130
.short -681, -681, -681, -681, -681, -681, -681, -681
.short 1017, 1017, 1017, 1017, 1017, 1017, 1017, 1017
.short 732, 732, 732, 732, 732, 732, 732, 732
.short 608, 608, 608, 608, 608, 608, 608, 608
.short -1542, -1542, -1542, -1542, -1542, -1542, -1542, -1542
.short 411, 411, 411, 411, 411, 411, 411, 411
.short -205, -205, -205, -205, -205, -205, -205, -205
.short -1571, -1571, -1571, -1571, -1571, -1571, -1571, -1571
.short 1223, 1223, 1223, 1223, 1223, 1223, 1223, 1223
.short 652, 652, 652, 652, 652, 652, 652, 652
.short -552, -552, -552, -552, -552, -552, -552, -552
.short 1015, 1015, 1015, 1015, 1015, 1015, 1015, 1015
.short -1293, -1293, -1293, -1293, -1293, -1293, -1293, -1293
.short 1491, 1491, 1491, 1491, 1491, 1491, 1491, 1491
.short -282, -282, -282, -282, -282, -282, -282, -282
.short -1544, -1544, -1544, -1544, -1544, -1544, -1544, -1544
.short 516, 516, 516, 516, 516, 516, 516, 516
.short -8, -8, -8, -8, -8, -8, -8, -8
.short -320, -320, -320, -320, -320, -320, -320, -320
.short -666, -666, -666, -666, -666, -666, -666, -666
.short -1618, -1618, -1618, -1618, -1618, -1618, -1618, -1618
.short -1162, -1162, -1162, -1162, -1162, -1162, -1162, -1162
.short 126, 126, 126, 126, 126, 126, 126, 126
.short 1469, 1469, 1469, 1469, 1469, 1469, 1469, 1469
.short -853, -853, -853, -853, -853, -853, -853, -853
.short -90, -90, -90, -90, -90, -90, -90, -90
.short -271, -271, -271, -271, -271, -271, -271, -271
.short 830, 830, 830, 830, 830, 830, 830, 830
.short 107, 107, 107, 107, 107, 107, 107, 107
.short -1421, -1421, -1421, -1421, -1421, -1421, -1421, -1421
.short -247, -247, -247, -247, -247, -247, -247, -247
.short -951, -951, -951, -951, -951, -951, -951, -951
.short -398, -398, -398, -398, -398, -398, -398, -398
.short 961, 961, 961, 961, 961, 961, 961, 961
.short -1508, -1508, -1508, -1508, -1508, -1508, -1508, -1508
.short -725, -725, -725, -725, -725, -725, -725, -725
.short 448, 448, 448, 448, 448, 448, 448, 448
.short -1065, -1065, -1065, -1065, -1065, -1065, -1065, -1065
.short 677, 677, 677, 677, 677, 677, 677, 677
.short -1275, -1275, -1275, -1275, -1275, -1275, -1275, -1275
.K64:
.short -1103, -1103, -1103, -1103, 430, 430, 430, 430
.short 555, 555, 555, 555, 843, 843, 843, 843
.short -1251, -1251, -1251, -1251, 871, 871, 871, 871
.short 1550, 1550, 1550, 1550, 105, 105, 105, 105
.short 422, 422, 422, 422, 587, 587, 587, 587
.short 177, 177, 177, 177, -235, -235, -235, -235
.short -291, -291, -291, -291, -460, -460, -460, -460
.short 1574, 1574, 1574, 1574, 1653, 1653, 1653, 1653
.short -246, -246, -246, -246, 778, 778, 778, 778
.short 1159, 1159, 1159, 1159, -147, -147, -147, -147
.short -777, -777, -777, -777, 1483, 1483, 1483, 1483
.short -602, -602, -602, -602, 1119, 1119, 1119, 1119
.short -1590, -1590, -1590, -1590, 644, 644, 644, 644
.short -872, -872, -872, -872, 349, 349, 349, 349
.short 418, 418, 418, 418, 329, 329, 329, 329
.short -156, -156, -156, -156, -75, -75, -75, -75
.short 817, 817, 817, 817, 1097, 1097, 1097, 1097
.short 603, 603, 603, 603, 610, 610, 610, 610
.short 1322, 1322, 1322, 1322, -1285, -1285, -1285, -1285
.short -1465, -1465, -1465, -1465, 384, 384, 384, 384
.short -1215, -1215, -1215, -1215, -136, -136, -136, -136
.short 1218, 1218, 1218, 1218, -1335, -1335, -1335, -1335
.short -874, -874, -874, -874, 220, 220, 220, 220
.short -1187, -1187, -1187, -1187, -1659, -1659, -1659, -1659
.short -1185, -1185, -1185, -1185, -1530, -1530, -1530, -1530
.short -1278, -1278, -1278, -1278, 794, 794, 794, 794
.short -1510, -1510, -1510, -1510, -854, -854, -854, -854
.short -870, -870, -870, -870, 478, 478, 478, 478
.short -108, -108, -108, -108, -308, -308, -308, -308
.short 996, 996, 996, 996, 991, 991, 991, 991
.short 958, 958, 958, 958, -1460, -1460, -1460, -1460
.short 1522, 1522, 1522, 1522, 1628, 1628, 1628, 1628
#endif /* MLK_ARITH_BACKEND_PPC64LE */
