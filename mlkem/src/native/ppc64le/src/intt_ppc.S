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
 *   dev/ppc64le/src/intt_ppc.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 16
.global MLK_ASM_NAMESPACE(intt_ppc)
MLK_ASM_FN_SYMBOL(intt_ppc)

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
        lxv 0, 0(4)
        lxv 34, 16(4)
        xxlxor 35, 35, 35
        vspltish 4, 1
        xxlor 2, 34, 34
        xxlor 3, 35, 35
        xxlor 4, 36, 36
        lxv 6, 32(4)
        lxv 32, 48(4)
        lxv 7, 0(4)
        vspltisw 8, 13
        vadduwm 8, 8, 8
        xxlor 8, 40, 40
        vspltisw 9, 1
        vsubuwm 10, 8, 9
        vslw 9, 9, 10
        xxlor 7, 41, 41
        ori 2, 2, 0
        addi 14, 4, 1616
        li 7, 4
        li 15, 4
        mtctr 15
        li 5, 0

Lintt_ppc__Loop2:
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        xxlor 10, 36, 36
        xxlor 11, 41, 41
        xxlor 12, 45, 45
        xxlor 13, 49, 49
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        xxmrglw 44, 45, 10
        xxmrghw 43, 45, 10
        xxmrgld	10, 44, 43
        xxmrglw 48, 50, 11
        xxmrghw 47, 50, 11
        xxmrgld	11, 48, 47
        xxmrglw 44, 55, 12
        xxmrghw 43, 55, 12
        xxmrgld	12, 44, 43
        xxmrglw 48, 60, 13
        xxmrghw 47, 60, 13
        xxmrgld	13, 48, 47
        stxvd2x 10, 3, 9
        stxvd2x 11, 3, 16
        stxvd2x 12, 3, 18
        stxvd2x 13, 3, 20
        addi 5, 5, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        xxlor 10, 36, 36
        xxlor 11, 41, 41
        xxlor 12, 45, 45
        xxlor 13, 49, 49
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        xxmrglw 44, 45, 10
        xxmrghw 43, 45, 10
        xxmrgld	10, 44, 43
        xxmrglw 48, 50, 11
        xxmrghw 47, 50, 11
        xxmrgld	11, 48, 47
        xxmrglw 44, 55, 12
        xxmrghw 43, 55, 12
        xxmrgld	12, 44, 43
        xxmrglw 48, 60, 13
        xxmrghw 47, 60, 13
        xxmrgld	13, 48, 47
        stxvd2x 10, 3, 9
        stxvd2x 11, 3, 16
        stxvd2x 12, 3, 18
        stxvd2x 13, 3, 20
        addi 5, 5, 64
        bdnz Lintt_ppc__Loop2
        nop
        ori 2, 2, 0
        addi 14, 4, 2128
        li 5, 0
        li 7, 8
        li 15, 4
        mtctr 15

Lintt_ppc__Loop4:
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        xxlor 10, 36, 36
        xxlor 11, 41, 41
        xxlor 12, 45, 45
        xxlor 13, 49, 49
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        xxmrgld	10, 10, 45
        xxmrgld	11, 11, 50
        xxmrgld	12, 12, 55
        xxmrgld	13, 13, 60
        stxvd2x 10, 3, 9
        stxvd2x 11, 3, 16
        stxvd2x 12, 3, 18
        stxvd2x 13, 3, 20
        addi 5, 5, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        xxlor 10, 36, 36
        xxlor 11, 41, 41
        xxlor 12, 45, 45
        xxlor 13, 49, 49
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        xxmrgld	10, 10, 45
        xxmrgld	11, 11, 50
        xxmrgld	12, 12, 55
        xxmrgld	13, 13, 60
        stxvd2x 10, 3, 9
        stxvd2x 11, 3, 16
        stxvd2x 12, 3, 18
        stxvd2x 13, 3, 20
        addi 5, 5, 64
        bdnz Lintt_ppc__Loop4
        nop
        ori 2, 2, 0
        li 7, 16
        li 5, 0
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 128
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 384
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 32
        addi 17, 10, 32
        addi 18, 16, 32
        addi 19, 17, 32
        addi 20, 18, 32
        addi 21, 19, 32
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        nop
        nop
        ori 2, 2, 0
        li 5, 0
        li 7, 32
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 16
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        addi 14, 14, -64
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 272
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 64
        addi 17, 10, 64
        addi 18, 16, 64
        addi 19, 17, 64
        addi 20, 18, 64
        addi 21, 19, 64
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        addi 14, 14, -64
        lxv 39, 0(14)
        lxv 40, 16(14)
        lxv 41, 32(14)
        lxv 42, 48(14)
        addi 14, 14, 64
        vmladduhm 15, 25, 7, 3
        vmladduhm 20, 26, 8, 3
        vmladduhm 27, 30, 9, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 7, 3
        vmhraddshs 19, 26, 8, 3
        vmhraddshs 24, 30, 9, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        ori 2, 2, 0
        li 5, 0
        li 7, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lvx 10, 0, 14
        addi 14, 14, 16
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 128
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lvx 10, 0, 14
        addi 14, 14, 16
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lvx 10, 0, 14
        addi 14, 14, 16
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 384
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lvx 10, 0, 14
        addi 14, 14, 16
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        nop
        nop
        ori 2, 2, 0
        li 5, 0
        li 7, 128
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lvx 10, 0, 14
        addi 14, 14, 16
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 42, -16(14)
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lvx 10, 0, 14
        addi 14, 14, 16
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 320
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lxv 42, -16(14)
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        ori 2, 2, 0
        li 5, 0
        li 7, 256
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        lvx 10, 0, 14
        xxlor 9, 42, 42
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 64
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        xxlor 42, 9, 9
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 128
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        xxlor 42, 9, 9
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        li 5, 192
        mr	9, 5
        add 10, 7, 9
        addi 16, 9, 16
        addi 17, 10, 16
        addi 18, 16, 16
        addi 19, 17, 16
        addi 20, 18, 16
        addi 21, 19, 16
        lxvd2x 40, 3, 10
        lxvd2x 44, 3, 17
        lxvd2x 48, 3, 19
        lxvd2x 52, 3, 21
        xxswapd	40, 40
        xxswapd	44, 44
        xxswapd	48, 48
        xxswapd	52, 52
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
        xxswapd	53, 53
        xxswapd	54, 54
        xxswapd	55, 55
        xxswapd	56, 56
        vsubuhm 25, 8, 21
        vsubuhm 26, 12, 22
        vsubuhm 30, 16, 23
        vsubuhm 31, 20, 24
        vadduhm 8, 8, 21
        vadduhm 12, 12, 22
        vadduhm 16, 16, 23
        vadduhm 20, 20, 24
        vxor 7, 7, 7
        xxlor 35, 6, 6
        xxlor 33, 7, 7
        xxlor 34, 8, 8
        vmulosh 6, 8, 0
        vmulesh 5, 8, 0
        vmulosh 11, 12, 0
        vmulesh 10, 12, 0
        vmulosh 15, 16, 0
        vmulesh 14, 16, 0
        vmulosh 19, 20, 0
        vmulesh 18, 20, 0
        xxmrglw 36, 37, 38
        xxmrghw 37, 37, 38
        xxmrglw 41, 42, 43
        xxmrghw 42, 42, 43
        xxmrglw 45, 46, 47
        xxmrghw 46, 46, 47
        xxmrglw 49, 50, 51
        xxmrghw 50, 50, 51
        vadduwm 4, 4, 1
        vadduwm 5, 5, 1
        vadduwm 9, 9, 1
        vadduwm 10, 10, 1
        vadduwm 13, 13, 1
        vadduwm 14, 14, 1
        vadduwm 17, 17, 1
        vadduwm 18, 18, 1
        vsraw 4, 4, 2
        vsraw 5, 5, 2
        vsraw 9, 9, 2
        vsraw 10, 10, 2
        vsraw 13, 13, 2
        vsraw 14, 14, 2
        vsraw 17, 17, 2
        vsraw 18, 18, 2
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        vmladduhm 4, 4, 3, 8
        vmladduhm 9, 9, 3, 12
        vmladduhm 13, 13, 3, 16
        vmladduhm 17, 17, 3, 20
        stxvx 36, 3, 9
        stxvx 41, 3, 16
        stxvx 45, 3, 18
        stxvx 49, 3, 20
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4
        xxlor 42, 9, 9
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxvx 45, 3, 10
        stxvx 50, 3, 17
        stxvx 55, 3, 19
        stxvx 60, 3, 21
        nop
        ori 2, 2, 0
        addi 14, 4, 64
        lvx 10, 0, 14
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 6, 15, 4
        vsrah 7, 20, 4
        vsrah 8, 25, 4
        vsrah 9, 30, 4
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxv 38, -128(3)
        stxv 39, -112(3)
        stxv 40, -96(3)
        stxv 41, -80(3)
        stxv 45, -64(3)
        stxv 50, -48(3)
        stxv 55, -32(3)
        stxv 60, -16(3)
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 6, 15, 4
        vsrah 7, 20, 4
        vsrah 8, 25, 4
        vsrah 9, 30, 4
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxv 38, -128(3)
        stxv 39, -112(3)
        stxv 40, -96(3)
        stxv 41, -80(3)
        stxv 45, -64(3)
        stxv 50, -48(3)
        stxv 55, -32(3)
        stxv 60, -16(3)
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 6, 15, 4
        vsrah 7, 20, 4
        vsrah 8, 25, 4
        vsrah 9, 30, 4
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxv 38, -128(3)
        stxv 39, -112(3)
        stxv 40, -96(3)
        stxv 41, -80(3)
        stxv 45, -64(3)
        stxv 50, -48(3)
        stxv 55, -32(3)
        stxv 60, -16(3)
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 6, 15, 4
        vsrah 7, 20, 4
        vsrah 8, 25, 4
        vsrah 9, 30, 4
        lxv 57, 0(3)
        lxv 58, 16(3)
        lxv 62, 32(3)
        lxv 63, 48(3)
        addi 3, 3, 64
        vmladduhm 15, 25, 10, 3
        vmladduhm 20, 26, 10, 3
        vmladduhm 27, 30, 10, 3
        vmladduhm 28, 31, 10, 3
        vmhraddshs 14, 25, 10, 3
        vmhraddshs 19, 26, 10, 3
        vmhraddshs 24, 30, 10, 3
        vmhraddshs 29, 31, 10, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 27, 2, 3
        vmladduhm 30, 28, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 30, 30, 5, 29
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 28, 30, 4
        stxv 38, -128(3)
        stxv 39, -112(3)
        stxv 40, -96(3)
        stxv 41, -80(3)
        stxv 45, -64(3)
        stxv 50, -48(3)
        stxv 55, -32(3)
        stxv 60, -16(3)
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
