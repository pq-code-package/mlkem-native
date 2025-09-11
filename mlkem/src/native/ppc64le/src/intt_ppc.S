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
 *   dev/ppc64le/src/intt_ppc.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
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
        addis 8, 2, 0
        addi 8, 8, 0
        lxv 0, 0(8)
        lxv 34, 16(8)
        xxlxor 35, 35, 35
        vspltish 4, 1
        xxlor 2, 34, 34
        xxlor 3, 35, 35
        xxlor 4, 36, 36
        addis 8, 2, 0
        addi 8, 8, 0
        addis 9, 2, 0
        addi 9, 9, 0
        addis 10, 2, 0
        addi 10, 10, 0
        lxv 6, 0(8)
        lxv 32, 0(9)
        lxv 7, 0(10)
        vspltisw 8, 13
        vadduwm 8, 8, 8
        xxlor 8, 40, 40

Lintt_ppc_Len2:
        addis 14, 2, 0
        addi 14, 14, 0
        li 4, 4
        li 15, 4
        mtctr 15
        li 5, 0

Lintt_ppc_Loop2:
        mr	9, 5
        add 10, 4, 9
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
        add 10, 4, 9
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
        bdnz Lintt_ppc_Loop2

Lintt_ppc_Len4:
        addis 14, 2, 0
        addi 14, 14, 0
        li 5, 0
        li 4, 8
        li 15, 4
        mtctr 15

Lintt_ppc_Loop4:
        mr	9, 5
        add 10, 4, 9
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
        add 10, 4, 9
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
        bdnz Lintt_ppc_Loop4

Lintt_ppc_Len8:
        li 4, 16
        li 5, 0
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 128
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 384
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21

Lintt_ppc_Len16:
        li 5, 0
        li 4, 32
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 16
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 272
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21

Lintt_ppc_Len32:
        li 5, 0
        li 4, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 128
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 384
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21

Lintt_ppc_Len64:
        li 5, 0
        li 4, 128
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 256
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 320
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21

Lintt_ppc_Len128:
        li 5, 0
        li 4, 256
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 64
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 128
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        li 5, 192
        mr	9, 5
        add 10, 4, 9
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
        stxvd2x 36, 3, 9
        stxvd2x 41, 3, 16
        stxvd2x 45, 3, 18
        stxvd2x 49, 3, 20
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
        stxvd2x 45, 3, 10
        stxvd2x 50, 3, 17
        stxvd2x 55, 3, 19
        stxvd2x 60, 3, 21
        addis 10, 2, 0
        addi 10, 10, 0
        lvx 10, 0, 10
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

Lintt_ppc_intt_out:
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
.short -3329, -3329, -3329, -3329, -3329, -3329, -3329, -3329
// QINV
.short  -3327, -3327, -3327, -3327, -3327, -3327, -3327, -3327

// MLKEM_Q
.mkq:
.short 3329, 3329, 3329, 3329, 3329, 3329, 3329, 3329

.C20159:
.short  20159, 20159, 20159, 20159, 20159, 20159, 20159, 20159

// 0x2000000
.C25:
.long   33554432, 33554432, 33554432, 33554432

.C1441:
.short 1441, 1441, 1441, 1441, 1441, 1441, 1441, 1441

.izeta127:
.short 1628, 1628, 1628, 1628, 1522, 1522, 1522, 1522
.short -1460, -1460, -1460, -1460, 958, 958, 958, 958
.short 991, 991, 991, 991, 996, 996, 996, 996
.short -308, -308, -308, -308, -108, -108, -108, -108
.short 478, 478, 478, 478, -870, -870, -870, -870
.short -854, -854, -854, -854, -1510, -1510, -1510, -1510
.short 794, 794, 794, 794, -1278, -1278, -1278, -1278
.short -1530, -1530, -1530, -1530, -1185, -1185, -1185, -1185
.short -1659, -1659, -1659, -1659, -1187, -1187, -1187, -1187
.short 220, 220, 220, 220, -874, -874, -874, -874
.short -1335, -1335, -1335, -1335, 1218, 1218, 1218, 1218
.short -136, -136, -136, -136, -1215, -1215, -1215, -1215
.short 384, 384, 384, 384, -1465, -1465, -1465, -1465
.short -1285, -1285, -1285, -1285, 1322, 1322, 1322, 1322
.short 610, 610, 610, 610, 603, 603, 603, 603
.short 1097, 1097, 1097, 1097, 817, 817, 817, 817
.short -75, -75, -75, -75, -156, -156, -156, -156
.short 329, 329, 329, 329, 418, 418, 418, 418
.short 349, 349, 349, 349, -872, -872, -872, -872
.short 644, 644, 644, 644, -1590, -1590, -1590, -1590
.short 1119, 1119, 1119, 1119, -602, -602, -602, -602
.short 1483, 1483, 1483, 1483, -777, -777, -777, -777
.short -147, -147, -147, -147, 1159, 1159, 1159, 1159
.short 778, 778, 778, 778, -246, -246, -246, -246
.short 1653, 1653, 1653, 1653, 1574, 1574, 1574, 1574
.short -460, -460, -460, -460, -291, -291, -291, -291
.short -235, -235, -235, -235, 177, 177, 177, 177
.short 587, 587, 587, 587, 422, 422, 422, 422
.short 105, 105, 105, 105, 1550, 1550, 1550, 1550
.short 871, 871, 871, 871, -1251, -1251, -1251, -1251
.short 843, 843, 843, 843, 555, 555, 555, 555
.short 430, 430, 430, 430, -1103, -1103, -1103, -1103
.izeta63:
.short -1275, -1275, -1275, -1275, -1275, -1275, -1275, -1275
.short 677, 677, 677, 677, 677, 677, 677, 677
.short -1065, -1065, -1065, -1065, -1065, -1065, -1065, -1065
.short 448, 448, 448, 448, 448, 448, 448, 448
.short -725, -725, -725, -725, -725, -725, -725, -725
.short -1508, -1508, -1508, -1508, -1508, -1508, -1508, -1508
.short 961, 961, 961, 961, 961, 961, 961, 961
.short -398, -398, -398, -398, -398, -398, -398, -398
.short -951, -951, -951, -951, -951, -951, -951, -951
.short -247, -247, -247, -247, -247, -247, -247, -247
.short -1421, -1421, -1421, -1421, -1421, -1421, -1421, -1421
.short 107, 107, 107, 107, 107, 107, 107, 107
.short 830, 830, 830, 830, 830, 830, 830, 830
.short -271, -271, -271, -271, -271, -271, -271, -271
.short -90, -90, -90, -90, -90, -90, -90, -90
.short -853, -853, -853, -853, -853, -853, -853, -853
.short 1469, 1469, 1469, 1469, 1469, 1469, 1469, 1469
.short 126, 126, 126, 126, 126, 126, 126, 126
.short -1162, -1162, -1162, -1162, -1162, -1162, -1162, -1162
.short -1618, -1618, -1618, -1618, -1618, -1618, -1618, -1618
.short -666, -666, -666, -666, -666, -666, -666, -666
.short -320, -320, -320, -320, -320, -320, -320, -320
.short -8, -8, -8, -8, -8, -8, -8, -8
.short 516, 516, 516, 516, 516, 516, 516, 516
.short -1544, -1544, -1544, -1544, -1544, -1544, -1544, -1544
.short -282, -282, -282, -282, -282, -282, -282, -282
.short 1491, 1491, 1491, 1491, 1491, 1491, 1491, 1491
.short -1293, -1293, -1293, -1293, -1293, -1293, -1293, -1293
.short 1015, 1015, 1015, 1015, 1015, 1015, 1015, 1015
.short -552, -552, -552, -552, -552, -552, -552, -552
.short 652, 652, 652, 652, 652, 652, 652, 652
.short 1223, 1223, 1223, 1223, 1223, 1223, 1223, 1223
.short -1571, -1571, -1571, -1571, -1571, -1571, -1571, -1571
.short -205, -205, -205, -205, -205, -205, -205, -205
.short 411, 411, 411, 411, 411, 411, 411, 411
.short -1542, -1542, -1542, -1542, -1542, -1542, -1542, -1542
.short 608, 608, 608, 608, 608, 608, 608, 608
.short 732, 732, 732, 732, 732, 732, 732, 732
.short 1017, 1017, 1017, 1017, 1017, 1017, 1017, 1017
.short -681, -681, -681, -681, -681, -681, -681, -681
.short -130, -130, -130, -130, -130, -130, -130, -130
.short -1602, -1602, -1602, -1602, -1602, -1602, -1602, -1602
.short 1458, 1458, 1458, 1458, 1458, 1458, 1458, 1458
.short -829, -829, -829, -829, -829, -829, -829, -829
.short 383, 383, 383, 383, 383, 383, 383, 383
.short 264, 264, 264, 264, 264, 264, 264, 264
.short -1325, -1325, -1325, -1325, -1325, -1325, -1325, -1325
.short 573, 573, 573, 573, 573, 573, 573, 573
.short 1468, 1468, 1468, 1468, 1468, 1468, 1468, 1468
.short -1474, -1474, -1474, -1474, -1474, -1474, -1474, -1474
.short -1202, -1202, -1202, -1202, -1202, -1202, -1202, -1202
.short 962, 962, 962, 962, 962, 962, 962, 962
.short 182, 182, 182, 182, 182, 182, 182, 182
.short 1577, 1577, 1577, 1577, 1577, 1577, 1577, 1577
.short 622, 622, 622, 622, 622, 622, 622, 622
.short -171, -171, -171, -171, -171, -171, -171, -171
.short 202, 202, 202, 202, 202, 202, 202, 202
.short 287, 287, 287, 287, 287, 287, 287, 287
.short 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422
.short 1493, 1493, 1493, 1493, 1493, 1493, 1493, 1493
.short -1517, -1517, -1517, -1517, -1517, -1517, -1517, -1517
.short -359, -359, -359, -359, -359, -359, -359, -359
.short -758, -758, -758, -758, -758, -758, -758, -758

#endif /* MLK_ARITH_BACKEND_PPC64LE */
