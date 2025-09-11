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
        lxvx 0, 0, 4
        li 10, 16
        lxvx 34, 10, 4
        xxlxor 35, 35, 35
        vspltish 4, 1
        xxlor 2, 34, 34
        xxlor 3, 35, 35
        xxlor 4, 36, 36
        li 10, 32
        li 11, 48
        lxvx 6, 10, 4
        lxvx 32, 11, 4
        vspltisw 8, 13
        vadduwm 8, 8, 8
        xxlor 8, 40, 40
        vspltisw 9, 1
        vsubuwm 10, 8, 9
        vslw 9, 9, 10
        xxlor 7, 41, 41
        li 10, 16
        li 11, 32
        li 12, 48
        li 15, 64
        li 16, 80
        li 17, 96
        li 18, 112
        addi 14, 4, 64
        lvx 10, 0, 14
        li 8, 4
        mtctr 8
        xxlor 37, 0, 0
        xxlor 34, 2, 2
        xxlor 35, 3, 3
        xxlor 36, 4, 4

Lintt_ppc__Loopf:
        lxvd2x 57, 0, 3
        lxvd2x 58, 10, 3
        lxvd2x 62, 11, 3
        lxvd2x 63, 12, 3
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
        lxvd2x 57, 0, 3
        lxvd2x 58, 10, 3
        lxvd2x 62, 11, 3
        lxvd2x 63, 12, 3
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
        addi 3, 3, -128
        stxvd2x 38, 0, 3
        stxvd2x 39, 10, 3
        stxvd2x 40, 11, 3
        stxvd2x 41, 12, 3
        stxvd2x 45, 15, 3
        stxvd2x 50, 16, 3
        stxvd2x 55, 17, 3
        stxvd2x 60, 18, 3
        addi 3, 3, 128
        bdnz Lintt_ppc__Loopf
        addi 3, 3, -512
        nop
        ori 2, 2, 0
        addi 14, 4, 1104
        li 7, 4
        li 8, 4
        mtctr 8
        mr	5, 3

Lintt_ppc__Loop2:
        lxvd2x 57, 0, 5
        lxvd2x 58, 10, 5
        vmrgew 8, 25, 26
        vmrgow 21, 25, 26
        lxvd2x 57, 11, 5
        lxvd2x 58, 12, 5
        vmrgew 12, 25, 26
        vmrgow 22, 25, 26
        lxvd2x 57, 15, 5
        lxvd2x 58, 16, 5
        vmrgew 16, 25, 26
        vmrgow 23, 25, 26
        lxvd2x 57, 17, 5
        lxvd2x 58, 18, 5
        vmrgew 20, 25, 26
        vmrgow 24, 25, 26
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
        li 8, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 8, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
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
        xxlor 46, 10, 10
        xxlor 51, 11, 11
        xxlor 56, 12, 12
        xxlor 61, 13, 13
        vmrgew 10, 13, 14
        vmrgow 11, 13, 14
        vmrgew 12, 18, 19
        vmrgow 13, 18, 19
        vmrgew 14, 23, 24
        vmrgow 15, 23, 24
        vmrgew 16, 28, 29
        vmrgow 17, 28, 29
        stxvd2x 42, 0, 5
        stxvd2x 43, 10, 5
        stxvd2x 44, 11, 5
        stxvd2x 45, 12, 5
        stxvd2x 46, 15, 5
        stxvd2x 47, 16, 5
        stxvd2x 48, 17, 5
        stxvd2x 49, 18, 5
        addi 5, 5, 128
        bdnz Lintt_ppc__Loop2
        ori 2, 2, 0
        mr	5, 3
        li 7, 8
        li 8, 4
        mtctr 8

Lintt_ppc__Loop4:
        lxvd2x 10, 0, 5
        lxvd2x 11, 10, 5
        xxmrgld	40, 11, 10
        xxmrghd	53, 11, 10
        lxvd2x 10, 11, 5
        lxvd2x 11, 12, 5
        xxmrgld	44, 11, 10
        xxmrghd	54, 11, 10
        lxvd2x 10, 15, 5
        lxvd2x 11, 16, 5
        xxmrgld	48, 11, 10
        xxmrghd	55, 11, 10
        lxvd2x 10, 17, 5
        lxvd2x 11, 18, 5
        xxmrgld	52, 11, 10
        xxmrghd	56, 11, 10
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
        li 8, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 8, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
        addi 14, 14, 64
        xxswapd	39, 39
        xxswapd	40, 40
        xxswapd	41, 41
        xxswapd	42, 42
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
        xxlor 46, 10, 10
        xxlor 51, 11, 11
        xxlor 56, 12, 12
        xxlor 61, 13, 13
        xxmrgld	42, 46, 45
        xxmrghd	43, 46, 45
        xxmrgld	44, 51, 50
        xxmrghd	45, 51, 50
        xxmrgld	46, 56, 55
        xxmrghd	47, 56, 55
        xxmrgld	48, 61, 60
        xxmrghd	49, 61, 60
        stxvd2x 42, 0, 5
        stxvd2x 43, 10, 5
        stxvd2x 44, 11, 5
        stxvd2x 45, 12, 5
        stxvd2x 46, 15, 5
        stxvd2x 47, 16, 5
        stxvd2x 48, 17, 5
        stxvd2x 49, 18, 5
        addi 5, 5, 128
        bdnz Lintt_ppc__Loop4
        nop
        ori 2, 2, 0
        li 7, 16
        li 5, 0
        li 15, 4
        mtctr 15

Lintt_ppc__Loop8:
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        li 8, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 8, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
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
        addi 5, 5, 128
        bdnz Lintt_ppc__Loop8
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        li 8, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 8, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
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
        addi 14, 14, -64
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        li 8, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 8, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        li 8, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 8, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
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
        addi 14, 14, -64
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        li 8, 16
        li 11, 32
        li 12, 48
        lxvd2x 39, 0, 14
        lxvd2x 40, 8, 14
        lxvd2x 41, 11, 14
        lxvd2x 42, 12, 14
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
        lxvd2x 53, 3, 9
        lxvd2x 54, 3, 16
        lxvd2x 55, 3, 18
        lxvd2x 56, 3, 20
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
