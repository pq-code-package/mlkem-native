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

// Poly_tomont: Inplace conversion of all coefficients of a polynomial
//              from normal domain to Montgomery domain
//
// Arguments:*r: pointer to input/output polynomial

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/ppc64le/src/poly_tomont.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 16
.global MLK_ASM_NAMESPACE(poly_tomont_ppc)
MLK_ASM_FN_SYMBOL(poly_tomont_ppc)

        .cfi_startproc
        stdu 1, -320(1)
        mflr 0
        li 6, 128
        li 7, 144
        li 8, 160
        li 9, 176
        li 10, 192
        li 11, 208
        li 12, 224
        stxvx 52, 6, 1
        stxvx 53, 7, 1
        stxvx 54, 8, 1
        stxvx 55, 9, 1
        stxvx 56, 10, 1
        stxvx 57, 11, 1
        stxvx 58, 12, 1
        li 6, 240
        li 7, 256
        li 8, 272
        li 9, 288
        stxvx 59, 6, 1
        stxvx 60, 7, 1
        stxvx 61, 8, 1
        stxvx 62, 9, 1
        li 6, 0
        li 7, 16
        li 8, 80
        lxvx 37, 6, 4
        lxvx 34, 7, 4
        lxvx 32, 8, 4
        vxor 3, 3, 3
        vspltish 4, 1
        li 4, -128
        li 5, -112
        li 6, -96
        li 7, -80
        li 8, -64
        li 9, -48
        li 10, -32
        li 11, -16
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 27, 15, 4
        vsrah 28, 20, 4
        vsrah 29, 25, 4
        vsrah 30, 9, 4
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 7, 9, 4
        stxvd2x 59, 4, 3
        stxvd2x 60, 5, 3
        stxvd2x 61, 6, 3
        stxvd2x 62, 7, 3
        stxvd2x 45, 8, 3
        stxvd2x 50, 9, 3
        stxvd2x 55, 10, 3
        stxvd2x 39, 11, 3
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 27, 15, 4
        vsrah 28, 20, 4
        vsrah 29, 25, 4
        vsrah 30, 9, 4
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 7, 9, 4
        stxvd2x 59, 4, 3
        stxvd2x 60, 5, 3
        stxvd2x 61, 6, 3
        stxvd2x 62, 7, 3
        stxvd2x 45, 8, 3
        stxvd2x 50, 9, 3
        stxvd2x 55, 10, 3
        stxvd2x 39, 11, 3
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 27, 15, 4
        vsrah 28, 20, 4
        vsrah 29, 25, 4
        vsrah 30, 9, 4
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 7, 9, 4
        stxvd2x 59, 4, 3
        stxvd2x 60, 5, 3
        stxvd2x 61, 6, 3
        stxvd2x 62, 7, 3
        stxvd2x 45, 8, 3
        stxvd2x 50, 9, 3
        stxvd2x 55, 10, 3
        stxvd2x 39, 11, 3
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 27, 15, 4
        vsrah 28, 20, 4
        vsrah 29, 25, 4
        vsrah 30, 9, 4
        lxvd2x 45, 0, 3
        addi 3, 3, 16
        lxvd2x 50, 0, 3
        addi 3, 3, 16
        lxvd2x 55, 0, 3
        addi 3, 3, 16
        lxvd2x 39, 0, 3
        addi 3, 3, 16
        vmladduhm 15, 13, 0, 3
        vmladduhm 20, 18, 0, 3
        vmladduhm 25, 23, 0, 3
        vmladduhm 9, 7, 0, 3
        vmhraddshs 14, 13, 0, 3
        vmhraddshs 19, 18, 0, 3
        vmhraddshs 24, 23, 0, 3
        vmhraddshs 8, 7, 0, 3
        vmladduhm 15, 15, 2, 3
        vmladduhm 20, 20, 2, 3
        vmladduhm 25, 25, 2, 3
        vmladduhm 9, 9, 2, 3
        vmhraddshs 15, 15, 5, 14
        vmhraddshs 20, 20, 5, 19
        vmhraddshs 25, 25, 5, 24
        vmhraddshs 9, 9, 5, 8
        vsrah 13, 15, 4
        vsrah 18, 20, 4
        vsrah 23, 25, 4
        vsrah 7, 9, 4
        stxvd2x 59, 4, 3
        stxvd2x 60, 5, 3
        stxvd2x 61, 6, 3
        stxvd2x 62, 7, 3
        stxvd2x 45, 8, 3
        stxvd2x 50, 9, 3
        stxvd2x 55, 10, 3
        stxvd2x 39, 11, 3
        li 6, 128
        li 7, 144
        li 8, 160
        li 9, 176
        li 10, 192
        li 11, 208
        li 12, 224
        lxvx 52, 6, 1
        lxvx 53, 7, 1
        lxvx 54, 8, 1
        lxvx 55, 9, 1
        lxvx 56, 10, 1
        lxvx 57, 11, 1
        lxvx 58, 12, 1
        li 6, 240
        li 7, 256
        li 8, 272
        li 9, 288
        lxvx 59, 6, 1
        lxvx 60, 7, 1
        lxvx 61, 8, 1
        lxvx 62, 9, 1
        mtlr 0
        addi 1, 1, 320
        blr
        .cfi_endproc

#endif /* MLK_ARITH_BACKEND_PPC64LE && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
