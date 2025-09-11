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
        lxv 37, 0(4)
        lxv 34, 16(4)
        lxv 32, 80(4)
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
        mtlr 0
        addi 1, 1, 320
        blr
        .cfi_endproc

#endif /* MLK_ARITH_BACKEND_PPC64LE && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
