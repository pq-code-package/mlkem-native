/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) IBM Corp. 2025, 2026
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * Written by Danny Tsen <dtsen@us.ibm.com>
 * poly_reduce optimization (#1724) by Scott Boudreaux.
 */
#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && defined(__POWER8_VECTOR__)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/ppc64le/src/reduce_ppc_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
.global MLK_ASM_NAMESPACE(reduce_ppc_asm)
MLK_ASM_FN_SYMBOL(reduce_ppc_asm)

        stdu 1, -224(1)
        mflr 0
        std 14, 96(1)
        std 15, 104(1)
        std 16, 112(1)
        li 6, 128
        li 7, 144
        li 8, 160
        li 9, 176
        li 10, 192
        stxvd2x 52, 6, 1
        stxvd2x 53, 7, 1
        stxvd2x 54, 8, 1
        stxvd2x 55, 9, 1
        stxvd2x 56, 10, 1
        li 6, 32
        li 7, 0
        li 8, 16
        lxvd2x 32, 6, 4
        lxvd2x 33, 7, 4
        lxvd2x 39, 8, 4
        vspltish 3, 11
        vspltish 2, 1
        vspltish 4, 10
        vslh 2, 2, 4
        li 4, -128
        li 5, -112
        li 6, -96
        li 7, -80
        li 8, -64
        li 9, -48
        li 10, -32
        li 11, -16
        li 14, 16
        li 15, 32
        li 16, 48
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 21, 5, 1, 8
        vmladduhm 22, 6, 1, 12
        vmladduhm 23, 10, 1, 16
        vmladduhm 24, 11, 1, 20
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 4, 5, 1, 8
        vmladduhm 9, 6, 1, 12
        vmladduhm 13, 10, 1, 16
        vmladduhm 17, 11, 1, 20
        stxvd2x 53, 4, 3
        stxvd2x 54, 5, 3
        stxvd2x 55, 6, 3
        stxvd2x 56, 7, 3
        stxvd2x 36, 8, 3
        stxvd2x 41, 9, 3
        stxvd2x 45, 10, 3
        stxvd2x 49, 11, 3
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 21, 5, 1, 8
        vmladduhm 22, 6, 1, 12
        vmladduhm 23, 10, 1, 16
        vmladduhm 24, 11, 1, 20
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 4, 5, 1, 8
        vmladduhm 9, 6, 1, 12
        vmladduhm 13, 10, 1, 16
        vmladduhm 17, 11, 1, 20
        stxvd2x 53, 4, 3
        stxvd2x 54, 5, 3
        stxvd2x 55, 6, 3
        stxvd2x 56, 7, 3
        stxvd2x 36, 8, 3
        stxvd2x 41, 9, 3
        stxvd2x 45, 10, 3
        stxvd2x 49, 11, 3
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 21, 5, 1, 8
        vmladduhm 22, 6, 1, 12
        vmladduhm 23, 10, 1, 16
        vmladduhm 24, 11, 1, 20
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 4, 5, 1, 8
        vmladduhm 9, 6, 1, 12
        vmladduhm 13, 10, 1, 16
        vmladduhm 17, 11, 1, 20
        stxvd2x 53, 4, 3
        stxvd2x 54, 5, 3
        stxvd2x 55, 6, 3
        stxvd2x 56, 7, 3
        stxvd2x 36, 8, 3
        stxvd2x 41, 9, 3
        stxvd2x 45, 10, 3
        stxvd2x 49, 11, 3
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 21, 5, 1, 8
        vmladduhm 22, 6, 1, 12
        vmladduhm 23, 10, 1, 16
        vmladduhm 24, 11, 1, 20
        lxvd2x 40, 0, 3
        lxvd2x 44, 14, 3
        lxvd2x 48, 15, 3
        lxvd2x 52, 16, 3
        addi 3, 3, 64
        vmhaddshs 5, 8, 0, 2
        vmhaddshs 6, 12, 0, 2
        vmhaddshs 10, 16, 0, 2
        vmhaddshs 11, 20, 0, 2
        vsrah 5, 5, 3
        vsrah 6, 6, 3
        vsrah 10, 10, 3
        vsrah 11, 11, 3
        vmladduhm 4, 5, 1, 8
        vmladduhm 9, 6, 1, 12
        vmladduhm 13, 10, 1, 16
        vmladduhm 17, 11, 1, 20
        stxvd2x 53, 4, 3
        stxvd2x 54, 5, 3
        stxvd2x 55, 6, 3
        stxvd2x 56, 7, 3
        stxvd2x 36, 8, 3
        stxvd2x 41, 9, 3
        stxvd2x 45, 10, 3
        stxvd2x 49, 11, 3
        addi 3, 3, -512
        vxor 9, 9, 9
        vspltish 10, 15
        vmr 11, 7
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        lxvd2x 44, 0, 3
        lxvd2x 45, 14, 3
        lxvd2x 46, 15, 3
        lxvd2x 47, 16, 3
        addi 3, 3, 64
        vsrh 1, 12, 10
        vsrh 0, 13, 10
        vsrh 3, 14, 10
        vsrh 2, 15, 10
        vadduhm 7, 12, 11
        vadduhm 8, 13, 11
        vadduhm 5, 14, 11
        vadduhm 6, 15, 11
        vcmpequh 1, 1, 9
        vcmpequh 0, 0, 9
        vcmpequh 3, 3, 9
        vcmpequh 2, 2, 9
        xxsel 33, 39, 44, 33
        xxsel 32, 40, 45, 32
        xxsel 35, 37, 46, 35
        xxsel 34, 38, 47, 34
        stxvd2x 35, 10, 3
        stxvd2x 34, 11, 3
        stxvd2x 33, 8, 3
        stxvd2x 32, 9, 3
        ld 14, 96(1)
        ld 15, 104(1)
        ld 16, 112(1)
        li 6, 128
        li 7, 144
        li 8, 160
        li 9, 176
        li 10, 192
        lxvd2x 52, 6, 1
        lxvd2x 53, 7, 1
        lxvd2x 54, 8, 1
        lxvd2x 55, 9, 1
        lxvd2x 56, 10, 1
        mtlr 0
        addi 1, 1, 224
        blr

MLK_ASM_FN_SIZE(reduce_ppc_asm)

#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
