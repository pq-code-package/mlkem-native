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

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/ppc64le/src/ntt_ppc_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
.global MLK_ASM_NAMESPACE(ntt_ppc_asm)
MLK_ASM_FN_SYMBOL(ntt_ppc_asm)

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
        stxvd2x 52, 10, 1
        stxvd2x 53, 11, 1
        stxvd2x 54, 12, 1
        stxvd2x 55, 14, 1
        stxvd2x 56, 15, 1
        stxvd2x 57, 16, 1
        li 10, 224
        li 11, 240
        li 12, 256
        li 14, 272
        li 15, 288
        li 16, 304
        stxvd2x 58, 10, 1
        stxvd2x 59, 11, 1
        stxvd2x 60, 12, 1
        stxvd2x 61, 14, 1
        stxvd2x 62, 15, 1
        stxvd2x 63, 16, 1
        lvx 5, 0, 4
        addi 14, 4, 96
        addi 8, 4, 2112
        vxor 3, 3, 3
        lvx 0, 0, 14
        lvx 1, 0, 8
        li 10, 16
        lvx 2, 10, 14
        lvx 4, 10, 8
        li 11, 32
        lvx 6, 11, 14
        lvx 11, 11, 8
        li 12, 48
        lvx 7, 12, 14
        lvx 8, 12, 8
        li 10, 64
        lvx 9, 10, 14
        lvx 10, 10, 8
        li 11, 80
        lvx 14, 11, 14
        lvx 19, 11, 8
        li 12, 96
        lvx 24, 12, 14
        lvx 29, 12, 8
        addi 14, 14, 112
        addi 8, 8, 112
        li 9, 0
        li 10, 64
        li 11, 128
        li 12, 192
        li 16, 256
        li 17, 320
        li 18, 384
        li 19, 448
        li 6, 4
        mtctr 6

ntt_ppc_layer123_start:
        lxvd2x 44, 9, 3
        lxvd2x 45, 10, 3
        lxvd2x 49, 11, 3
        lxvd2x 50, 12, 3
        lxvd2x 54, 16, 3
        lxvd2x 55, 17, 3
        lxvd2x 59, 18, 3
        lxvd2x 60, 19, 3
        vmhraddshs 15, 22, 1, 3
        vmladduhm 16, 22, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 22, 12, 16
        vadduhm 12, 12, 16
        vmhraddshs 15, 23, 1, 3
        vmladduhm 16, 23, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 23, 13, 16
        vadduhm 13, 13, 16
        vmhraddshs 15, 27, 1, 3
        vmladduhm 16, 27, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 27, 17, 16
        vadduhm 17, 17, 16
        vmhraddshs 15, 28, 1, 3
        vmladduhm 16, 28, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 28, 18, 16
        vadduhm 18, 18, 16
        vmhraddshs 15, 17, 4, 3
        vmladduhm 16, 17, 2, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 17, 12, 16
        vadduhm 12, 12, 16
        vmhraddshs 15, 18, 4, 3
        vmladduhm 16, 18, 2, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 18, 13, 16
        vadduhm 13, 13, 16
        vmhraddshs 15, 27, 11, 3
        vmladduhm 16, 27, 6, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 27, 22, 16
        vadduhm 22, 22, 16
        vmhraddshs 15, 28, 11, 3
        vmladduhm 16, 28, 6, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 28, 23, 16
        vadduhm 23, 23, 16
        vmhraddshs 15, 13, 8, 3
        vmladduhm 16, 13, 7, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 13, 12, 16
        vadduhm 12, 12, 16
        vmhraddshs 15, 18, 10, 3
        vmladduhm 16, 18, 9, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 18, 17, 16
        vadduhm 17, 17, 16
        vmhraddshs 15, 23, 19, 3
        vmladduhm 16, 23, 14, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 23, 22, 16
        vadduhm 22, 22, 16
        vmhraddshs 15, 28, 29, 3
        vmladduhm 16, 28, 24, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 28, 27, 16
        vadduhm 27, 27, 16
        stxvd2x 44, 9, 3
        stxvd2x 45, 10, 3
        stxvd2x 49, 11, 3
        stxvd2x 50, 12, 3
        stxvd2x 54, 16, 3
        stxvd2x 55, 17, 3
        stxvd2x 59, 18, 3
        stxvd2x 60, 19, 3
        addi 3, 3, 16
        bdnz ntt_ppc_layer123_start
        addi 3, 3, -64
        addi 6, 14, 128
        addi 20, 8, 128
        addi 15, 4, 3120
        li 9, 0
        li 10, 16
        li 11, 32
        li 12, 48
        li 16, 8
        mtctr 16
        li 16, 64
        li 17, 80

ntt_ppc_layer4567_start:
        lvx 12, 9, 3
        lvx 13, 10, 3
        lvx 17, 11, 3
        lvx 18, 12, 3
        lvx 0, 0, 14
        lvx 1, 0, 8
        lvx 2, 0, 6
        lvx 4, 0, 20
        lvx 6, 10, 6
        lvx 11, 10, 20
        addi 14, 14, 16
        addi 8, 8, 16
        addi 6, 6, 32
        addi 20, 20, 32
        vmhraddshs 15, 17, 1, 3
        vmladduhm 16, 17, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 17, 12, 16
        vadduhm 12, 12, 16
        vmhraddshs 15, 18, 1, 3
        vmladduhm 16, 18, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 18, 13, 16
        vadduhm 13, 13, 16
        vmhraddshs 15, 13, 4, 3
        vmladduhm 16, 13, 2, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 13, 12, 16
        vadduhm 12, 12, 16
        vmhraddshs 15, 18, 11, 3
        vmladduhm 16, 18, 6, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 18, 17, 16
        vadduhm 17, 17, 16
        vmrgew 22, 13, 12
        vmrgow 23, 13, 12
        vmrgew 27, 18, 17
        vmrgow 28, 18, 17
        xxmrgld 44, 60, 55
        xxmrgld 45, 59, 54
        xxmrghd 49, 60, 55
        xxmrghd 50, 59, 54
        lvx 0, 0, 15
        lvx 1, 10, 15
        lvx 2, 11, 15
        lvx 4, 12, 15
        lvx 6, 16, 15
        lvx 11, 17, 15
        addi 15, 15, 96
        vmhraddshs 15, 17, 1, 3
        vmladduhm 16, 17, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 17, 12, 16
        vadduhm 12, 12, 16
        vmhraddshs 15, 18, 1, 3
        vmladduhm 16, 18, 0, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 18, 13, 16
        vadduhm 13, 13, 16
        vmhraddshs 15, 13, 4, 3
        vmladduhm 16, 13, 2, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 13, 12, 16
        vadduhm 12, 12, 16
        vmhraddshs 15, 18, 11, 3
        vmladduhm 16, 18, 6, 3
        vmladduhm 16, 15, 5, 16
        vsubuhm 18, 17, 16
        vadduhm 17, 17, 16
        vmrgew 22, 13, 12
        vmrgow 23, 13, 12
        vmrgew 27, 18, 17
        vmrgow 28, 18, 17
        xxmrgld 44, 60, 55
        xxmrgld 45, 59, 54
        xxmrghd 49, 60, 55
        xxmrghd 50, 59, 54
        stvx 12, 9, 3
        stvx 13, 10, 3
        stvx 17, 11, 3
        stvx 18, 12, 3
        addi 3, 3, 64
        bdnz ntt_ppc_layer4567_start
        addi 3, 3, -512
        li 10, 128
        li 11, 144
        li 12, 160
        li 14, 176
        li 15, 192
        li 16, 208
        lxvd2x 52, 10, 1
        lxvd2x 53, 11, 1
        lxvd2x 54, 12, 1
        lxvd2x 55, 14, 1
        lxvd2x 56, 15, 1
        lxvd2x 57, 16, 1
        li 10, 224
        li 11, 240
        li 12, 256
        li 14, 272
        li 15, 288
        li 16, 304
        lxvd2x 58, 10, 1
        lxvd2x 59, 11, 1
        lxvd2x 60, 12, 1
        lxvd2x 61, 14, 1
        lxvd2x 62, 15, 1
        lxvd2x 63, 16, 1
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

MLK_ASM_FN_SIZE(ntt_ppc_asm)

#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
