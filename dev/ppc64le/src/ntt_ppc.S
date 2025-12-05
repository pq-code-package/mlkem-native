/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Copyright 2025- IBM Corp.
 *
 * ===================================================================================
 * Written by Danny Tsen <dtsen@us.ibm.com>
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "consts.h"

#define V_QINV  2
#define V_NMKQ  5
#define V_Z0    7
#define V_Z1    8
#define V_Z2    9
#define V_Z3    10
#define V_ZETA  10

.machine "any"
.text

.macro SAVE_REGS
        stdu    r1, -352(r1)
        mflr    r0
        std     r14, 56(r1)
        std     r15, 64(r1)
        std     r16, 72(r1)
        std     r17, 80(r1)
        std     r18, 88(r1)
        std     r19, 96(r1)
        std     r20, 104(r1)
        std     r21, 112(r1)
        li      r10, 128
        li      r11, 144
        li      r12, 160
        li      r14, 176
        li      r15, 192
        li      r16, 208
        stxvx   32+v20, r10, r1
        stxvx   32+v21, r11, r1
        stxvx   32+v22, r12, r1
        stxvx   32+v23, r14, r1
        stxvx   32+v24, r15, r1
        stxvx   32+v25, r16, r1
        li      r10, 224
        li      r11, 240
        li      r12, 256
        li      r14, 272
        li      r15, 288
        li      r16, 304
        stxvx   32+v26, r10, r1
        stxvx   32+v27, r11, r1
        stxvx   32+v28, r12, r1
        stxvx   32+v29, r14, r1
        stxvx   32+v30, r15, r1
        stxvx   32+v31, r16, r1
.endm

.macro RESTORE_REGS
        li      r10, 128
        li      r11, 144
        li      r12, 160
        li      r14, 176
        li      r15, 192
        li      r16, 208
        lxvx    32+v20, r10, r1
        lxvx    32+v21, r11, r1
        lxvx    32+v22, r12, r1
        lxvx    32+v23, r14, r1
        lxvx    32+v24, r15, r1
        lxvx    32+v25, r16, r1
        li      r10, 224
        li      r11, 240
        li      r12, 256
        li      r14, 272
        li      r15, 288
        li      r16, 304
        lxvx    32+v26, r10, r1
        lxvx    32+v27, r11, r1
        lxvx    32+v28, r12, r1
        lxvx    32+v29, r14, r1
        lxvx    32+v30, r15, r1
        lxvx    32+v31, r16, r1
        ld      r14, 56(r1)
        ld      r15, 64(r1)
        ld      r16, 72(r1)
        ld      r17, 80(r1)
        ld      r18, 88(r1)
        ld      r19, 96(r1)
        ld      r20, 104(r1)
        ld      r21, 112(r1)

        mtlr    r0
        addi    r1, r1, 352
.endm

/*
 * Init_Coeffs_offset: initial offset setup for the coeeficient array.
 *
 * start: beginning of the offset to the coefficient array.
 * next: Next offset.
 * len: Index difference between coefficients.
 *
 * r7: len * 2, each coefficient component is 2 bytes.
 *
 * registers used for offset to coefficients, r[j] and r[j+len]
 * R9: offset to r0 = j
 * R16: offset to r1 = r0 + next
 * R18: offset to r2 = r1 + next
 * R20: offset to r3 = r2 + next
 *
 * R10: offset to r'0 = r0 + len*2
 * R17: offset to r'1 = r'0 + step
 * R19: offset to r'2 = r'1 + step
 * R21: offset to r'3 = r'2 + step
 *
 */
.macro Init_Coeffs_offset start next
        li      r9, \start         /* first offset to j */
        add     r10, r7, r9        /* J + len*2 */
        addi    r16, r9, \next
        addi    r17, r10, \next
        addi    r18, r16, \next
        addi    r19, r17, \next
        addi    r20, r18, \next
        addi    r21, r19, \next
.endm

/*
 * Load coefficient in r[j+len] (r') vectors from offset, R10, R17, R19 and R21
 *  r[j+len]: V13, V18, V23, V28
 */
.macro Load_4Rjp
        lxvd2x  32+v13, r3, r10    /* V13: vector r'0 */
        lxvd2x  32+v18, r3, r17    /* V18: vector for r'1 */
        lxvd2x  32+v23, r3, r19    /* V23: vector for r'2 */
        lxvd2x  32+v28, r3, r21    /* V28: vector for r'3 */
.endm

/*
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *  rjlen0, rjlen1, rjlen2, rjlen3, rjlen4, rjlen5, rjlen6, rjlen7
 */
.macro Load_4Coeffs start next
        Init_Coeffs_offset \start \next
        Load_4Rjp
.endm

/*
 * Load 2 - 2 - 2 - 2 layout
 *
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *    rj0, rj1, rjlen2, rjlen3, rj4, rj5, rjlen6, arlen7
 *    rj8, rj9, rjlen10, rjlen11, rj12, rj13, rjlen14, rjlen15
 *  Each vmrgew and vmrgow will transpose vectors as,
 *  r[j]=      rj0, rj1, rj8, rj9, rj4, rj5, rj12, rj13
 *  r[j+len]=  rjlen2, rjlen3, rjlen10, rjlen11, rjlen6, arlen7, rjlen14, rjlen15
 *
 *  r[j+len]: V13, V18, V23, V28
 *  r[j]: V12, V17, V22, V27
 *
 * In order to do the coefficients computation, zeta vector will arrange
 * in the proper order to match the multiplication.
 */
.macro Load_L24Coeffs
        lxvd2x     32+v25, 0, r5
        lxvd2x     32+v26, r10, r5
        vmrgew v13, v25, v26
        vmrgow v12, v25, v26
        lxvd2x     32+v25, r11, r5
        lxvd2x     32+v26, r12, r5
        vmrgew v18, v25, v26
        vmrgow v17, v25, v26
        lxvd2x     32+v25, r15, r5
        lxvd2x     32+v26, r16, r5
        vmrgew v23, v25, v26
        vmrgow v22, v25, v26
        lxvd2x     32+v25, r17, r5
        lxvd2x     32+v26, r18, r5
        vmrgew v28, v25, v26
        vmrgow v27, v25, v26
.endm

/*
 * Load 4 - 4 layout
 *
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *  rj0, rj1, rj2, rj3, rjlen4, rjlen5, rjlen6, rjlen7
 *  rj8, rj9, rj10, rj11, rjlen12, rjlen13, rjlen14, rjlen15
 *
 *  Each xxpermdi will transpose vectors as,
 *  rjlen4, rjlen5, rjlen6, rjlen7, rjlen12, rjlen13, rjlen14, rjlen15
 *  rj0, rj1, rj2, rj3, rj8, rj9, rj10, rj11
 *
 * In order to do the coefficients computation, zeta vector will arrange
 * in the proper order to match the multiplication.
 */
.macro Load_L44Coeffs
        lxvd2x     vs1, 0, r5
        lxvd2x     vs2, r10, r5
        xxpermdi 32+v13, vs2, vs1, 3
        xxpermdi 32+v12, vs2, vs1, 0
        lxvd2x     vs3, r11, r5
        lxvd2x     vs4, r12, r5
        xxpermdi 32+v18, vs4, vs3, 3
        xxpermdi 32+v17, vs4, vs3, 0
        lxvd2x     vs1, r15, r5
        lxvd2x     vs2, r16, r5
        xxpermdi 32+v23, vs2, vs1, 3
        xxpermdi 32+v22, vs2, vs1, 0
        lxvd2x     vs3, r17, r5
        lxvd2x     vs4, r18, r5
        xxpermdi 32+v28, vs4, vs3, 3
        xxpermdi 32+v27, vs4, vs3, 0
.endm

/*
 * montgomery_reduce
 * t = a * QINV
 * t = (a - (int32_t)t*_MLKEM_Q) >> 16
 *
 * -----------------------------------
 * MREDUCE_4X(_vz0, _vz1, _vz2, _vz3)
 */
.macro MREDUCE_4X _vz0 _vz1 _vz2 _vz3
        /* fqmul = zeta * coefficient
           Modular multification bond by 2^16 * q in abs value */
        vmladduhm v15, v13, \_vz0, v3
        vmladduhm v20, v18, \_vz1, v3
        vmladduhm v25, v23, \_vz2, v3
        vmladduhm v30, v28, \_vz3, v3

        /* Signed multiply-high-round; outputs are bound by 2^15 * q in abs value */
        vmhraddshs v14, v13, \_vz0, v3
        vmhraddshs v19, v18, \_vz1, v3
        vmhraddshs v24, v23, \_vz2, v3
        vmhraddshs v29, v28, \_vz3, v3

        vmladduhm v15, v15, V_QINV, v3
        vmladduhm v20, v20, V_QINV, v3
        vmladduhm v25, v25, V_QINV, v3
        vmladduhm v30, v30, V_QINV, v3

        vmhraddshs v15, v15, V_NMKQ, v14
        vmhraddshs v20, v20, V_NMKQ, v19
        vmhraddshs v25, v25, V_NMKQ, v24
        vmhraddshs v30, v30, V_NMKQ, v29

        /* Shift right 1 bit */
        vsrah v13, v15, v4
        vsrah v18, v20, v4
        vsrah v23, v25, v4
        vsrah v28, v30, v4
.endm

/*
 * Load 4 r[j] (r) coefficient vectors:
 *   Load coefficient in vectors from offset, R9, R16, R18 and R20
 *  r[j]: V12, V17, V22, V27
 */
.macro Load_4Rj
        lxvd2x  32+v12, r3, r9     /* V12: vector r0 */
        lxvd2x  32+v17, r3, r16    /* V17: vector r1 */
        lxvd2x  32+v22, r3, r18    /* V22: vector r2 */
        lxvd2x  32+v27, r3, r20    /* V27: vector r3 */
.endm

/*
 * Compute final final r[j] and r[j+len]
 *  final r[j+len]: V16, V21, V26, V31
 *  final r[j]: V15, V20, V25, V30
 */
.macro Compute_4Coeffs
        /* Since the result of the Montgomery multiplication is bounded
           by q in absolute value.
           Finally to complete the final update of the results with add/sub
           r[j] = r[j] + t.
           r[j+len] = r[j] - t
         */
        vsubuhm v16, v12, v13
        vadduhm v15, v13, v12
        vsubuhm v21, v17, v18
        vadduhm v20, v18, v17
        vsubuhm v26, v22, v23
        vadduhm v25, v23, v22
        vsubuhm v31, v27, v28
        vadduhm v30, v28, v27
.endm

.macro Write_One
        stxvd2x 32+v15, r3, r9
        stxvd2x 32+v16, r3, r10
        stxvd2x 32+v20, r3, r16
        stxvd2x 32+v21, r3, r17
        stxvd2x 32+v25, r3, r18
        stxvd2x 32+v26, r3, r19
        stxvd2x 32+v30, r3, r20
        stxvd2x 32+v31, r3, r21
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL44
        Compute_4Coeffs
        xxpermdi vs0, 32+v15, 32+v16, 3
        xxpermdi vs1, 32+v15, 32+v16, 0
        xxpermdi vs2, 32+v20, 32+v21, 3
        xxpermdi vs3, 32+v20, 32+v21, 0
        xxpermdi vs4, 32+v25, 32+v26, 3
        xxpermdi vs5, 32+v25, 32+v26, 0
        xxpermdi vs6, 32+v30, 32+v31, 3
        xxpermdi vs7, 32+v30, 32+v31, 0
        stxvd2x vs0, 0, r5
        stxvd2x vs1, r10, r5
        stxvd2x vs2, r11, r5
        stxvd2x vs3, r12, r5
        stxvd2x vs4, r15, r5
        stxvd2x vs5, r16, r5
        stxvd2x vs6, r17, r5
        stxvd2x vs7, r18, r5
.endm

/*
 * Transpose the final coefficients of 2-2-2-2 layout to the orginal
 * coefficient array order.
 */
.macro PermWriteL24
        Compute_4Coeffs
        vmrgew v10, v16, v15
        vmrgow v11, v16, v15
        vmrgew v12, v21, v20
        vmrgow v13, v21, v20
        vmrgew v14, v26, v25
        vmrgow v15, v26, v25
        vmrgew v16, v31, v30
        vmrgow v17, v31, v30
        stxvd2x 32+v10, 0, r5
        stxvd2x 32+v11, r10, r5
        stxvd2x 32+v12, r11, r5
        stxvd2x 32+v13, r12, r5
        stxvd2x 32+v14, r15, r5
        stxvd2x 32+v15, r16, r5
        stxvd2x 32+v16, r17, r5
        stxvd2x 32+v17, r18, r5
.endm

.macro Load_next_4zetas
        li      r10, 16
        li      r11, 32
        li      r12, 48
        lxvd2x  32+V_Z0, 0, r14
        lxvd2x  32+V_Z1, r10, r14
        lxvd2x  32+V_Z2, r11, r14
        lxvd2x  32+V_Z3, r12, r14
        addi    r14, r14, 64
.endm

/*
 * Re-ordering of the 4-4 layout zetas.
 * Swap double-words.
 */
.macro Perm_4zetas
        xxpermdi 32+V_Z0, 32+V_Z0, 32+V_Z0, 2
        xxpermdi 32+V_Z1, 32+V_Z1, 32+V_Z1, 2
        xxpermdi 32+V_Z2, 32+V_Z2, 32+V_Z2, 2
        xxpermdi 32+V_Z3, 32+V_Z3, 32+V_Z3, 2
.endm

.macro NTT_MREDUCE_4X start next _vz0 _vz1 _vz2 _vz3
        Load_4Coeffs \start, \next
        MREDUCE_4x \_vz0, \_vz1, \_vz2, \_vz3
        Load_4Rj
        Compute_4Coeffs
        Write_One
.endm

/*
 * mlk_ntt_ppc(int16_t *r)
 */
.global MLK_ASM_NAMESPACE(ntt_ppc)
.align 4
MLK_ASM_FN_SYMBOL(ntt_ppc)

        SAVE_REGS

        /* load MLKEM_Q */
        lvx     V_NMKQ,0,r4

        /* Register 14 as pointer to zetas array */
        addi    r14, r4, ZETA_NTT_OFFSET

        vxor    v3, v3, v3
        vspltish v4, 1

        li      r10, QINV_OFFSET
        lvx     V_QINV, r10, r4

.align 4
        /*
         * Compute coefficients of the NTT based on the following loop.
         *   for (len = 128; len ≥ 2; len =  len/2)
         *
         * 1. len = 128, start = 0
         */
        li      r7, 256          /* len * 2 */
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16

        NTT_MREDUCE_4X 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 64, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 192, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

.align 4
        /*
         * 2. len = 64, start = 0, 128
         * k += 2
         */
        li      r7, 128
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        NTT_MREDUCE_4X 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 64, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        NTT_MREDUCE_4X 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
        NTT_MREDUCE_4X 320, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

.align 4
        /*
         * 3. len = 32, start = 0, 64, 128, 192
         * k += 4
         */
        li      r7, 64
        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        NTT_MREDUCE_4X 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        NTT_MREDUCE_4X 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        NTT_MREDUCE_4X 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

        lvx     V_ZETA, 0, r14
        addi    r14, r14, 16
        NTT_MREDUCE_4X 384, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA

.align 4
        /*
         * 4. len = 16, start = 0, 32, 64,,...160, 192, 224
         * k += 8
         */
        li      r7, 32
        Load_next_4zetas
        NTT_MREDUCE_4X 0, 64, V_Z0, V_Z1, V_Z2, V_Z3
        NTT_MREDUCE_4X 16, 64, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 256, 64, V_Z0, V_Z1, V_Z2, V_Z3
        NTT_MREDUCE_4X  272, 64, V_Z0, V_Z1, V_Z2, V_Z3

.align 4
        /*
         * 5. len = 8, start = 0, 16, 32, 48,...208, 224, 240
         * k += 16
         */
        li      r7, 16
        Load_next_4zetas
        NTT_MREDUCE_4X 0, 32, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 128, 32, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 256, 32, V_Z0, V_Z1, V_Z2, V_Z3

        Load_next_4zetas
        NTT_MREDUCE_4X 384, 32, V_Z0, V_Z1, V_Z2, V_Z3

        /*
         * 6. len = 4, start = 0, 8, 16, 24,...232, 240, 248
         * k += 32
         * Load zeta vectors in 4-4 layout
         */
        li      r15, 4
        mtctr   r15
        mr      r5, r3                 /* Let r5 points to coefficient array */
        li      r7, 8

        li      r10, 16
        li      r11, 32
        li      r12, 48
        li      r15, 64
        li      r16, 80
        li      r17, 96
        li      r18, 112

.align 4
ntt_ppc__Len4:
        Load_next_4zetas
        Perm_4zetas
        Load_L44Coeffs
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3
        PermWriteL44
        addi    r5, r5, 128

        bdnz    ntt_ppc__Len4

        /*
         * 7. len = 2, start = 0, 4, 8, 12,...244, 248, 252
         * k += 64
         * Load zeta vectors in 2-2-2-2 layout
         */

        li      r8, 4
        mtctr   r8
        mr      r5, r3                  /* Let r5 points to coefficient array */
        li      r7, 4

.align 4
ntt_ppc__Len2:
        Load_next_4zetas
        Load_L24Coeffs
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3
        PermWriteL24
        addi    r5, r5, 128

        bdnz    ntt_ppc__Len2

        RESTORE_REGS
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V_QINV
#undef V_NMKQ
#undef V_ZETA

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
