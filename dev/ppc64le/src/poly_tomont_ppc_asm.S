/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) IBM Corp. 2025, 2026
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * Written by Danny Tsen <dtsen@us.ibm.com>
 * poly_tomont frame trim (#1722) by Scott Boudreaux.
 */

/*
 * Poly_tomont: Inplace conversion of all coefficients of a polynomial
 *              from normal domain to Montgomery domain
 *
 * Arguments:*r: pointer to input/output polynomial
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && defined(__POWER8_VECTOR__)
/* simpasm: header-end */

#include "consts.h"

/*
 * For the VSX register-naming convention (FPR/VR vs. the unified VSR
 * namespace, and the `32+V_FOO` syntax used to name a VR from a VSX-form
 * instruction), see the primer at the top of ntt_ppc_asm.S /
 * intt_ppc_asm.S.
 */

#define rinp 3   /* input/output polynomial pointer */

#define V_FACTOR     0
#define V_FACTOR_TW  2
#define V_ZERO       3
#define V_NMKQ       5

#define vdata1 13
#define vdata2 18
#define vdata3 23
#define vdata4 7

#define vtmp1  14
#define vtmp2  19
#define vtmp3  24
#define vtmp4  8

#define vresult1  27
#define vresult2  28
#define vresult3  29
#define vresult4  30

.text

/*
 * Barrett multiplication by R = 2^16 mod q,
 * mapping each coefficient to the Montgomery domain.
 *   For each lane (a in vdata1..4):
 *     t      = vmhraddshs(a, V_FACTOR_TW, 0) = round(a*factor_tw / 2^15)
 *     a_lo   = vmladduhm(a, V_FACTOR, 0)     = (a*factor) mod 2^16
 *     result = vmladduhm(t, -q, a_lo)        = a*factor - t*q (mod 2^16)
 *   Loads 4 consecutive 16-byte vectors from rinp and advances rinp by 64;
 *   results in _v0.._v3.
 */
.macro barrett_tomont_4x _v0, _v1, _v2, _v3
        lxvd2x  32+vdata1, 0, rinp
        addi    rinp, rinp, 16
        lxvd2x  32+vdata2, 0, rinp
        addi    rinp, rinp, 16
        lxvd2x  32+vdata3, 0, rinp
        addi    rinp, rinp, 16
        lxvd2x  32+vdata4, 0, rinp
        addi    rinp, rinp, 16

        vmhraddshs vtmp1, vdata1, V_FACTOR_TW, V_ZERO
        vmhraddshs vtmp2, vdata2, V_FACTOR_TW, V_ZERO
        vmhraddshs vtmp3, vdata3, V_FACTOR_TW, V_ZERO
        vmhraddshs vtmp4, vdata4, V_FACTOR_TW, V_ZERO

        vmladduhm vdata1, vdata1, V_FACTOR, V_ZERO
        vmladduhm vdata2, vdata2, V_FACTOR, V_ZERO
        vmladduhm vdata3, vdata3, V_FACTOR, V_ZERO
        vmladduhm vdata4, vdata4, V_FACTOR, V_ZERO

        vmladduhm \_v0, vtmp1, V_NMKQ, vdata1
        vmladduhm \_v1, vtmp2, V_NMKQ, vdata2
        vmladduhm \_v2, vtmp3, V_NMKQ, vdata3
        vmladduhm \_v3, vtmp4, V_NMKQ, vdata4
.endm

/* Store the 8 result vectors of one iteration. The index registers r4..r11
 * hold the byte offsets -128..-16 relative to the (already advanced) rinp. */
.macro Write_8X
        stxvd2x 32+vresult1, 4, rinp
        stxvd2x 32+vresult2, 5, rinp
        stxvd2x 32+vresult3, 6, rinp
        stxvd2x 32+vresult4, 7, rinp
        stxvd2x 32+vdata1, 8, rinp
        stxvd2x 32+vdata2, 9, rinp
        stxvd2x 32+vdata3, 10, rinp
        stxvd2x 32+vdata4, 11, rinp
.endm

.global MLK_ASM_NAMESPACE(poly_tomont_ppc_asm)
.balign 16
MLK_ASM_FN_SYMBOL(poly_tomont_ppc_asm)
        stdu    1, -224(1)
        mflr    0

        /*
         * #1722: save/restore ONLY the callee-saved VRs the body actually
         * clobbers -- v23 (vdata3), v24 (vtmp3), v27-v30 (vresult1..4).
         * The previous code also spilled v20,v21,v22,v25,v26 (5 dead
         * stxvx/lxvx pairs + 80 bytes of frame); those are never touched
         * (V_FACTOR/V_FACTOR_TW/V_ZERO/V_NMKQ and the rest map to volatile
         * VRs). Frame trimmed 320 -> 224. Algorithm is byte-identical.
         */
        li      6, 128
        li      7, 144
        li      8, 160
        li      9, 176
        li      10, 192
        li      11, 208
        stxvx   32+23, 6, 1
        stxvx   32+24, 7, 1
        stxvx   32+27, 8, 1
        stxvx   32+28, 9, 1
        stxvx   32+29, 10, 1
        stxvx   32+30, 11, 1

        li      6, MLK_PPC_NQ_OFFSET
        li      7, MLK_PPC_TOMONT_OFFSET
        li      8, MLK_PPC_TOMONT_TW_OFFSET
        lxvx    32+V_NMKQ, 6, 4
        lxvx    32+V_FACTOR, 7, 4
        lxvx    32+V_FACTOR_TW, 8, 4

        vxor    V_ZERO, V_ZERO, V_ZERO

        li      4, -128
        li      5, -112
        li      6, -96
        li      7, -80
        li      8, -64
        li      9, -48
        li      10, -32
        li      11, -16

        barrett_tomont_4x vresult1, vresult2, vresult3, vresult4
        barrett_tomont_4x vdata1, vdata2, vdata3, vdata4
        Write_8X

        barrett_tomont_4x vresult1, vresult2, vresult3, vresult4
        barrett_tomont_4x vdata1, vdata2, vdata3, vdata4
        Write_8X

        barrett_tomont_4x vresult1, vresult2, vresult3, vresult4
        barrett_tomont_4x vdata1, vdata2, vdata3, vdata4
        Write_8X

        barrett_tomont_4x vresult1, vresult2, vresult3, vresult4
        barrett_tomont_4x vdata1, vdata2, vdata3, vdata4
        Write_8X

        li      6, 128
        li      7, 144
        li      8, 160
        li      9, 176
        li      10, 192
        li      11, 208
        lxvx    32+23, 6, 1
        lxvx    32+24, 7, 1
        lxvx    32+27, 8, 1
        lxvx    32+28, 9, 1
        lxvx    32+29, 10, 1
        lxvx    32+30, 11, 1
        mtlr    0
        addi    1, 1, 224
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros. */
#undef rinp
#undef V_FACTOR
#undef V_FACTOR_TW
#undef V_ZERO
#undef V_NMKQ
#undef vdata1
#undef vdata2
#undef vdata3
#undef vdata4
#undef vtmp1
#undef vtmp2
#undef vtmp3
#undef vtmp4
#undef vresult1
#undef vresult2
#undef vresult3
#undef vresult4

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */
