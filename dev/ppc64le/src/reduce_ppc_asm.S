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
/* simpasm: header-end */

#include "consts.h"

/*
 * For the VSX register-naming convention (FPR/VR vs. the unified VSR
 * namespace, and the `32+V_FOO` syntax used to name a VR from a VSX-form
 * instruction), see the primer at the top of ntt_ppc_asm.S /
 * intt_ppc_asm.S.
 */

/*
 * Optimization status (#1724):
 *  1. DONE -- High-multiply + shift replaces the full-width multiply.
 *     barrett_reduce_4x now forms t = round(a*20159/2^26) entirely in the
 *     8-halfword domain: vmhaddshs gives the non-rounding high product
 *     (a*20159)>>15 plus the 2^10 rounding bias; vsrah #11 finishes the
 *     >>26. No vmul{o,e}sh widen, no xxmrg interleave, no word-domain
 *     bias/shift, no vpkuwum pack. Mirror this in intt_ppc_asm.S's
 *     barrett_reduce_4x in lockstep (same scheme).
 *  2. DONE -- Uses -Q (MLK_PPC_NQ_OFFSET) so the closing vmladduhm computes
 *     a + t*(-Q) = a - t*Q directly; the explicit negate (vsubuhm with
 *     V_ZERO) and V_ZERO itself are gone.
 *  3. TODO (follow-up, validate after #1/#2) -- Trim the save/restore and
 *     224-byte frame. The optimized macro no longer needs the word-domain
 *     temporaries, so the working set can be confined to volatile VRs
 *     (v0-v19) and the v20-v24 / r14-r16 spills dropped. Deferred so the
 *     algorithm change can be exhaustively validated first without also
 *     perturbing register allocation / ABI frame.
 *
 * !! VALIDATION GATE: exhaustively test all 2^16 int16 inputs vs the C
 *    reference (every output in [0, MLKEM_Q)) on real POWER8 before PR.
 *    The two-stage rounding (>>15 then >>11) matches aarch64's accepted
 *    sqdmulh+srshr scheme but is not bit-identical to one-stage >>26 in
 *    every case; Barrett only tolerates +/-1 in t within bounds.
 */

/*
 * poly_reduce: Reduces every coefficient of a polynomial to its unsigned
 *              canonical representative in [0, MLKEM_Q).
 */

/* Barrett-reduce constants (materialized at entry, VR-resident across body). */
#define V20159  0   /* round(2^26 / MLKEM_Q) = 20159, Barrett estimate factor */
#define V_NEGQ  1   /* -MLKEM_Q (-3329), for a + t*(-Q) = a - t*Q             */
#define V_1024  2   /* 2^10, rounding bias for the >> 11 stage               */
#define V_11    3   /* shift amount 11 (halfword right-shift for vsrah)       */
#define V_Q     7   /* +MLKEM_Q, kept for the To_unsigned_16 pass below       */

#define rinp    3   /* in/out polynomial pointer */
#define qinp    4   /* qdata (constant table) pointer */

#define vdata1   8
#define vdata2   12
#define vdata3   16
#define vdata4   20

/* Barrett estimate t, one per loaded vector (8 halfword lanes each). */
#define vt1      5
#define vt2      6
#define vt3      10
#define vt4      11

#define vout0    21
#define vout1    22
#define vout2    23
#define vout3    24
#define vout4    4
#define vout5    9
#define vout6    13
#define vout7    17

.text

/*
 * Barrett reduction (4 lanes). Loads 4 consecutive 16-byte coefficient
 * vectors from rinp, advances rinp by 64, and reduces each lane into the
 * signed canonical range (-MLKEM_Q/2, MLKEM_Q/2):
 *
 *   t = ( (a*20159) >> 15 + 2^10 ) >> 11   ==  round(a * 20159 / 2^26)
 *       \______ vmhaddshs ______/  \vsrah/
 *   _vi = a + t*(-MLKEM_Q) = a - t*MLKEM_Q
 *
 * No saturation in vmhaddshs: |(a*20159)>>15| <= 20159, +1024 <= 21183 < 2^15.
 * The original a values stay in vdata1..4 for the closing FMA. Outputs land
 * in _v0.._v3.
 */
.macro barrett_reduce_4x _v0, _v1, _v2, _v3
        lxvd2x  32+vdata1, 0, rinp
        lxvd2x  32+vdata2, 14, rinp
        lxvd2x  32+vdata3, 15, rinp
        lxvd2x  32+vdata4, 16, rinp
        addi    rinp, rinp, 64
        /* t_hi = (a*20159) >> 15 + 2^10  (non-saturating high mul + bias) */
        vmhaddshs vt1, vdata1, V20159, V_1024
        vmhaddshs vt2, vdata2, V20159, V_1024
        vmhaddshs vt3, vdata3, V20159, V_1024
        vmhaddshs vt4, vdata4, V20159, V_1024
        /* t = t_hi >> 11  (completes round(a*20159 / 2^26)) */
        vsrah   vt1, vt1, V_11
        vsrah   vt2, vt2, V_11
        vsrah   vt3, vt3, V_11
        vsrah   vt4, vt4, V_11
        /* a + t*(-Q) = a - t*MLKEM_Q  (one FMA per lane, no negate/pack) */
        vmladduhm \_v0, vt1, V_NEGQ, vdata1
        vmladduhm \_v1, vt2, V_NEGQ, vdata2
        vmladduhm \_v2, vt3, V_NEGQ, vdata3
        vmladduhm \_v3, vt4, V_NEGQ, vdata4
.endm

.macro Write_8X
        stxvd2x 32+vout0, qinp, rinp
        stxvd2x 32+vout1, 5, rinp
        stxvd2x 32+vout2, 6, rinp
        stxvd2x 32+vout3, 7, rinp
        stxvd2x 32+vout4, 8, rinp
        stxvd2x 32+vout5, 9, rinp
        stxvd2x 32+vout6, 10, rinp
        stxvd2x 32+vout7, 11, rinp
.endm

/*
 * Working registers for the unsigned-canonical pass (To_unsigned_16).
 * This is a separate allocation from barrett_reduce_4x above.
 */
#define vu_data1  12    /* input: signed canonical in (-MLKEM_Q/2, MLKEM_Q/2) */
#define vu_data2  13
#define vu_data3  14
#define vu_data4  15
#define vu_addq1  7     /* coeff +MLKEM_Q, the chosen when input < 0 */
#define vu_addq2  8
#define vu_addq3  5
#define vu_addq4  6
#define vu_res1   1     /* sign mask -> selected result */
#define vu_res2   0
#define vu_res3   3
#define vu_res4   2
#define vu_zero   9     /* zero: compare target for the sign test */
#define vu_signsh 10    /* 15: a logical >>15 leaves just the sign bit */
#define vu_q      11    /* +MLKEM_Q copy (taken from V_Q before this pass) */

/*
 * Conditional addition to get unsigned canonical representative
 */
.macro To_unsigned_16
        lxvd2x    32+vu_data1, 0, rinp
        lxvd2x    32+vu_data2, 14, rinp
        lxvd2x    32+vu_data3, 15, rinp
        lxvd2x    32+vu_data4, 16, rinp
        addi    rinp, rinp, 64
        vsrh    vu_res1, vu_data1, vu_signsh
        vsrh    vu_res2, vu_data2, vu_signsh
        vsrh    vu_res3, vu_data3, vu_signsh
        vsrh    vu_res4, vu_data4, vu_signsh
        vadduhm vu_addq1, vu_data1, vu_q
        vadduhm vu_addq2, vu_data2, vu_q
        vadduhm vu_addq3, vu_data3, vu_q
        vadduhm vu_addq4, vu_data4, vu_q
        /* mask = (sign == 0) ? all-ones : 0, i.e. set when non-negative */
        vcmpequh vu_res1, vu_res1, vu_zero
        vcmpequh vu_res2, vu_res2, vu_zero
        vcmpequh vu_res3, vu_res3, vu_zero
        vcmpequh vu_res4, vu_res4, vu_zero
        /* xxsel D,A,B,C: D = (C set) ? B : A -> non-negative keeps coeff,
           negative takes coeff+q */
        xxsel   32+vu_res1, 32+vu_addq1, 32+vu_data1, 32+vu_res1
        xxsel   32+vu_res2, 32+vu_addq2, 32+vu_data2, 32+vu_res2
        xxsel   32+vu_res3, 32+vu_addq3, 32+vu_data3, 32+vu_res3
        xxsel   32+vu_res4, 32+vu_addq4, 32+vu_data4, 32+vu_res4
        /* Store back in place; r8..r11 hold byte offsets -64..-16. */
        stxvd2x 32+vu_res3, 10, rinp
        stxvd2x 32+vu_res4, 11, rinp
        stxvd2x 32+vu_res1, 8, rinp
        stxvd2x 32+vu_res2, 9, rinp
.endm

/*
 * mlk_reduce_ppc_asm(int16_t *r, const int16_t *qdata)
 *   Barrett-reduce all MLKEM_N coefficients to signed canonical range,
 *   then fold into [0, MLKEM_Q). r3 = r, r4 = qdata.
 *
 * Leaf function; LR is held in r0 across the body. The 224-byte frame
 * still spills r14-r16 and v20-v24 (vdata4 + vout0..3 remain mapped onto
 * non-volatile VRs); TODO #3 (frame trim) drops these after the algorithm
 * is validated.
 */
.global MLK_ASM_NAMESPACE(reduce_ppc_asm)
.balign 16
MLK_ASM_FN_SYMBOL(reduce_ppc_asm)
        stdu    1, -224(1)
        mflr    0
        std     14, 96(1)
        std     15, 104(1)
        std     16, 112(1)
        li      6, 128
        li      7, 144
        li      8, 160
        li      9, 176
        li      10, 192
        stxvx   32+20, 6, 1
        stxvx   32+21, 7, 1
        stxvx   32+22, 8, 1
        stxvx   32+23, 9, 1
        stxvx   32+24, 10, 1

        /* Load Barrett constants from the qdata table (qinp = r4 still
           points at qdata here, before it is reused as a store offset). */
        li      6, MLK_PPC_C20159_OFFSET
        li      7, MLK_PPC_NQ_OFFSET
        li      8, MLK_PPC_Q_OFFSET
        lxvx    32+V20159, 6, qinp
        lxvx    32+V_NEGQ, 7, qinp
        lxvx    32+V_Q,    8, qinp

        /* V_11 = 11 (shift amount); V_1024 = 1 << 10 = 2^10 (rounding bias).
           VR4 is scratch here (it becomes vout4, not live until the loop). */
        vspltish V_11, 11
        vspltish V_1024, 1
        vspltish 4, 10
        vslh    V_1024, V_1024, 4

        /* r4..r11 (r4 = qinp, reused now that qdata is loaded): store-back
           byte offsets -128..-16, consumed by Write_8X after rinp has
           advanced 128 bytes over the two reduced batches. */
        li      qinp, -128
        li      5, -112
        li      6, -96
        li      7, -80
        li      8, -64
        li      9, -48
        li      10, -32
        li      11, -16

        /* r14..r16: byte offsets 16/32/48 for the 4 vectors loaded per
           reduce call (relative to its own rinp). */
        li      14, 16
        li      15, 32
        li      16, 48

        /* Reduce 256 coefficients = 4 iterations x 2 batches x 8 lanes. */
        barrett_reduce_4x vout0, vout1, vout2, vout3
        barrett_reduce_4x vout4, vout5, vout6, vout7
        Write_8X

        barrett_reduce_4x vout0, vout1, vout2, vout3
        barrett_reduce_4x vout4, vout5, vout6, vout7
        Write_8X

        barrett_reduce_4x vout0, vout1, vout2, vout3
        barrett_reduce_4x vout4, vout5, vout6, vout7
        Write_8X

        barrett_reduce_4x vout0, vout1, vout2, vout3
        barrett_reduce_4x vout4, vout5, vout6, vout7
        Write_8X

.balign 16
        /*
         * Fold the signed canonical coefficients into [0, MLKEM_Q).
         * Rewind rinp to the start of the buffer and set up the constants
         * To_unsigned_16 needs: zero, the >>15 sign-extract amount, and the
         * +MLKEM_Q copy carried in V_Q from entry.
         */
        addi    rinp, rinp, -512
        vxor    vu_zero, vu_zero, vu_zero
        vspltish vu_signsh, 15
        vmr     vu_q, V_Q

        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16
        To_unsigned_16

        ld      14, 96(1)
        ld      15, 104(1)
        ld      16, 112(1)
        li      6, 128
        li      7, 144
        li      8, 160
        li      9, 176
        li      10, 192
        lxvx    32+20, 6, 1
        lxvx    32+21, 7, 1
        lxvx    32+22, 8, 1
        lxvx    32+23, 9, 1
        lxvx    32+24, 10, 1
        mtlr    0
        addi    1, 1, 224
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros. */
#undef V20159
#undef V_NEGQ
#undef V_1024
#undef V_11
#undef V_Q
#undef rinp
#undef qinp
#undef vdata1
#undef vdata2
#undef vdata3
#undef vdata4
#undef vt1
#undef vt2
#undef vt3
#undef vt4
#undef vout0
#undef vout1
#undef vout2
#undef vout3
#undef vout4
#undef vout5
#undef vout6
#undef vout7
#undef vu_data1
#undef vu_data2
#undef vu_data3
#undef vu_data4
#undef vu_addq1
#undef vu_addq2
#undef vu_addq3
#undef vu_addq4
#undef vu_res1
#undef vu_res2
#undef vu_res3
#undef vu_res4
#undef vu_zero
#undef vu_signsh
#undef vu_q

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */
