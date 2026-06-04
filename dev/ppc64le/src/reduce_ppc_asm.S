/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) IBM Corp. 2025, 2026
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * Written by Danny Tsen <dtsen@us.ibm.com>
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
 * TODO (optimization opportunities).
 *
 * Items 1 and 2 should be applied in lockstep with the matching
 * barrett_reduce_4x in intt_ppc_asm.S, which uses the same scheme.
 *
 *  1. High-multiply + shift instead of the full-width multiply.
 *     barrett_reduce_4x splits a*20159 into odd/even halfword products
 *     (vmulosh/vmulesh), interleaves, biases, shifts and packs to form
 *     the estimate t. The aarch64 backend forms t in two halfword ops:
 *     a non-rounding high multiply then a rounding shift (sqdmulh +
 *     srshr #11). The ppc equivalent is vmhaddshs (non-rounding,
 *     (a*magic) >> 15) + rounding >> 11.
 *
 *  2. Use -Q (MLK_PPC_NQ_OFFSET) and drop the explicit negation.
 *     The tail negates t (vsubuhm t, V_ZERO, t) only so the closing
 *     vmladduhm with +MLKEM_Q subtracts. Loading -Q instead and keeping +t
 *     gives the same a - t*q in one fewer op per lane, and removes the
 *     V_ZERO vector (used here solely for that negation). -Q is already
 *     in the constant table.
 *
 *  3. Trim the save/restore (and the 224-byte frame) accordingly.
 *     v20-v24 / r14-r16 are spilled only because the full-width scheme
 *     of item 1 needs that many live vectors and offset registers. With
 *     item 1 the working set shrinks to volatile registers, so the
 *     prologue/epilogue spills and the stack frame can largely or wholly
 *     disappear. (Compare the clear-cut unconditional over-save flagged
 *     inline in poly_tomont_ppc_asm.S, which holds regardless of item 1.)
 */

/*
 * poly_reduce: Reduces every coefficient of a polynomial to its unsigned
 *              canonical representative in [0, MLKEM_Q).
 *
 *   Input  bound: each coefficient is an arbitrary int16_t (no precondition).
 *   Output bound: each coefficient is in [0, MLKEM_Q).
 *
 *   Implementation: Barrett reduction maps any int16_t input into the signed
 *   canonical range (-MLKEM_Q/2, MLKEM_Q/2); a conditional addition of
 *   MLKEM_Q (`To_unsigned_16`) then folds negative values into [0, MLKEM_Q).
 *
 * Arguments: *r: in/out pointer to an array of MLKEM_N int16_t coefficients
 *                (one polynomial in NTT or normal domain).
 */

/*
 * VR aliases for the Barrett-reduce constants. These name the registers;
 * their values are materialized at function entry and stay VR-resident
 * across the whole body (unlike intt_ppc_asm.S, which re-materializes
 * them from an FPR-anchored VSR stash each call):
 *   V20159 <- round(2^26 / MLKEM_Q) = 20159, the Barrett estimate factor.
 *   V_25   <- 2^25, the rounding bias added before the >> 26 shift.
 *   V_26   <- shift amount 26 (word right-shift count for vsraw).
 *   V_MKQ  <- +MLKEM_Q, subtracted via the final fused multiply-add.
 */
#define V20159  0
#define V_25    1
#define V_26    2
#define V_MKQ   3

#define rinp    3   /* in/out polynomial pointer */
#define qinp    4   /* qdata (constant table) pointer */

#define V_ZERO   7  /* zero; negation source for 0 - t */

#define vdata1   8
#define vdata2   12
#define vdata3   16
#define vdata4   20

/* 32-bit products a*20159, split across even/odd lanes. */
#define vprod_odd1  6
#define vprod_odd2  11
#define vprod_odd3  15
#define vprod_odd4  19

#define vprod_even1 5
#define vprod_even2 10
#define vprod_even3 14
#define vprod_even4 18

/* 32-bit products a*20159, in normal order. */
#define vt_prod_lo1 4
#define vt_prod_lo2 9
#define vt_prod_lo3 13
#define vt_prod_lo4 17

#define vt_prod_hi1 5
#define vt_prod_hi2 10
#define vt_prod_hi3 14
#define vt_prod_hi4 18

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
 *   t   = round(a * 20159 / 2^26)     Barrett estimate of a/MLKEM_Q
 *   _vi = a - t*MLKEM_Q
 *
 * The original a values are kept in vdata1..4 for the closing a - t*q.
 * V_ZERO must hold zero on entry (set once by the caller); it is used to
 * negate t. Outputs land in _v0.._v3.
 */
.macro barrett_reduce_4x _v0, _v1, _v2, _v3
        lxvd2x  32+vdata1, 0, rinp
        lxvd2x  32+vdata2, 14, rinp
        lxvd2x  32+vdata3, 15, rinp
        lxvd2x  32+vdata4, 16, rinp
        addi    rinp, rinp, 64
        /* Widen a*20159 to words. There is no 8-halfword->8-word multiply,
           so vmul{o,e}sh split the 8 coeffs into odd/even lanes (4 words
           each); each product is bound by 2^32 in abs value. */
        vmulosh vprod_odd1, vdata1, V20159
        vmulesh vprod_even1, vdata1, V20159
        vmulosh vprod_odd2, vdata2, V20159
        vmulesh vprod_even2, vdata2, V20159
        vmulosh vprod_odd3, vdata3, V20159
        vmulesh vprod_even3, vdata3, V20159
        vmulosh vprod_odd4, vdata4, V20159
        vmulesh vprod_even4, vdata4, V20159
        /* Interleave the odd/even word products back into coefficient
           order, forming the estimate t across vt_prod_lo (coeffs 0-3)
           and vt_prod_hi (coeffs 4-7). Since vt_prod_hi{i} aliases
           vprod_even{i}, xxmrglw must read vprod_even{i} before xxmrghw
           overwrites that register as vt_prod_hi{i} -- order is load-bearing. */
        xxmrglw 32+vt_prod_lo1, 32+vprod_even1, 32+vprod_odd1
        xxmrghw 32+vt_prod_hi1, 32+vprod_even1, 32+vprod_odd1
        xxmrglw 32+vt_prod_lo2, 32+vprod_even2, 32+vprod_odd2
        xxmrghw 32+vt_prod_hi2, 32+vprod_even2, 32+vprod_odd2
        xxmrglw 32+vt_prod_lo3, 32+vprod_even3, 32+vprod_odd3
        xxmrghw 32+vt_prod_hi3, 32+vprod_even3, 32+vprod_odd3
        xxmrglw 32+vt_prod_lo4, 32+vprod_even4, 32+vprod_odd4
        xxmrghw 32+vt_prod_hi4, 32+vprod_even4, 32+vprod_odd4
        /* Add the 2^25 rounding bias before the >> 26 shift. */
        vadduwm vt_prod_lo1, vt_prod_lo1, V_25
        vadduwm vt_prod_hi1, vt_prod_hi1, V_25
        vadduwm vt_prod_lo2, vt_prod_lo2, V_25
        vadduwm vt_prod_hi2, vt_prod_hi2, V_25
        vadduwm vt_prod_lo3, vt_prod_lo3, V_25
        vadduwm vt_prod_hi3, vt_prod_hi3, V_25
        vadduwm vt_prod_lo4, vt_prod_lo4, V_25
        vadduwm vt_prod_hi4, vt_prod_hi4, V_25
        /* Arithmetic shift right by 26 to finish t = round(a/MLKEM_Q). */
        vsraw   vt_prod_lo1, vt_prod_lo1, V_26
        vsraw   vt_prod_hi1, vt_prod_hi1, V_26
        vsraw   vt_prod_lo2, vt_prod_lo2, V_26
        vsraw   vt_prod_hi2, vt_prod_hi2, V_26
        vsraw   vt_prod_lo3, vt_prod_lo3, V_26
        vsraw   vt_prod_hi3, vt_prod_hi3, V_26
        vsraw   vt_prod_lo4, vt_prod_lo4, V_26
        vsraw   vt_prod_hi4, vt_prod_hi4, V_26
        /* Pack t back to halfwords (vt_prod_lo := [vt_prod_hi | vt_prod_lo])
           and negate it so the multiply-add below subtracts t*MLKEM_Q. */
        vpkuwum vt_prod_lo1, vt_prod_hi1, vt_prod_lo1
        vsubuhm vt_prod_lo1, V_ZERO, vt_prod_lo1
        vpkuwum vt_prod_lo2, vt_prod_hi2, vt_prod_lo2
        vsubuhm vt_prod_lo2, V_ZERO, vt_prod_lo2
        vpkuwum vt_prod_lo3, vt_prod_hi3, vt_prod_lo3
        vsubuhm vt_prod_lo3, V_ZERO, vt_prod_lo3
        vpkuwum vt_prod_lo4, vt_prod_hi4, vt_prod_lo4
        vsubuhm vt_prod_lo4, V_ZERO, vt_prod_lo4
        /* a + (-t)*MLKEM_Q = a - t*MLKEM_Q, the signed canonical representative
           in (-MLKEM_Q/2, MLKEM_Q/2). */
        vmladduhm \_v0, vt_prod_lo1, V_MKQ, vdata1
        vmladduhm \_v1, vt_prod_lo2, V_MKQ, vdata2
        vmladduhm \_v2, vt_prod_lo3, V_MKQ, vdata3
        vmladduhm \_v3, vt_prod_lo4, V_MKQ, vdata4
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
#define vu_q      11    /* +MLKEM_Q copy (V_MKQ reg is reused as vu_res3) */

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
 * spills the callee-saved registers actually used (r14-r16 and v20-v24):
 *
 *     [   0,   8)  -- caller's SP (back chain, set atomically by stdu)
 *     [  96, 120)  -- r14..r16  (3 x 8 bytes)
 *     [ 128, 208)  -- v20..v24  (5 x 16 bytes; vdata4 and vout0..3)
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

        vxor    V_ZERO, V_ZERO, V_ZERO

        li      6, MLK_PPC_Q_OFFSET
        li      7, MLK_PPC_C20159_OFFSET
        lxvx    32+V_MKQ, 6, qinp
        lxvx    32+V20159, 7, qinp

        /* Build the Barrett rounding constants: V_26 = 26 (shift amount),
           V_25 = 1 << 25 = 2^25 (rounding bias). v4/v5 are scratch. */
        vspltisw V_26, 13
        vadduwm V_26, V_26, V_26
        vspltisw 4, 1
        vsubuwm 5, V_26, 4
        vslw    V_25, 4, 5

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

        /* Reduce 256 coefficients = 4 iterations x 2 batches x 8 lanes.
           Batch A writes vout0..3 (parked), batch B writes vout4..7
           (in place in the vt_prod_lo regs), then Write_8X stores all 8. */
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
         * To_unsigned_16 needs: zero, the >>15 sign-extract amount, and a
         * +MLKEM_Q copy (V_MKQ's register is reused as a result lane inside).
         */
        addi    rinp, rinp, -512
        vxor    vu_zero, vu_zero, vu_zero
        vspltish vu_signsh, 15
        vmr     vu_q, V_MKQ

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

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V20159
#undef V_25
#undef V_26
#undef V_MKQ
#undef rinp
#undef qinp
#undef V_ZERO
#undef vdata1
#undef vdata2
#undef vdata3
#undef vdata4
#undef vprod_odd1
#undef vprod_odd2
#undef vprod_odd3
#undef vprod_odd4
#undef vprod_even1
#undef vprod_even2
#undef vprod_even3
#undef vprod_even4
#undef vt_prod_lo1
#undef vt_prod_lo2
#undef vt_prod_lo3
#undef vt_prod_lo4
#undef vt_prod_hi1
#undef vt_prod_hi2
#undef vt_prod_hi3
#undef vt_prod_hi4
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
