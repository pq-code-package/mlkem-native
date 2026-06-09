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
/*yaml
  Name: ntt_ppc_asm
  Description: PowerPC64 VSX forward NTT
  Signature: void mlk_ntt_ppc_asm(int16_t *r, const int16_t *qdata)
  ABI:
    r3:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t *r
      description: Input/output polynomial (256 x int16_t)
    r4:
      type: buffer
      size_bytes: 4144
      permissions: read-only
      c_parameter: const int16_t *qdata
      description: Precomputed constants (2072 x int16_t)
*/
/* simpasm: header-end */

#include "consts.h"

/*
 * VSX register naming
 * ===================
 *
 * POWER has two separate 32-entry SIMD/FP register files: f0..f31 (FPRs,
 * scalar FP) and v0..v31 (VRs, 128-bit Altivec/VMX vectors). They are
 * physically distinct -- writing v3 does not touch f3.
 *
 * VSX (Power ISA 2.06, POWER7+) added a single 64-entry 128-bit-wide VSR
 * namespace covering both legacy files via a non-overlapping mapping:
 *
 *   FPR f<i>  -- LOW 64 bits of vs<i>           (i in 0..31)
 *                upper 64 bits of vs<i> are new VSX state, ignored by
 *                legacy FP instructions
 *   VR  v<i>  -- ALL 128 bits of vs<32+i>       (i in 0..31)
 *
 * So vs0..vs31 are the FPR-anchored slots (scalar-FP at the low half),
 * and vs32..vs63 are exactly the VR file. v3 and f3 live in different
 * VSR slots (vs35 and vs3) and never alias each other.
 *
 * VSX-form instructions (xxlor / lxvx / stxvx / xxpermdi / ...) take 6-bit
 * operands and can address any of the 64 VSRs; Altivec instructions take
 * 5-bit operands and can only address v0..v31. To name VR `V_FOO` from a
 * VSX instruction, we write `32+V_FOO` (= the VSR number of that VR).
 */

/*
 * TODO: layer merging, as in the aarch64 forward NTT. (No lazy reduction
 * on the forward side: barrett_fqmul_4x is the Montgomery product by
 * zeta, and the CT legs stay in int16 across all 7 layers. Lazy
 * reduction is an INTT concern -- see its TODO.)
 */

#define V_ZERO   3
#define V_NMKQ   5
#define V_Z0     7
#define V_Z1     8
#define V_Z2     9
#define V_Z3     10
#define V_ZETA   10
#define V_ZT0    0
#define V_ZT1    1
#define V_ZT2    6
#define V_ZT3    11
#define V_ZETATW 2

/*
 * The specific vector register numbers chosen for the symbols below are
 * arbitrary. Those in the callee-saved range v20-v31 are saved/restored
 * on entry/exit; the rest are caller-saved (v0-v19) and can be clobbered
 * freely.
 */
#define vdata_a1 12
#define vdata_a2 17
#define vdata_a3 22
#define vdata_a4 27
#define vdata_b1 13
#define vdata_b2 18
#define vdata_b3 23
#define vdata_b4 28

#define vresult_a1 15
#define vresult_b1 16
#define vresult_a2 20
#define vresult_b2 21
#define vresult_a3 25
#define vresult_b3 26
#define vresult_a4 30
#define vresult_b4 31

#define rinp      3
#define dup_rinp  5
#define qinp      4
#define len_2     7
#define zeta_inp     14
#define zeta_tw_inp  22
#define a1_offset 9
#define a2_offset 16
#define a3_offset 18
#define a4_offset 20
#define b1_offset 10
#define b2_offset 17
#define b3_offset 19
#define b4_offset 21

.text

/*
 * PowerPC ELF v2 ABI: r3 = int16_t *r, r4 = int16_t *qdata.
 *   caller-saved (volatile):     r0, r3-r12; v0-v19; f0-f13
 *   callee-saved (non-volatile): r14-r31; v20-v31; f14-f31
 *
 * SAVE_REGS allocates a 352-byte stack frame and spills the callee-saved
 * registers actually used by this function (r14-r22 and v20-v31). The
 * function is a leaf, so LR is held in r0 across the body rather than
 * spilled to memory.
 *
 * Frame layout (offsets relative to SP after `stdu 1, -352(1)`):
 *
 *     [   0,   8)  -- caller's SP (back chain, set atomically by stdu)
 *     [  56, 128)  -- r14..r22  (9 x 8 bytes)
 *     [ 128, 320)  -- v20..v31  (12 x 16 bytes)
 *
 * The remaining slots (8-55, 320-351) are unused.
 */
.macro SAVE_REGS
        stdu    1, -352(1)
        mflr    0
        std     14, 56(1)
        std     15, 64(1)
        std     16, 72(1)
        std     17, 80(1)
        std     18, 88(1)
        std     19, 96(1)
        std     20, 104(1)
        std     21, 112(1)
        std     22, 120(1)
        li      10, 128
        li      11, 144
        li      12, 160
        li      14, 176
        li      15, 192
        li      16, 208
        stxvx   32+20, 10, 1
        stxvx   32+21, 11, 1
        stxvx   32+22, 12, 1
        stxvx   32+23, 14, 1
        stxvx   32+24, 15, 1
        stxvx   32+25, 16, 1
        li      10, 224
        li      11, 240
        li      12, 256
        li      14, 272
        li      15, 288
        li      16, 304
        stxvx   32+26, 10, 1
        stxvx   32+27, 11, 1
        stxvx   32+28, 12, 1
        stxvx   32+29, 14, 1
        stxvx   32+30, 15, 1
        stxvx   32+31, 16, 1
.endm

.macro RESTORE_REGS
        li      10, 128
        li      11, 144
        li      12, 160
        li      14, 176
        li      15, 192
        li      16, 208
        lxvx    32+20, 10, 1
        lxvx    32+21, 11, 1
        lxvx    32+22, 12, 1
        lxvx    32+23, 14, 1
        lxvx    32+24, 15, 1
        lxvx    32+25, 16, 1
        li      10, 224
        li      11, 240
        li      12, 256
        li      14, 272
        li      15, 288
        li      16, 304
        lxvx    32+26, 10, 1
        lxvx    32+27, 11, 1
        lxvx    32+28, 12, 1
        lxvx    32+29, 14, 1
        lxvx    32+30, 15, 1
        lxvx    32+31, 16, 1
        ld      14, 56(1)
        ld      15, 64(1)
        ld      16, 72(1)
        ld      17, 80(1)
        ld      18, 88(1)
        ld      19, 96(1)
        ld      20, 104(1)
        ld      21, 112(1)
        ld      22, 120(1)

        mtlr    0
        addi    1, 1, 352
.endm

/*
 * Init_Coeffs_offset: compute the 8 byte offsets used by the load/store
 * macros for one CT_Butterfly_4x call.
 *
 * Args:
 *   start: byte offset of the first low coefficient (leg 1) within the
 *          polynomial buffer.
 *   next:  byte stride between successive butterfly groups.
 *
 * Reads:
 *   len_2 (r7): 2*len, the byte distance from a low coefficient to its
 *               paired high coefficient.
 *
 * Writes (all byte offsets relative to rinp):
 *   a1_offset = start                a*: low  legs (r[j])
 *   a2_offset = start + next
 *   a3_offset = start + 2*next
 *   a4_offset = start + 3*next
 *   b1_offset = start + len_2        b*: high legs (r[j+len])
 *   b2_offset = start + len_2 + next
 *   b3_offset = start + len_2 + 2*next
 *   b4_offset = start + len_2 + 3*next
 */
.macro Init_Coeffs_offset start, next
        li      a1_offset, \start               /* first offset to j */
        add     b1_offset, len_2, a1_offset     /* J + len*2 */
        addi    a2_offset, a1_offset, \next
        addi    b2_offset, b1_offset, \next
        addi    a3_offset, a2_offset, \next
        addi    b3_offset, b2_offset, \next
        addi    a4_offset, a3_offset, \next
        addi    b4_offset, b3_offset, \next
.endm

/*
 * Load_4_High: load the r[j+len] coefficient vectors (the "high" operands, which
 * are scaled by zeta in the CT butterfly) from b1_offset..b4_offset into
 * vdata_b1..vdata_b4.
 */
.macro Load_4_High
        lxvd2x  32+vdata_b1, rinp, b1_offset    /* vector r'0 */
        lxvd2x  32+vdata_b2, rinp, b2_offset    /* vector for r'1 */
        lxvd2x  32+vdata_b3, rinp, b3_offset    /* vector for r'2 */
        lxvd2x  32+vdata_b4, rinp, b4_offset    /* vector for r'3 */
.endm

/*
 * Load 2 - 2 - 2 - 2 layout
 *
 * Load Coefficients and setup vectors for 8 coefficients in the
 * following order,
 *    rj0, rj1, rjlen2, rjlen3, rj4, rj5, rjlen6, rjlen7
 *    rj8, rj9, rjlen10, rjlen11, rj12, rj13, rjlen14, rjlen15
 *  Each vmrgew and vmrgow will transpose vectors as,
 *  r[j]=      rj0, rj1, rj8, rj9, rj4, rj5, rj12, rj13
 *  r[j+len]=  rjlen2, rjlen3, rjlen10, rjlen11, rjlen6, rjlen7, rjlen14, rjlen15
 *
 *  r[j+len]: vdata_b1, vdata_b2, vdata_b3, vdata_b4
 *  r[j]: vdata_a1, vdata_a2, vdata_a3, vdata_a4
 *
 * In order to do the coefficients computation, zeta vector will arrange
 * in the proper order to match the multiplication.
 */
.macro LoadPermL24
        lxvd2x     32+25, 0, dup_rinp
        lxvd2x     32+26, 10, dup_rinp
        vmrgew vdata_b1, 25, 26
        vmrgow vdata_a1, 25, 26
        lxvd2x     32+25, 11, dup_rinp
        lxvd2x     32+26, 12, dup_rinp
        vmrgew vdata_b2, 25, 26
        vmrgow vdata_a2, 25, 26
        lxvd2x     32+25, 15, dup_rinp
        lxvd2x     32+26, 16, dup_rinp
        vmrgew vdata_b3, 25, 26
        vmrgow vdata_a3, 25, 26
        lxvd2x     32+25, 17, dup_rinp
        lxvd2x     32+26, 18, dup_rinp
        vmrgew vdata_b4, 25, 26
        vmrgow vdata_a4, 25, 26
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
.macro LoadPermL44
        lxvd2x     1, 0, dup_rinp
        lxvd2x     2, 10, dup_rinp
        xxpermdi 32+vdata_b1, 2, 1, 3
        xxpermdi 32+vdata_a1, 2, 1, 0
        lxvd2x     3, 11, dup_rinp
        lxvd2x     4, 12, dup_rinp
        xxpermdi 32+vdata_b2, 4, 3, 3
        xxpermdi 32+vdata_a2, 4, 3, 0
        lxvd2x     1, 15, dup_rinp
        lxvd2x     2, 16, dup_rinp
        xxpermdi 32+vdata_b3, 2, 1, 3
        xxpermdi 32+vdata_a3, 2, 1, 0
        lxvd2x     3, 17, dup_rinp
        lxvd2x     4, 18, dup_rinp
        xxpermdi 32+vdata_b4, 4, 3, 3
        xxpermdi 32+vdata_a4, 4, 3, 0
.endm

/*
 * Barrett multiplication (4 lanes), in-place over vdata_b_i.
 *   For each lane (b in vdata_b_i, z in _vz_i, zt in _vzt_i):
 *     t    = vmhraddshs(b, zt, 0)    = round(b*zt / 2^15)
 *     b_lo = vmladduhm(b, z, 0)      = (b*z) mod 2^16
 *     vdata_b_i = vmladduhm(t, -q, b_lo)  = b*z - t*q (mod 2^16)
 *
 *   Computes (b*z) mod MLKEM_Q in signed representation; the output
 *   is in the range (-MLKEM_Q, MLKEM_Q).
 *
 *   Note: this NTT variant overwrites the input vdata_b_i. The INTT
 *   variant in intt_ppc_asm.S takes explicit output operands (_vo*)
 *   because its callers need the GS subtraction input preserved.
 */
.macro barrett_fqmul_4x _vz0, _vz1, _vz2, _vz3, _vzt0, _vzt1, _vzt2, _vzt3
        vmhraddshs vresult_a1, vdata_b1, \_vzt0, V_ZERO
        vmhraddshs vresult_a2, vdata_b2, \_vzt1, V_ZERO
        vmhraddshs vresult_a3, vdata_b3, \_vzt2, V_ZERO
        vmhraddshs vresult_a4, vdata_b4, \_vzt3, V_ZERO

        vmladduhm vdata_b1, vdata_b1, \_vz0, V_ZERO
        vmladduhm vdata_b2, vdata_b2, \_vz1, V_ZERO
        vmladduhm vdata_b3, vdata_b3, \_vz2, V_ZERO
        vmladduhm vdata_b4, vdata_b4, \_vz3, V_ZERO

        vmladduhm vdata_b1, vresult_a1, V_NMKQ, vdata_b1
        vmladduhm vdata_b2, vresult_a2, V_NMKQ, vdata_b2
        vmladduhm vdata_b3, vresult_a3, V_NMKQ, vdata_b3
        vmladduhm vdata_b4, vresult_a4, V_NMKQ, vdata_b4
.endm

/*
 * Load_4_Low: load the r[j] coefficient vectors (the "low" operands, which are
 * not scaled by zeta in the CT butterfly) from a1_offset..a4_offset into
 * vdata_a1..vdata_a4.
 */
.macro Load_4_Low
        lxvd2x  32+vdata_a1, rinp, a1_offset     /* vector r0 */
        lxvd2x  32+vdata_a2, rinp, a2_offset    /* vector r1 */
        lxvd2x  32+vdata_a3, rinp, a3_offset    /* vector r2 */
        lxvd2x  32+vdata_a4, rinp, a4_offset    /* vector r3 */
.endm

/*
 * Cooley-Tukey add/sub (4 lanes). Combines the low input r[j] with the
 * Barrett-multiplied high input (leg2 * zeta) already left in vdata_b*:
 *
 *   vresult_a_i = vdata_a_i + vdata_b_i   (final r[j])
 *   vresult_b_i = vdata_a_i - vdata_b_i   (final r[j+len])
 *
 * Inputs:  vdata_a1..a4 (low coefficients r[j]),
 *          vdata_b1..b4 (high coefficients already multiplied by zeta).
 * Outputs: vresult_a1..a4 (low), vresult_b1..b4 (high).
 *
 * Counterpart in intt_ppc_asm.S has the same name but implements the
 * Gentleman-Sande add/sub (sum and difference of unmodified r[j], r[j+len]),
 * with vdata_b_i meaning the *unmodified* high input there.
 */
.macro AddSub_4x
        vsubuhm vresult_b1, vdata_a1, vdata_b1
        vadduhm vresult_a1, vdata_b1, vdata_a1
        vsubuhm vresult_b2, vdata_a2, vdata_b2
        vadduhm vresult_a2, vdata_b2, vdata_a2
        vsubuhm vresult_b3, vdata_a3, vdata_b3
        vadduhm vresult_a3, vdata_b3, vdata_a3
        vsubuhm vresult_b4, vdata_a4, vdata_b4
        vadduhm vresult_a4, vdata_b4, vdata_a4
.endm

.macro Write_8X
        stxvd2x 32+vresult_a1, rinp, a1_offset
        stxvd2x 32+vresult_b1, rinp, b1_offset
        stxvd2x 32+vresult_a2, rinp, a2_offset
        stxvd2x 32+vresult_b2, rinp, b2_offset
        stxvd2x 32+vresult_a3, rinp, a3_offset
        stxvd2x 32+vresult_b3, rinp, b3_offset
        stxvd2x 32+vresult_a4, rinp, a4_offset
        stxvd2x 32+vresult_b4, rinp, b4_offset
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the original
 * coefficient array order.
 */
.macro PermStoreL44
        xxpermdi 0, 32+vresult_a1, 32+vresult_b1, 3
        xxpermdi 1, 32+vresult_a1, 32+vresult_b1, 0
        xxpermdi 2, 32+vresult_a2, 32+vresult_b2, 3
        xxpermdi 3, 32+vresult_a2, 32+vresult_b2, 0
        xxpermdi 4, 32+vresult_a3, 32+vresult_b3, 3
        xxpermdi 5, 32+vresult_a3, 32+vresult_b3, 0
        xxpermdi 6, 32+vresult_a4, 32+vresult_b4, 3
        xxpermdi 7, 32+vresult_a4, 32+vresult_b4, 0
        stxvd2x 0, 0, dup_rinp
        stxvd2x 1, 10, dup_rinp
        stxvd2x 2, 11, dup_rinp
        stxvd2x 3, 12, dup_rinp
        stxvd2x 4, 15, dup_rinp
        stxvd2x 5, 16, dup_rinp
        stxvd2x 6, 17, dup_rinp
        stxvd2x 7, 18, dup_rinp
.endm

/*
 * Transpose the final coefficients of 2-2-2-2 layout to the original
 * coefficient array order.
 */
.macro PermStoreL24
        vmrgew 10, vresult_b1, vresult_a1
        vmrgow 11, vresult_b1, vresult_a1
        vmrgew 12, vresult_b2, vresult_a2
        vmrgow 13, vresult_b2, vresult_a2
        vmrgew 14, vresult_b3, vresult_a3
        vmrgow 15, vresult_b3, vresult_a3
        vmrgew 16, vresult_b4, vresult_a4
        vmrgow 17, vresult_b4, vresult_a4
        stxvd2x 32+10, 0, dup_rinp
        stxvd2x 32+11, 10, dup_rinp
        stxvd2x 32+12, 11, dup_rinp
        stxvd2x 32+13, 12, dup_rinp
        stxvd2x 32+14, 15, dup_rinp
        stxvd2x 32+15, 16, dup_rinp
        stxvd2x 32+16, 17, dup_rinp
        stxvd2x 32+17, 18, dup_rinp
.endm

.macro Load_next_4zetas
        li      10, 16
        li      11, 32
        li      12, 48
        lxvd2x  32+V_Z0, 0, zeta_inp
        lxvd2x  32+V_Z1, 10, zeta_inp
        lxvd2x  32+V_Z2, 11, zeta_inp
        lxvd2x  32+V_Z3, 12, zeta_inp
        lxvd2x  32+V_ZT0, 0, zeta_tw_inp
        lxvd2x  32+V_ZT1, 10, zeta_tw_inp
        lxvd2x  32+V_ZT2, 11, zeta_tw_inp
        lxvd2x  32+V_ZT3, 12, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 64
        addi    zeta_tw_inp, zeta_tw_inp, 64
.endm

/*
 * Cooley-Tukey 4-batched butterfly, len=2 (2-2-2-2 layout).
 * Used by layer 7 of the forward NTT.
 */
.macro CT_Butterfly_4x_len2
        Load_next_4zetas
        LoadPermL24
        barrett_fqmul_4x V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        AddSub_4x
        PermStoreL24
        addi    dup_rinp, dup_rinp, 128
.endm

/*
 * Cooley-Tukey 4-batched butterfly, len=4 (4-4 layout).
 * Used by layer 6 of the forward NTT.
 */
.macro CT_Butterfly_4x_len4
        Load_next_4zetas
        LoadPermL44
        barrett_fqmul_4x V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        AddSub_4x
        PermStoreL44
        addi    dup_rinp, dup_rinp, 128
.endm

/*
 * A group of 4 CT butterflies, used by NTT layers 1, 2, 3, 4, 5.
 */
.macro CT_Butterfly_4x start, next, _vz0, _vz1, _vz2, _vz3, _vzt0, _vzt1, _vzt2, _vzt3
        Init_Coeffs_offset \start, \next
        Load_4_High
        barrett_fqmul_4x \_vz0, \_vz1, \_vz2, \_vz3, \_vzt0, \_vzt1, \_vzt2, \_vzt3
        Load_4_Low
        AddSub_4x
        Write_8X
.endm

/*
 * mlk_ntt_ppc_asm(int16_t *r, int16_t *qdata)
 *   Compute the 7-layer forward NTT in place. Each layer is a Cooley-Tukey
 *   butterfly stage with stride `len` (the index distance between paired
 *   coefficients). Layers 1..7 use len = 128, 64, 32, 16, 8, 4, 2.
 *
 *   Each layer pairs a low coefficient r[j] (leg 1) with a high coefficient
 *   r[j+len] (leg 2). Offsets below are byte offsets into r; as each coefficient
 *   is an int16_t (2 bytes), an index distance len is a byte distance len*2, so
 *   leg 2 sits at byte offset start + len*2.
 *
 *   leg 1 (low, r[j])            leg 2 (high, r[j+len])
 *   -----                        -----
 *   start                        start+len*2
 *   start+next                   start+len*2+next
 *   start+next+next              start+len*2+next+next
 *   start+next+next+next         start+len*2+next+next+next
 *
 *   Each computation loads 8 vectors, 4 for each leg, and applies the
 *   Cooley-Tukey butterfly in place:
 *
 *      t        = leg2 * zeta   (mod MLKEM_Q, via Barrett multiplication)
 *      leg1_new = leg1 + t
 *      leg2_new = leg1 - t
 *
 *   Layers 1-5 have len >= 8, so each loaded 8-lane vector lies entirely
 *   within one leg and pairs with a single zeta replicated across all 8 lanes.
 *
 *   Layers 6 (len=4) and 7 (len=2) have stride smaller than the vector width,
 *   so each loaded vector straddles both legs in memory:
 *
 *     len=4, "4-4 layout":     vector = [ leg1 x 4, leg2 x 4 ]
 *                              -> 1 butterfly group per vector,
 *                                 1 distinct zeta replicated 4-wise
 *
 *     len=2, "2-2-2-2 layout": vector = [ leg1 x 2, leg2 x 2,
 *                                         leg1 x 2, leg2 x 2 ]
 *                              -> 2 butterfly groups per vector,
 *                                 2 distinct zetas, each replicated 2-wise
 *
 *   For these layers, each loaded vector is permuted into separate leg1/leg2
 *   vectors before the butterfly, and the result is permuted back to the
 *   original in-memory order on store. The zeta vectors are pre-arranged in
 *   the constant table to match the permuted lane order, e.g. for len=2:
 *
 *         leg1 / leg2 vector    a1   a2   a3   a4   a5   a6   a7   a8
 *         zeta vector           z1   z1   z2   z2   z3   z3   z4   z4
 */
.global MLK_ASM_NAMESPACE(ntt_ppc_asm)
.balign 16
MLK_ASM_FN_SYMBOL(ntt_ppc_asm)

        SAVE_REGS

        /* load -MLKEM_Q */
        lvx     V_NMKQ,0,qinp

        /* zeta_inp: regular Barrett roots; zeta_tw_inp: twisted roots */
        addi    zeta_inp, qinp, MLK_PPC_ZETA_NTT_OFFSET
        addi    zeta_tw_inp, qinp, MLK_PPC_ZETA_NTT_TW_OFFSET

        vxor    V_ZERO, V_ZERO, V_ZERO

.balign 16
        /*
         * Layer 1. len = 128, start = 0, 64, 128, 192
         *
         * For all NTT layers below: `start` and `next` are byte offsets
         * into the polynomial buffer (CT_Butterfly_4x's first two args).
         * Coefficients are int16, so an index distance of L corresponds
         * to a byte distance of 2*L.
         */
        li      len_2, 256          /* len * 2 */
        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16

        CT_Butterfly_4x 0, 16,   V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        CT_Butterfly_4x 64, 16,  V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        CT_Butterfly_4x 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        CT_Butterfly_4x 192, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

.balign 16
        /*
         * Layer 2. len = 64, start= 0, 64, 256, 320
         */
        li      len_2, 128
        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        CT_Butterfly_4x 0, 16,  V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        CT_Butterfly_4x 64, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        CT_Butterfly_4x 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW
        CT_Butterfly_4x 320, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

.balign 16
        /*
         * Layer 3. len = 32, start = 0, 128, 256, 384
         */
        li      len_2, 64
        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        CT_Butterfly_4x 0, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        CT_Butterfly_4x 128, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        CT_Butterfly_4x 256, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        CT_Butterfly_4x 384, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW

.balign 16
        /*
         * Layer 4. len = 16, start = 0, 16, 256, 272
         */
        li      len_2, 32
        Load_next_4zetas
        CT_Butterfly_4x 0, 64,  V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        CT_Butterfly_4x 16, 64, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        CT_Butterfly_4x 256, 64, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3
        CT_Butterfly_4x 272, 64, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

.balign 16
        /*
         * Layer 5. len = 8, start= 0, 128, 256, 384
         */
        li      len_2, 16
        Load_next_4zetas
        CT_Butterfly_4x 0, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        CT_Butterfly_4x 128, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        CT_Butterfly_4x 256, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        Load_next_4zetas
        CT_Butterfly_4x 384, 32, V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3

        /*
         * Layer 6. len = 4,
         *     leg1 offset - 0, 32, 64, 96
         *     leg2 offset - 16, 48, 80, 112
         *
         *    Load zeta vectors in 4-4 layout
         */
        mr      dup_rinp, rinp                 /* Let r5 points to coefficient array */
        li      len_2, 8

        /* Raw coefficient byte-offsets for the 4-4 / 2-2-2-2 loads,
         * held in scratch regs r10-r12 and r15-r18. r10/r16/r17/r18 happen to
         * alias b1/a2/b2/a3_offset, but those layer-1-5 roles do not apply
         * here - the values are unrelated. */
        li      10, 16
        li      11, 32
        li      12, 48
        li      15, 64
        li      16, 80
        li      17, 96
        li      18, 112

.balign 16
        CT_Butterfly_4x_len4
        CT_Butterfly_4x_len4
        CT_Butterfly_4x_len4
        CT_Butterfly_4x_len4

        /*
         * Layer 7. len = 2
         *     leg1 offset - 0, 32, 64, 96
         *     leg2 offset - 16, 48, 80, 112
         *
         *    Load zeta vectors in 2-2-2-2 layout
         */
        mr      dup_rinp, rinp                  /* Let r5 points to coefficient array */
        li      len_2, 4

.balign 16
        CT_Butterfly_4x_len2
        CT_Butterfly_4x_len2
        CT_Butterfly_4x_len2
        CT_Butterfly_4x_len2

        RESTORE_REGS
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V_ZERO
#undef V_NMKQ
#undef V_Z0
#undef V_Z1
#undef V_Z2
#undef V_Z3
#undef V_ZETA
#undef V_ZT0
#undef V_ZT1
#undef V_ZT2
#undef V_ZT3
#undef V_ZETATW
#undef vdata_a1
#undef vdata_a2
#undef vdata_a3
#undef vdata_a4
#undef vdata_b1
#undef vdata_b2
#undef vdata_b3
#undef vdata_b4
#undef vresult_a1
#undef vresult_b1
#undef vresult_a2
#undef vresult_b2
#undef vresult_a3
#undef vresult_b3
#undef vresult_a4
#undef vresult_b4
#undef rinp
#undef dup_rinp
#undef qinp
#undef len_2
#undef zeta_inp
#undef zeta_tw_inp
#undef a1_offset
#undef a2_offset
#undef a3_offset
#undef a4_offset
#undef b1_offset
#undef b2_offset
#undef b3_offset
#undef b4_offset

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */
