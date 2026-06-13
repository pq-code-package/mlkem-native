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
  Name: intt_ppc_asm
  Description: PowerPC64 VSX inverse NTT
  Signature: void mlk_intt_ppc_asm(int16_t *r, const int16_t *qdata)
  ABI:
    Architecture: powerpc64le
    CallingConvention: ELFv2
    Features: [VSX]
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
 *
 * Several Barrett-Q-reduce constants (-Q, +Q, zero, 2^25, 26) are
 * precomputed at function entry and parked in the FPR-anchored VSRs
 * vs0/3/6/7/8 -- free 128-bit scratch slots, since this routine does
 * no scalar-FP work. They are reloaded into VRs via xxlor as needed.
 */

/*
 * TODO: lazy reduction and layer merging, as in the aarch64 inverse NTT.
 */

/* Barrett-Q-reduce constants */
#define V20159  0
#define V_25    1
#define V_26    2
#define V_MKQ   3

/* Shared zero vector (aliases V_MKQ; V_MKQ is only live during
 * barrett_reduce_4x, where V_ZERO/zero is reloaded from vs3 anyway). */
#define V_ZERO  3

/* Barrett-multiply constants */
#define V_NMKQ  5
#define V_Z0    7
#define V_Z1    8
#define V_Z2    9
#define V_Z3    10
#define V_ZETA  10
#define V_NINV    10
#define V_NINV_TW 11

/* Barrett twisted zetas: zt = round_to_even(z * 2^16 / q) / 2.
 * Placed in vdata_b slots (free by the time Load_next_4zetas runs) to
 * avoid the V20159/V_25/V_26/V_MKQ/V_Z0..3 constants required by the
 * next Barrett-Q-reduce. V_ZETATW aliases V_ZT0 (broadcast layer 5-7). */
#define V_ZT0     12
#define V_ZT1     20
#define V_ZT2     6
#define V_ZT3     11
#define V_ZETATW  12

#define vdata_a1 21
#define vdata_a2 22
#define vdata_a3 23
#define vdata_a4 24
#define vdata_b1 8
#define vdata_b2 12
#define vdata_b3 16
#define vdata_b4 20

#define vdata_brt1 8
#define vdata_brt2 12
#define vdata_brt3 16
#define vdata_brt4 20

#define vdata_t1 25
#define vdata_t2 26
#define vdata_t3 30
#define vdata_t4 31

#define vresult_brt1 4
#define vresult_brt2 9
#define vresult_brt3 13
#define vresult_brt4 17
#define vresult_t1 13
#define vresult_t2 18
#define vresult_t3 23
#define vresult_t4 28

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

/* VSR slot indices for the long-term constant stash documented in the
 * file-header comment. Used as the literal VSR operand in xxlor (low
 * half of vsX, alias fX, dead in this routine). */
#define VS_NMKQ_STASH   0
#define VS_ZERO_STASH   3
#define VS_MKQ_STASH    6
#define VS_25_STASH     7
#define VS_26_STASH     8

.text

/*
 * PowerPC ELF v2 ABI: r3 = int16_t *r, r4 = int16_t *qdata.
 *   callee-saved registers: r14-r31; v20-v31
 * The callee-saved registers used here (r14-r22, v20-v31) are saved/restored.
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
 * Compute r[j]+r[j+len] and r[j+len]-r[j] (Gentleman-Sande)
 *  r[j]+r[j+len]: vdata_brt1, vdata_brt2, vdata_brt3, vdata_brt4
 *  r[j+len]-r[j]: vdata_t1, vdata_t2, vdata_t3, vdata_t4
 */
.macro AddSub_4x
        vsubuhm vdata_t1, vdata_b1, vdata_a1
        vsubuhm vdata_t2, vdata_b2, vdata_a2
        vsubuhm vdata_t3, vdata_b3, vdata_a3
        vsubuhm vdata_t4, vdata_b4, vdata_a4
        vadduhm vdata_brt1, vdata_b1, vdata_a1
        vadduhm vdata_brt2, vdata_b2, vdata_a2
        vadduhm vdata_brt3, vdata_b3, vdata_a3
        vadduhm vdata_brt4, vdata_b4, vdata_a4
.endm

/*
 * Init_Coeffs_offset: compute the 8 byte offsets used by the load/store
 * macros for one GS_Butterfly_4x call.
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
 * Load both coefficient vectors of each butterfly:
 *   r[j+len] (r') from offsets b1_offset..b4_offset into vdata_b1..vdata_b4
 *   r[j]     (r)  from offsets a1_offset..a4_offset into vdata_a1..vdata_a4
 */
.macro Load_4Both
        lxvd2x  32+vdata_b1, rinp, b1_offset    /* vector r'0 */
        lxvd2x  32+vdata_b2, rinp, b2_offset    /* vector for r'1 */
        lxvd2x  32+vdata_b3, rinp, b3_offset    /* vector for r'2 */
        lxvd2x  32+vdata_b4, rinp, b4_offset    /* vector for r'3 */

        lxvd2x  32+vdata_a1, rinp, a1_offset    /* vector r0 */
        lxvd2x  32+vdata_a2, rinp, a2_offset    /* vector r1 */
        lxvd2x  32+vdata_a3, rinp, a3_offset    /* vector r2 */
        lxvd2x  32+vdata_a4, rinp, a4_offset    /* vector r3 */
.endm

/*
 * Set up the offsets, load r[j] and r[j+len], and form the GS sum/difference
 * (vdata_brt* = r[j]+r[j+len], vdata_t* = r[j+len]-r[j]).
 */
.macro Load_4Coeffs start, next
        Init_Coeffs_offset \start, \next
        Load_4Both
        AddSub_4x
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
 * In order to do the coefficient computation, zeta vector will arrange
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
        lxvd2x     10, 0, dup_rinp
        lxvd2x     11, 10, dup_rinp
        xxpermdi 32+vdata_b1, 11, 10, 3
        xxpermdi 32+vdata_a1, 11, 10, 0
        lxvd2x     10, 11, dup_rinp
        lxvd2x     11, 12, dup_rinp
        xxpermdi 32+vdata_b2, 11, 10, 3
        xxpermdi 32+vdata_a2, 11, 10, 0
        lxvd2x     10, 15, dup_rinp
        lxvd2x     11, 16, dup_rinp
        xxpermdi 32+vdata_b3, 11, 10, 3
        xxpermdi 32+vdata_a3, 11, 10, 0
        lxvd2x     10, 17, dup_rinp
        lxvd2x     11, 18, dup_rinp
        xxpermdi 32+vdata_b4, 11, 10, 3
        xxpermdi 32+vdata_a4, 11, 10, 0
.endm

.macro barrett_reduce_4x _v0, _v1, _v2, _v3
        /* Materialize VR copies of V_MKQ (v3), V_25 (v1), V_26 (v2)
           from their long-term VSR stash slots. The caller does not
           keep these VR-resident between barrett_reduce_4x calls.
           Also zero v7 (scratch). */
        vxor    7, 7, 7
        xxlor   32+V_MKQ,   VS_MKQ_STASH,   VS_MKQ_STASH
        xxlor   32+V_25,    VS_25_STASH,    VS_25_STASH
        xxlor   32+V_26,    VS_26_STASH,    VS_26_STASH
        /* Multiply Odd/Even signed halfword;
           Results word bound by 2^32 in abs value. */
        vmulosh 6, vdata_brt1, V20159
        vmulesh 5, vdata_brt1, V20159
        vmulosh 11, vdata_brt2, V20159
        vmulesh 10, vdata_brt2, V20159
        vmulosh 15, vdata_brt3, V20159
        vmulesh 14, vdata_brt3, V20159
        vmulosh 19, vdata_brt4, V20159
        vmulesh 18, vdata_brt4, V20159
        xxmrglw 32+4, 32+5, 32+6
        xxmrghw 32+5, 32+5, 32+6
        xxmrglw 32+9, 32+10, 32+11
        xxmrghw 32+10, 32+10, 32+11
        xxmrglw 32+13, 32+14, 32+15
        xxmrghw 32+14, 32+14, 32+15
        xxmrglw 32+17, 32+18, 32+19
        xxmrghw 32+18, 32+18, 32+19
        vadduwm 4, 4, V_25
        vadduwm 5, 5, V_25
        vadduwm 9, 9, V_25
        vadduwm 10, 10, V_25
        vadduwm 13, 13, V_25
        vadduwm 14, 14, V_25
        vadduwm 17, 17, V_25
        vadduwm 18, 18, V_25
        /* Right shift and pack lower halfword,
           results bound by 2^16 in abs value */
        vsraw   4, 4, V_26
        vsraw   5, 5, V_26
        vsraw   9, 9, V_26
        vsraw   10, 10, V_26
        vsraw   13, 13, V_26
        vsraw   14, 14, V_26
        vsraw   17, 17, V_26
        vsraw   18, 18, V_26
        vpkuwum 4, 5, 4
        vsubuhm 4, 7, 4
        vpkuwum 9, 10, 9
        vsubuhm 9, 7, 9
        vpkuwum 13, 14, 13
        vsubuhm 13, 7, 13
        vpkuwum 17, 18, 17
        vsubuhm 17, 7, 17
        /* Modulo multiply-Low unsigned halfword;
           results bound by 2^16 * q in abs value. */
        vmladduhm \_v0, 4, V_MKQ, 8
        vmladduhm \_v1, 9, V_MKQ, 12
        vmladduhm \_v2, 13, V_MKQ, 16
        vmladduhm \_v3, 17, V_MKQ, 20
.endm

/*
 * Barrett multiplication (4 lanes), with explicit output operands _vo*.
 *   For each lane (b in vdata_t_i, z in _vz_i, zt in _vzt_i):
 *     t    = vmhraddshs(b, zt, 0)    = round(b*zt / 2^15)
 *     b_lo = vmladduhm(b, z, 0)      = (b*z) mod 2^16
 *     _vo  = vmladduhm(t, -q, b_lo)  = b*z - t*q (mod 2^16)
 *
 *   Computes (b*z) mod MLKEM_Q in signed representation; the output is
 *   in the range (-MLKEM_Q, MLKEM_Q). V_ZERO is the zero vector set at
 *   function entry.
 *
 *   Note: this INTT variant writes to explicit output operands and does
 *   not overwrite vdata_t_i. The NTT variant in ntt_ppc_asm.S is in-place
 *   over its vdata_b_i input.
 */
.macro barrett_fqmul_4x _vz0, _vz1, _vz2, _vz3, _vzt0, _vzt1, _vzt2, _vzt3, _vo0, _vo1, _vo2, _vo3
        vmhraddshs 14, vdata_t1, \_vzt0, V_ZERO
        vmhraddshs 19, vdata_t2, \_vzt1, V_ZERO
        vmhraddshs 24, vdata_t3, \_vzt2, V_ZERO
        vmhraddshs 29, vdata_t4, \_vzt3, V_ZERO

        vmladduhm \_vo0, vdata_t1, \_vz0, V_ZERO
        vmladduhm \_vo1, vdata_t2, \_vz1, V_ZERO
        vmladduhm \_vo2, vdata_t3, \_vz2, V_ZERO
        vmladduhm \_vo3, vdata_t4, \_vz3, V_ZERO

        vmladduhm \_vo0, 14, V_NMKQ, \_vo0
        vmladduhm \_vo1, 19, V_NMKQ, \_vo1
        vmladduhm \_vo2, 24, V_NMKQ, \_vo2
        vmladduhm \_vo3, 29, V_NMKQ, \_vo3
.endm

.macro Load_next_4zetas
        li      8, 16
        li      11, 32
        li      12, 48
        lxvd2x    32+V_Z0, 0, zeta_inp
        lxvd2x    32+V_Z1, 8, zeta_inp
        lxvd2x    32+V_Z2, 11, zeta_inp
        lxvd2x    32+V_Z3, 12, zeta_inp
        lxvd2x    32+V_ZT0, 0, zeta_tw_inp
        lxvd2x    32+V_ZT1, 8, zeta_tw_inp
        lxvd2x    32+V_ZT2, 11, zeta_tw_inp
        lxvd2x    32+V_ZT3, 12, zeta_tw_inp
        addi    zeta_inp, zeta_inp, 64
        addi    zeta_tw_inp, zeta_tw_inp, 64
.endm

.macro Write_4_Low _vs0, _vs1, _vs2, _vs3
        stxvd2x \_vs0, rinp, a1_offset
        stxvd2x \_vs1, rinp, a2_offset
        stxvd2x \_vs2, rinp, a3_offset
        stxvd2x \_vs3, rinp, a4_offset
.endm

.macro Write_4_High _vs0, _vs1, _vs2, _vs3
        stxvd2x \_vs0, rinp, b1_offset
        stxvd2x \_vs1, rinp, b2_offset
        stxvd2x \_vs2, rinp, b3_offset
        stxvd2x \_vs3, rinp, b4_offset
.endm

.macro Reload_4coeffs
        lxvd2x  32+vdata_t1, 0, rinp
        lxvd2x  32+vdata_t2, 10, rinp
        lxvd2x  32+vdata_t3, 11, rinp
        lxvd2x  32+vdata_t4, 12, rinp
        addi    rinp, rinp, 64
.endm

.macro MWrite_8X _vs0, _vs1, _vs2, _vs3, _vs4, _vs5, _vs6, _vs7
        addi    rinp, rinp, -128
        stxvd2x \_vs0, 0, rinp
        stxvd2x \_vs1, 10, rinp
        stxvd2x \_vs2, 11, rinp
        stxvd2x \_vs3, 12, rinp
        stxvd2x \_vs4, 15, rinp
        stxvd2x \_vs5, 16, rinp
        stxvd2x \_vs6, 17, rinp
        stxvd2x \_vs7, 18, rinp
        addi    rinp, rinp, 128
.endm

/*
 * Transpose the final coefficients of 4-4 layout to the original
 * coefficient array order.
 */
.macro PermStoreL44
        xxpermdi 32+10, 32+14, 32+vresult_t1, 3
        xxpermdi 32+11, 32+14, 32+vresult_t1, 0
        xxpermdi 32+12, 32+19, 32+vresult_t2, 3
        xxpermdi 32+13, 32+19, 32+vresult_t2, 0
        xxpermdi 32+14, 32+24, 32+vresult_t3, 3
        xxpermdi 32+15, 32+24, 32+vresult_t3, 0
        xxpermdi 32+16, 32+29, 32+vresult_t4, 3
        xxpermdi 32+17, 32+29, 32+vresult_t4, 0
        stxvd2x    32+10, 0, dup_rinp
        stxvd2x    32+11, 10, dup_rinp
        stxvd2x    32+12, 11, dup_rinp
        stxvd2x    32+13, 12, dup_rinp
        stxvd2x    32+14, 15, dup_rinp
        stxvd2x    32+15, 16, dup_rinp
        stxvd2x    32+16, 17, dup_rinp
        stxvd2x    32+17, 18, dup_rinp
.endm

/*
 * Transpose the final coefficients of 2-2-2-2 layout to the original
 * coefficient array order.
 */
.macro PermStoreL24
        vmrgew 10, vresult_t1, 14
        vmrgow 11, vresult_t1, 14
        vmrgew 12, vresult_t2, 19
        vmrgow 13, vresult_t2, 19
        vmrgew 14, vresult_t3, 24
        vmrgow 15, vresult_t3, 24
        vmrgew 16, vresult_t4, 29
        vmrgow 17, vresult_t4, 29
        stxvd2x    32+10, 0, dup_rinp
        stxvd2x    32+11, 10, dup_rinp
        stxvd2x    32+12, 11, dup_rinp
        stxvd2x    32+13, 12, dup_rinp
        stxvd2x    32+14, 15, dup_rinp
        stxvd2x    32+15, 16, dup_rinp
        stxvd2x    32+16, 17, dup_rinp
        stxvd2x    32+17, 18, dup_rinp
.endm

/*
 * Park vresult_brt1..brt4 (the GS sums = future leg1 values, output of
 * barrett_reduce_4x) in the FPR-anchored VSR scratch slots vs10..vs13,
 * before the upcoming Load_next_4zetas + barrett_fqmul_4x sequence
 * clobbers them. Specifically vresult_brt3 = v13 collides with
 * vresult_t1 = v13 written by barrett_fqmul_4x.
 *
 * Pairs with RecoverLow (called from the wrapper after barrett_fqmul_4x).
 *
 * Future work: this save/recover pair only exists because of the v13
 * collision in the chosen register allocation. A future re-allocation
 * that picks non-overlapping VRs for vresult_brt* and vresult_t* could
 * eliminate both helpers.
 */
.macro SaveLow
        xxlor   10, 32+vresult_brt1, 32+vresult_brt1
        xxlor   11, 32+vresult_brt2, 32+vresult_brt2
        xxlor   12, 32+vresult_brt3, 32+vresult_brt3
        xxlor   13, 32+vresult_brt4, 32+vresult_brt4
.endm

/*
 * Pull the parked low/sum results back from vs10..vs13 into VRs 14, 19,
 * 24, 29 (chosen so they don't collide with vresult_t1..t4 = v13, v18,
 * v23, v28 left by barrett_fqmul_4x). These are the brt operands that
 * PermStoreL{44,24} interleaves with the multiplied-diff vectors.
 */
.macro RecoverLow
        xxlor   32+14, 10, 10
        xxlor   32+19, 11, 11
        xxlor   32+24, 12, 12
        xxlor   32+29, 13, 13
.endm

/*
 * Restore the VR copies of long-term constants V_NMKQ (v5) and V_ZERO
 * (v3) from their VSR stashes (vs0 and vs3). barrett_reduce_4x clobbers
 * v5 (used as a multiply-even scratch destination) and v3 (used to hold
 * V_MKQ for its own body, since V_MKQ and V_ZERO share v3).
 */
.macro RestoreGlobals
        xxlor   32+V_NMKQ, VS_NMKQ_STASH, VS_NMKQ_STASH
        xxlor   32+V_ZERO, VS_ZERO_STASH, VS_ZERO_STASH
.endm

/*
 * Gentleman-Sande 4-batched butterfly, len=2 (2-2-2-2 layout).
 * Used by layer 1 of the inverse NTT.
 */
.macro GS_Butterfly_4x_len2
        LoadPermL24
        AddSub_4x
        barrett_reduce_4x vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        SaveLow
        RestoreGlobals
        Load_next_4zetas
        barrett_fqmul_4x V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3, vresult_t1, vresult_t2, vresult_t3, vresult_t4
        RecoverLow
        PermStoreL24
.endm

/*
 * Gentleman-Sande 4-batched butterfly, len=4 (4-4 layout).
 * Used by layer 2 of the inverse NTT.
 */
.macro GS_Butterfly_4x_len4
        LoadPermL44
        AddSub_4x
        barrett_reduce_4x vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        SaveLow
        RestoreGlobals
        Load_next_4zetas
        barrett_fqmul_4x V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3, vresult_t1, vresult_t2, vresult_t3, vresult_t4
        RecoverLow
        PermStoreL44
.endm

/*
 * Gentleman-Sande 4-batched butterfly with 4 packed zetas per call.
 * Used by layers 3 and 4 of the inverse NTT (len=8 and 16).
 */
.macro GS_Butterfly_4x start, next
        Load_4Coeffs \start, \next
        barrett_reduce_4x vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        Write_4_Low 32+vresult_brt1, 32+vresult_brt2, 32+vresult_brt3, 32+vresult_brt4
        RestoreGlobals
        Load_next_4zetas
        barrett_fqmul_4x V_Z0, V_Z1, V_Z2, V_Z3, V_ZT0, V_ZT1, V_ZT2, V_ZT3, vresult_t1, vresult_t2, vresult_t3, vresult_t4
        Write_4_High 32+vresult_t1, 32+vresult_t2, 32+vresult_t3, 32+vresult_t4
.endm

/*
 * Gentleman-Sande 4-batched butterfly with a single zeta broadcast
 * across all 4 lanes. Used by layers 5, 6 and 7 of the inverse NTT
 * (len=32, 64 and 128).
 */
.macro GS_Butterfly_Broadcast_4x start, next
        Load_4Coeffs \start, \next
        barrett_reduce_4x vresult_brt1, vresult_brt2, vresult_brt3, vresult_brt4
        Write_4_Low 32+vresult_brt1, 32+vresult_brt2, 32+vresult_brt3, 32+vresult_brt4
        RestoreGlobals
        lvx     V_ZETA, 0, zeta_inp
        lvx     V_ZETATW, 0, zeta_tw_inp
        barrett_fqmul_4x V_ZETA, V_ZETA, V_ZETA, V_ZETA, V_ZETATW, V_ZETATW, V_ZETATW, V_ZETATW, vresult_t1, vresult_t2, vresult_t3, vresult_t4
        Write_4_High 32+vresult_t1, 32+vresult_t2, 32+vresult_t3, 32+vresult_t4
.endm

/*
 * mlk_intt_ppc_asm(int16_t *r, int16_t *qdata)
 *   Compute the 7-layer inverse NTT in place. Each layer is a Gentleman-Sande
 *   butterfly stage with stride `len` (the index distance between paired
 *   coefficients). Layers 1..7 use len = 2, 4, 8, 16, 32, 64, 128 -- the
 *   reverse of the forward NTT layer ordering.
 *
 *   Before the layered butterflies, every coefficient is first scaled by
 *   N^-1 (in Montgomery form) via Barrett multiplication.
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
 *   Gentleman-Sande butterfly in place:
 *
 *      leg1_new = (leg1 + leg2)         (then Barrett-reduced into (-MLKEM_Q, MLKEM_Q))
 *      leg2_new = (leg2 - leg1) * zeta  (mod MLKEM_Q, via Barrett multiplication)
 *
 *   Layers 3-7 have len >= 8, so each loaded 8-lane vector lies entirely
 *   within one leg and pairs with a single zeta replicated across all 8 lanes.
 *
 *   Layers 1 (len=2) and 2 (len=4) have stride smaller than the vector width,
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
.global MLK_ASM_NAMESPACE(intt_ppc_asm)
.balign 16
MLK_ASM_FN_SYMBOL(intt_ppc_asm)

        SAVE_REGS

        /* init vectors and constants */
        lxvx    VS_NMKQ_STASH, 0, qinp                  /* -Q */

        xxlxor  32+V_ZERO, 32+V_ZERO, 32+V_ZERO
        xxlor   VS_ZERO_STASH, 32+V_ZERO, 32+V_ZERO

        /*  Setup for Barrett reduce */
        li      10, MLK_PPC_Q_OFFSET
        li      11, MLK_PPC_C20159_OFFSET
        lxvx    VS_MKQ_STASH, 10, qinp                  /* V_MKQ */
        lxvx    32+V20159, 11, qinp                     /* V20159 */

        vspltisw 8, 13
        vadduwm  8, 8, 8
        xxlor   VS_26_STASH, 32+8, 32+8

        vspltisw 9, 1
        vsubuwm 10, 8, 9                                /* value 25 */
        vslw    9, 9, 10
        xxlor   VS_25_STASH, 32+9, 32+9

        li      10, 16
        li      11, 32
        li      12, 48
        li      15, 64
        li      16, 80
        li      17, 96
        li      18, 112

        /*
         * Scale every coefficient by N^-1 via Barrett multiplication.
         */
        addi    zeta_inp, qinp, MLK_PPC_N_INV_OFFSET
        lvx     V_NINV, 0, zeta_inp
        addi    zeta_inp, qinp, MLK_PPC_N_INV_TW_OFFSET
        lvx     V_NINV_TW, 0, zeta_inp
        li      8, 4
        mtctr   8

        xxlor   32+V_NMKQ, VS_NMKQ_STASH, VS_NMKQ_STASH      /* V_NMKQ = -Q */
intt_ppc_asm_Loopf:
        Reload_4coeffs
        barrett_fqmul_4x V_NINV, V_NINV, V_NINV, V_NINV, V_NINV_TW, V_NINV_TW, V_NINV_TW, V_NINV_TW, 6, 7, 8, 9
        Reload_4coeffs
        barrett_fqmul_4x V_NINV, V_NINV, V_NINV, V_NINV, V_NINV_TW, V_NINV_TW, V_NINV_TW, V_NINV_TW, 13, 18, 23, 28
        MWrite_8X 32+6, 32+7, 32+8, 32+9, 32+13, 32+18, 32+23, 32+28
        bdnz    intt_ppc_asm_Loopf

        addi    rinp, rinp, -512

.balign 16
        /*
         * Layer 1. len = 2
         *     leg1 offset - 0, 32, 64, 96
         *     leg2 offset - 16, 48, 80, 112
         *
         *    Update zetas vectors, each vector has 2 zetas
         *    Load zeta vectors in 2-2-2-2 layout
         *
         * For all INTT layers below: `start` and `next` are byte offsets
         * into the polynomial buffer (the GS_Butterfly_*'s first two args).
         * Coefficients are int16, so an index distance of L corresponds
         * to a byte distance of 2*L.
         */
        addi    zeta_inp, qinp, MLK_PPC_ZETA_INTT_OFFSET
        addi    zeta_tw_inp, qinp, MLK_PPC_ZETA_INTT_TW_OFFSET
        li      len_2, 4        /* len * 2 */
        mr      dup_rinp, rinp

        GS_Butterfly_4x_len2
        addi    dup_rinp, dup_rinp, 128
        GS_Butterfly_4x_len2
        addi    dup_rinp, dup_rinp, 128
        GS_Butterfly_4x_len2
        addi    dup_rinp, dup_rinp, 128
        GS_Butterfly_4x_len2
        addi    dup_rinp, dup_rinp, 128

.balign 16
        /*
         * Layer 2. len = 4
         *     leg1 offset - 0, 32, 64, 96
         *     leg2 offset - 16, 48, 80, 112
         *
         *    Load zeta vectors in 4-4 layout
         */
        mr      dup_rinp, rinp
        li      len_2, 8

        GS_Butterfly_4x_len4
        addi    dup_rinp, dup_rinp, 128
        GS_Butterfly_4x_len4
        addi    dup_rinp, dup_rinp, 128
        GS_Butterfly_4x_len4
        addi    dup_rinp, dup_rinp, 128
        GS_Butterfly_4x_len4
        addi    dup_rinp, dup_rinp, 128

.balign 16
        /*
         * Layer 3. len = 8, start = 0, 128, 256, 384
         */
        li      len_2, 16

        GS_Butterfly_4x 0, 32
        GS_Butterfly_4x 128, 32
        GS_Butterfly_4x 256, 32
        GS_Butterfly_4x 384, 32

.balign 16
        /*
         * Layer 4. len = 16, start = 0, 16, 256, 272
         *
         * The 4 calls share zeta blocks pairwise: starts 0 and 16 hit the
         * same 4 j-groups (with different sub-indices within each), and
         * likewise 256 and 272. Each pair therefore needs the same 4-zeta
         * block, but `GS_Butterfly_4x` calls `Load_next_4zetas` internally
         * which auto-advances `zeta_inp`/`zeta_tw_inp` by 64 bytes, so we
         * rewind by 64 before the second call of each pair to re-load the
         * same block.
         *
         * (NTT layer 4 sidesteps this by passing zeta registers explicitly
         * to `CT_Butterfly_4x` and lifting `Load_next_4zetas` to the layer
         * level. Worth aligning if this gets revisited.)
         */
        li      len_2, 32

        GS_Butterfly_4x 0, 64

        addi    zeta_inp, zeta_inp, -64
        addi    zeta_tw_inp, zeta_tw_inp, -64
        GS_Butterfly_4x 16, 64

        GS_Butterfly_4x 256, 64

        addi    zeta_inp, zeta_inp, -64
        addi    zeta_tw_inp, zeta_tw_inp, -64
        GS_Butterfly_4x 272, 64

.balign 16
        /*
         * Layer 5. len = 32, start = 0, 128, 256, 384
         */
        li      len_2, 64

        GS_Butterfly_Broadcast_4x 0, 16
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        GS_Butterfly_Broadcast_4x 128, 16
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        GS_Butterfly_Broadcast_4x 256, 16
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        GS_Butterfly_Broadcast_4x 384, 16
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16

.balign 16
        /*
         * Layer 6. len = 64, start = 0, 64, 256, 320
         */
        li      len_2, 128

        GS_Butterfly_Broadcast_4x 0, 16
        GS_Butterfly_Broadcast_4x 64, 16
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16
        GS_Butterfly_Broadcast_4x 256, 16
        GS_Butterfly_Broadcast_4x 320, 16
        addi    zeta_inp, zeta_inp, 16
        addi    zeta_tw_inp, zeta_tw_inp, 16

.balign 16
        /*
         * Layer 7. len = 128, start = 0, 64, 128, 192
         */
        li      len_2, 256          /* len*2 */

        GS_Butterfly_Broadcast_4x 0, 16
        GS_Butterfly_Broadcast_4x 64, 16
        GS_Butterfly_Broadcast_4x 128, 16
        GS_Butterfly_Broadcast_4x 192, 16

        RESTORE_REGS
        blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V20159
#undef V_25
#undef V_26
#undef V_MKQ
#undef V_ZERO
#undef V_NMKQ
#undef V_Z0
#undef V_Z1
#undef V_Z2
#undef V_Z3
#undef V_ZETA
#undef V_NINV
#undef V_NINV_TW
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
#undef vdata_brt1
#undef vdata_brt2
#undef vdata_brt3
#undef vdata_brt4
#undef vdata_t1
#undef vdata_t2
#undef vdata_t3
#undef vdata_t4
#undef vresult_brt1
#undef vresult_brt2
#undef vresult_brt3
#undef vresult_brt4
#undef vresult_t1
#undef vresult_t2
#undef vresult_t3
#undef vresult_t4
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
#undef VS_NMKQ_STASH
#undef VS_ZERO_STASH
#undef VS_MKQ_STASH
#undef VS_25_STASH
#undef VS_26_STASH

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && __POWER8_VECTOR__ */
