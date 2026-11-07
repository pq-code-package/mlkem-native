/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: ntt_vlen128_riscv64_asm
  Description: Forward negacyclic NTT of a polynomial in place, output in bitreversed order (VLEN=128 only)
  Signature: void mlk_ntt_vlen128_riscv64_asm(int16_t p[256], const int16_t zetas[576], const uint16_t perms[96])
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [RVV]
    a0:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t p[256]
      description: Input/output polynomial
    a1:
      type: buffer
      size_bytes: 1152
      permissions: read-only
      c_parameter: const int16_t zetas[576]
      description: Twiddle table (mlk_rv64v_ntt128_zetas)
    a2:
      type: buffer
      size_bytes: 192
      permissions: read-only
      c_parameter: const uint16_t perms[96]
      description: Permutation table (mlk_rv64v_ntt128_perms)
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "rv64v_ntt.inc"

/*
 * Forward NTT for VLEN=128 (8 lanes per register).
 *
 * The polynomial does not fit into the 16 registers v16-v31, so the NTT
 * makes two passes over memory:
 *
 * - Layers 1-4 (see rv64v_ntt.inc) run twice, once for each half of the
 *   lanes.
 * - Layers 5-7 run on units of 16 coefficients (a register pair), 8 units
 *   at a time. Layer 5 pairs the two registers of a unit directly, with a
 *   scalar twiddle. Before layers 6 and 7, the unit is permuted so that the
 *   butterfly partners are in the two halves of the pair, at the same lane;
 *   the butterflies use per-lane twiddles. A final permutation restores the
 *   order.
 *
 * Tables:
 * - zetas: after the 32 entries for layers 1-4, the layer 5 twiddle of
 *   each of the 16 units with its twisted constant (32 entries); then, for
 *   each unit, the per-lane twiddles for layers 6 and 7, each followed by
 *   their twisted constants (4 vectors of 8 entries per unit).
 * - perms: the three permutations of the forward NTT (16 entries each), as
 *   computed by scripts/autogen.
 *
 * Bounds: the input is bounded by q in absolute value; after layer L, all
 * coefficients are bounded by (L+1)*q, so the output is bounded by 8q.
 */

/* Layers 1-4 for half \half of the lanes. */
.macro ntt_half half
        vsetvl_m1
        access_layers1234 vle16.v, \half
        ntt_layers1234
        vsetvl_m1
        access_layers1234 vse16.v, \half
.endm

/* Layers 5-7 for the unit in the register pair \lo, \hi; the result is
 * stored to out_ptr, which is advanced. */
.macro ntt_unit lo, hi
        /* Layer 5: < 6q */
        vsetvl_m1
        load_next_scalar
        ct_bfly_scalar \lo, \hi, v0

        /* Layer 6: < 7q */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_a
        vsetvl_m1
        load_lane_twiddles 16
        ct_bfly_lanes pair, pair_hi

        /* Layer 7: < 8q */
        vsetvl_m2
        vrgatherei16.vv \lo, pair, perm_b
        vsetvl_m1
        load_lane_twiddles 16
        ct_bfly_lanes \lo, \hi

        /* Restore the order and store */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_c
        vse16.v     pair, (out_ptr)
        addi        out_ptr, out_ptr, 32
.endm

/* Layers 5-7 for the 8 units starting at out_ptr. */
.macro ntt_units8
        vsetvl_m8
        vle16.v     v16, (out_ptr)
        addi        tmp_addr, out_ptr, 128
        vle16.v     v24, (tmp_addr)
        ntt_unit    v16, v17
        ntt_unit    v18, v19
        ntt_unit    v20, v21
        ntt_unit    v22, v23
        ntt_unit    v24, v25
        ntt_unit    v26, v27
        ntt_unit    v28, v29
        ntt_unit    v30, v31
.endm

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(ntt_vlen128_riscv64_asm)
MLK_ASM_FN_SYMBOL(ntt_vlen128_riscv64_asm)

        ntt_setup   8

        ntt_half    0
        ntt_half    1

        /* Load the three permutations */
        vsetvl_m2
        vle16.v     perm_a, (perms)
        addi        tmp_addr, perms, 32
        vle16.v     perm_b, (tmp_addr)
        addi        tmp_addr, perms, 64
        vle16.v     perm_c, (tmp_addr)

        addi        scalar_ptr, zetas, 64
        addi        lane_ptr, zetas, 128
        mv          out_ptr, data
        ntt_units8
        ntt_units8

        ret
.option pop

MLK_ASM_FN_SIZE(ntt_vlen128_riscv64_asm)

/* simpasm: footer-start */
#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
