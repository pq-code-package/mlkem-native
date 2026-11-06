/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: intt_vlen128_riscv64_asm
  Description: Inverse negacyclic NTT of a polynomial in place, input in bitreversed order, with scaling to Montgomery form (VLEN=128 only)
  Signature: void mlk_intt_vlen128_riscv64_asm(int16_t p[256], const int16_t zetas[576], const uint16_t perms[96])
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
      description: Twiddle table (mlk_rv64v_intt128_zetas)
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
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (!defined(MLK_CONFIG_NO_ENCAPS_API) || !defined(MLK_CONFIG_NO_DECAPS_API))
/* simpasm: header-end */

#include "rv64v_ntt.inc"

/*
 * Inverse NTT for VLEN=128 (8 lanes per register); the reverse of the
 * forward NTT, with the same scaling and reductions as the VLEN=256
 * version.
 *
 * - Layers 7-5 run on units of 16 coefficients (a register pair), 8 units
 *   at a time. The unit is permuted so that the layer 7 partners are in the
 *   two halves of the pair, and multiplied by 2^16 / 128 = 512 mod q. After
 *   layers 7 and 6, it is permuted again; the last permutation restores the
 *   order, so that layer 5 pairs the two registers of the unit directly,
 *   with a scalar twiddle.
 * - Layers 4-1 (see rv64v_ntt.inc) run twice, once for each half of the
 *   lanes.
 *
 * Tables:
 * - zetas: after the 32 entries for layers 4-1, the layer 5 twiddle of
 *   each of the 16 units with its twisted constant (32 entries); then, for
 *   each unit, the per-lane twiddles for layers 7 and 6, each followed by
 *   their twisted constants (4 vectors of 8 entries per unit).
 * - perms: the three permutations of the inverse NTT at offset 48 (in
 *   entries), as computed by scripts/autogen.
 */

/* Layers 4-1 for half \half of the lanes. */
.macro intt_half half
        vsetvl_m1
        access_layers1234 vle16.v, \half
        intt_layers4321
        vsetvl_m1
        access_layers1234 vse16.v, \half
.endm

/* Layers 7-5 for the unit in the register pair \lo, \hi; the result is
 * stored to out_ptr, which is advanced. With t0, t1 the two halves of the
 * unit, the bounds in units of q are noted below. */
.macro intt_unit lo, hi
        /* Scale by 512 mod q: t0, t1 < 1 */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_a
        vsetvl_m1
        barrett_mul_const pair, 512, 5040
        barrett_mul_scalar pair_hi, tmp_t

        /* Layer 7: t0 < 2, t1 < 1 */
        load_lane_twiddles 16
        gs_bfly_lanes pair, pair_hi

        /* Layer 6: t0 < 4, t1 < 1 */
        vsetvl_m2
        vrgatherei16.vv \lo, pair, perm_b
        vsetvl_m1
        load_lane_twiddles 16
        gs_bfly_lanes \lo, \hi

        /* Layer 5: t0 < 8, t1 < 1; then reduce t0 to below q */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_c
        vsetvl_m1
        load_next_scalar
        gs_bfly_scalar pair, pair_hi, tmp_t
        barrett_mul_const pair, 1, 10

        /* Store */
        vsetvl_m2
        vse16.v     pair, (out_ptr)
        addi        out_ptr, out_ptr, 32
.endm

/* Layers 7-5 for the 8 units starting at out_ptr. */
.macro intt_units8
        vsetvl_m8
        vle16.v     v16, (out_ptr)
        addi        tmp_addr, out_ptr, 128
        vle16.v     v24, (tmp_addr)
        intt_unit   v16, v17
        intt_unit   v18, v19
        intt_unit   v20, v21
        intt_unit   v22, v23
        intt_unit   v24, v25
        intt_unit   v26, v27
        intt_unit   v28, v29
        intt_unit   v30, v31
.endm

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(intt_vlen128_riscv64_asm)
MLK_ASM_FN_SYMBOL(intt_vlen128_riscv64_asm)

        ntt_setup   8

        /* Load the three permutations */
        vsetvl_m2
        addi        tmp_addr, perms, 96
        vle16.v     perm_a, (tmp_addr)
        addi        tmp_addr, perms, 128
        vle16.v     perm_b, (tmp_addr)
        addi        tmp_addr, perms, 160
        vle16.v     perm_c, (tmp_addr)

        addi        scalar_ptr, zetas, 64
        addi        lane_ptr, zetas, 128
        mv          out_ptr, data
        intt_units8
        intt_units8

        intt_half   0
        intt_half   1

        ret
.option pop

MLK_ASM_FN_SIZE(intt_vlen128_riscv64_asm)

/* simpasm: footer-start */
#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && (!MLK_CONFIG_NO_ENCAPS_API || \
          !MLK_CONFIG_NO_DECAPS_API) */
