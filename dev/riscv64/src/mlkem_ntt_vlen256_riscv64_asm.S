/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: ntt_vlen256_riscv64_asm
  Description: Forward negacyclic NTT of a polynomial in place, output in bitreversed order (VLEN=256 only)
  Signature: void mlk_ntt_vlen256_riscv64_asm(int16_t p[256], const int16_t zetas[800], const uint16_t perms[160])
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
      size_bytes: 1600
      permissions: read-only
      c_parameter: const int16_t zetas[800]
      description: Twiddle table (mlk_rv64v_ntt256_zetas)
    a2:
      type: buffer
      size_bytes: 320
      permissions: read-only
      c_parameter: const uint16_t perms[160]
      description: Permutation table (mlk_rv64v_ntt256_perms)
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "rv64v_ntt.inc"

/*
 * Forward NTT for VLEN=256 (16 lanes per register).
 *
 * All 256 coefficients are held in v16-v31 throughout. Layers 1-4 are
 * described in rv64v_ntt.inc.
 *
 * Layers 5-7 operate within each block of 32 coefficients (a register pair).
 * Before each layer, the block is permuted so that the butterfly partners
 * are in the two halves of the pair, at the same lane; the butterfly then
 * uses per-lane twiddles. A final permutation restores the order.
 *
 * Tables:
 * - zetas: after the 32 entries for layers 1-4, for each of the 8 blocks,
 *   the per-lane twiddles for layers 5, 6, 7, each followed by their twisted
 *   constants (6 vectors of 16 entries per block).
 * - perms: p8, p4, p2, p1 (32 entries each), where p8, p4, p2 swap bit 4 of
 *   the index with bit 3, 2, 1, respectively, and p1 = p2 . p4 . p8.
 *
 * Bounds: the input is bounded by q in absolute value; after layer L, all
 * coefficients are bounded by (L+1)*q, so the output is bounded by 8q.
 */

/* Layers 5-7 for the block in the register pair \lo, \hi. */
.macro ntt_block lo, hi
        /* Layer 5: < 6q */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_a
        vsetvl_m1
        load_lane_twiddles 32
        ct_bfly_lanes pair, pair_hi

        /* Layer 6: < 7q */
        vsetvl_m2
        vrgatherei16.vv \lo, pair, perm_b
        vsetvl_m1
        load_lane_twiddles 32
        ct_bfly_lanes \lo, \hi

        /* Layer 7: < 8q */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_c
        vsetvl_m1
        load_lane_twiddles 32
        ct_bfly_lanes pair, pair_hi

        /* Restore the order */
        vsetvl_m2
        vrgatherei16.vv \lo, pair, perm_d
.endm

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(ntt_vlen256_riscv64_asm)
MLK_ASM_FN_SYMBOL(ntt_vlen256_riscv64_asm)

        ntt_setup   16

        /* Load all coefficients */
        vsetvl_m8
        vle16.v     v16, (data)
        addi        tmp_addr, data, 256
        vle16.v     v24, (tmp_addr)

        ntt_layers1234

        /* Load the permutations p8, p4, p2, p1 */
        vsetvl_m2
        vle16.v     perm_a, (perms)
        addi        tmp_addr, perms, 64
        vle16.v     perm_b, (tmp_addr)
        addi        tmp_addr, perms, 128
        vle16.v     perm_c, (tmp_addr)
        addi        tmp_addr, perms, 192
        vle16.v     perm_d, (tmp_addr)

        addi        lane_ptr, zetas, 64
        ntt_block   v16, v17
        ntt_block   v18, v19
        ntt_block   v20, v21
        ntt_block   v22, v23
        ntt_block   v24, v25
        ntt_block   v26, v27
        ntt_block   v28, v29
        ntt_block   v30, v31

        /* Store all coefficients */
        vsetvl_m8
        vse16.v     v16, (data)
        addi        tmp_addr, data, 256
        vse16.v     v24, (tmp_addr)

        ret
.option pop

MLK_ASM_FN_SIZE(ntt_vlen256_riscv64_asm)

/* simpasm: footer-start */
#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
