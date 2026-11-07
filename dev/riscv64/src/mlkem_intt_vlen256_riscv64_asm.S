/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: intt_vlen256_riscv64_asm
  Description: Inverse negacyclic NTT of a polynomial in place, input in bitreversed order, with scaling to Montgomery form (VLEN=256 only)
  Signature: void mlk_intt_vlen256_riscv64_asm(int16_t p[256], const int16_t zetas[800], const uint16_t perms[160])
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
      description: Twiddle table (mlk_rv64v_intt256_zetas)
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
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (!defined(MLK_CONFIG_NO_ENCAPS_API) || !defined(MLK_CONFIG_NO_DECAPS_API))
/* simpasm: header-end */

#include "rv64v_ntt.inc"

/*
 * Inverse NTT for VLEN=256 (16 lanes per register); the reverse of the
 * forward NTT.
 *
 * All 256 coefficients are held in v16-v31 throughout. Layers 4-1 are
 * described in rv64v_ntt.inc.
 *
 * Layers 7-5 operate within each block of 32 coefficients (a register
 * pair), as in the forward NTT. The block is first multiplied by
 * 2^16 / 128 = 512 mod q, which accounts for the division by 128 and the
 * conversion to Montgomery form, and also reduces arbitrary 16-bit inputs
 * to below q.
 *
 * Tables:
 * - zetas: after the 32 entries for layers 4-1, for each of the 8 blocks,
 *   the per-lane twiddles for layers 7, 6, 5, each followed by their twisted
 *   constants (6 vectors of 16 entries per block).
 * - perms: p8, p4, p2 at offsets 0, 32, 64 and p0 = p8 . p4 . p2 at offset
 *   128 (in entries); see the forward NTT.
 */

/* Layers 7-5 for the block in the register pair \lo, \hi. With t0, t1 the
 * two halves of the block, the bounds in units of q are noted below. */
.macro intt_block lo, hi
        /* Scale by 512 mod q: t0, t1 < 1 */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_a
        vsetvl_m1
        barrett_mul_const pair, 512, 5040
        barrett_mul_scalar pair_hi, tmp_t

        /* Layer 7: t0 < 2, t1 < 1 */
        load_lane_twiddles 32
        gs_bfly_lanes pair, pair_hi

        /* Layer 6: t0 < 4, t1 < 1 */
        vsetvl_m2
        vrgatherei16.vv \lo, pair, perm_b
        vsetvl_m1
        load_lane_twiddles 32
        gs_bfly_lanes \lo, \hi

        /* Layer 5: t0 < 8, t1 < 1; then reduce t0 to below q */
        vsetvl_m2
        vrgatherei16.vv pair, \lo, perm_c
        vsetvl_m1
        load_lane_twiddles 32
        gs_bfly_lanes pair, pair_hi
        barrett_mul_const pair, 1, 10

        /* Restore the order */
        vsetvl_m2
        vrgatherei16.vv \lo, pair, perm_d
.endm

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(intt_vlen256_riscv64_asm)
MLK_ASM_FN_SYMBOL(intt_vlen256_riscv64_asm)

        ntt_setup   16

        /* Load all coefficients */
        vsetvl_m8
        vle16.v     v16, (data)
        addi        tmp_addr, data, 256
        vle16.v     v24, (tmp_addr)

        /* Load the permutations p0, p2, p4, p8 */
        vsetvl_m2
        addi        tmp_addr, perms, 256
        vle16.v     perm_a, (tmp_addr)
        addi        tmp_addr, perms, 128
        vle16.v     perm_b, (tmp_addr)
        addi        tmp_addr, perms, 64
        vle16.v     perm_c, (tmp_addr)
        vle16.v     perm_d, (perms)

        addi        lane_ptr, zetas, 64
        intt_block  v16, v17
        intt_block  v18, v19
        intt_block  v20, v21
        intt_block  v22, v23
        intt_block  v24, v25
        intt_block  v26, v27
        intt_block  v28, v29
        intt_block  v30, v31

        intt_layers4321

        /* Store all coefficients */
        vse16.v     v16, (data)
        addi        tmp_addr, data, 256
        vse16.v     v24, (tmp_addr)

        ret
.option pop

MLK_ASM_FN_SIZE(intt_vlen256_riscv64_asm)

/* simpasm: footer-start */
#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && (!MLK_CONFIG_NO_ENCAPS_API || \
          !MLK_CONFIG_NO_DECAPS_API) */
