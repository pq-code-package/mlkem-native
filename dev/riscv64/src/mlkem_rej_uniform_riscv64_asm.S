/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: rej_uniform_riscv64_asm
  Description: Run rejection sampling on uniform random bytes to generate uniform random integers mod q
  Signature: uint64_t mlk_rej_uniform_riscv64_asm(int16_t *r, uint64_t len, const uint8_t *buf, uint64_t buflen)
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [RVV]
    a0:
      type: buffer
      size_bytes: 512
      permissions: write-only
      c_parameter: int16_t *r
      description: Output buffer (2 * len bytes)
    a1:
      type: scalar
      c_parameter: uint64_t len
      description: Maximum number of coefficients to sample
      test_with: 256  # MLKEM_N
    a2:
      type: buffer
      size_bytes: a3
      permissions: read-only
      c_parameter: const uint8_t *buf
      description: Input buffer
    a3:
      type: scalar
      c_parameter: uint64_t buflen
      description: Length of input buffer (must be multiple of 12)
      test_with: 504  # MLKEM_GEN_MATRIX_NBLOCKS * MLK_XOF_RATE
*/

#include "../../../common.h"
#if defined(MLK_SYS_RISCV64_RVV) && \
    defined(MLK_ARITH_BACKEND_RISCV64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

/*
 * Vector-length agnostic: works for any VLEN.
 *
 * Each iteration unpacks VL 12-bit values from 3*VL/2 bytes of input,
 * where VL = VLMAX for e16,m2 in the main loop. Once fewer than 3*VL/2
 * bytes remain, a single final iteration processes the rest with a
 * smaller VL. Since VLMAX is a power of 2 and buflen is a multiple of 12,
 * that smaller VL is a multiple of 8 and below VLMAX, so vsetvli returns
 * it unchanged.
 *
 * Unpacking: Lane i holds bits [12i, 12i+12) of the input. Gather the
 * halfword containing bit 12i into lane i, shift it right by 12i mod 16,
 * and OR in the next halfword shifted left by 16 - (12i mod 16). The next
 * halfword is lane i+1 of the gathered vector, which is either the same
 * halfword (if 12i mod 16 == 0, making the OR a no-op) or the next one.
 * Vector shifts use the shift amount modulo 16, so the per-lane shift
 * amounts are just 12i and 4i.
 *
 * The lane constants are computed in 16 bits. 12i overflows for i > 5461,
 * which only matters for lanes that are never used: since buflen <= 4096,
 * an iteration never processes more than 2730 lanes.
 */

#define out             a0  /* output pointer (advancing) */
#define len             a1
#define buf             a2  /* input pointer (advancing) */
#define remaining       a3  /* remaining input bytes */
#define ctr             a4  /* number of sampled coefficients */
#define chunk_bytes     a5  /* bytes per iteration (3*VL/2) */
#define chunk_halfwords a6  /* halfwords loaded per iteration (3*VL/4) */
#define room            a7  /* len - ctr */
#define vl              t0  /* coefficients per iteration */
#define accepted        t1  /* coefficients accepted in this iteration */
#define modulus         t2
#define mask12          t3
#define tmp             t4

#define accept_mask     v0  /* mask of accepted coefficients */
#define gather_idx      v2  /* 12i >> 4 (register group of 2) */
#define shift_right     v4  /* 12i */
#define shift_left      v6  /* 4i */
#define input           v8
#define coeffs          v10 /* gathered input, then unpacked coefficients */
#define coeffs_next     v12 /* gathered input slid down by one lane */
#define compressed      v14 /* accepted coefficients */

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(rej_uniform_riscv64_asm)
MLK_ASM_FN_SYMBOL(rej_uniform_riscv64_asm)

        li          ctr, 0
        li          modulus, MLKEM_Q
        li          mask12, 0xFFF

        /* Set up lane-dependent constants for VL = VLMAX.
         * They are prefix-consistent, so also valid for smaller VL. */
        vsetvli     vl, zero, e16, m2, ta, ma
        vid.v       shift_left
        li          tmp, 12
        vmul.vx     shift_right, shift_left, tmp
        vsrl.vi     gather_idx, shift_right, 4
        vsll.vi     shift_left, shift_left, 2

        /* chunk_bytes = 3*VL/2, chunk_halfwords = 3*VL/4 */
        slli        chunk_bytes, vl, 1
        add         chunk_bytes, chunk_bytes, vl
        srli        chunk_halfwords, chunk_bytes, 2
        srli        chunk_bytes, chunk_bytes, 1

mlk_rej_uniform_riscv64_loop:
        bgeu        ctr, len, mlk_rej_uniform_riscv64_done
        bltu        remaining, chunk_bytes, mlk_rej_uniform_riscv64_tail

mlk_rej_uniform_riscv64_body:
        vsetvli     zero, chunk_halfwords, e16, m2, ta, ma
        vle16.v     input, (buf)
        add         buf, buf, chunk_bytes
        sub         remaining, remaining, chunk_bytes

        vsetvli     zero, vl, e16, m2, ta, ma
        vrgather.vv coeffs, input, gather_idx
        vslidedown.vi coeffs_next, coeffs, 1
        vsrl.vv     coeffs, coeffs, shift_right
        vsll.vv     coeffs_next, coeffs_next, shift_left
        vor.vv      coeffs, coeffs, coeffs_next
        vand.vx     coeffs, coeffs, mask12

        vmsltu.vx   accept_mask, coeffs, modulus
        vcpop.m     accepted, accept_mask
        vcompress.vm compressed, coeffs, accept_mask

        /* accepted = min(accepted, len - ctr) */
        sub         room, len, ctr
        bgeu        room, accepted, mlk_rej_uniform_riscv64_store
        mv          accepted, room
mlk_rej_uniform_riscv64_store:
        vsetvli     zero, accepted, e16, m2, ta, ma
        vse16.v     compressed, (out)
        add         ctr, ctr, accepted
        slli        accepted, accepted, 1  // in bytes
        add         out, out, accepted
        j           mlk_rej_uniform_riscv64_loop

mlk_rej_uniform_riscv64_tail:
        /* Fewer than 3*VL/2 bytes left. Process all remaining bytes in one
         * final iteration with VL = 2*remaining/3. Afterwards remaining = 0,
         * so the next pass through the loop exits via the beqz below. */
        beqz        remaining, mlk_rej_uniform_riscv64_done
        mv          chunk_bytes, remaining
        srli        chunk_halfwords, remaining, 1
        /* 2*x/3 = (x * 0xAAAB) >> 16, exact for multiples x of 3 below 2^16 */
        li          tmp, 0xAAAB
        mul         vl, remaining, tmp
        srli        vl, vl, 16
        j           mlk_rej_uniform_riscv64_body

mlk_rej_uniform_riscv64_done:
        mv          a0, ctr                // return value
        ret
.option pop

MLK_ASM_FN_SIZE(rej_uniform_riscv64_asm)

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef out
#undef len
#undef buf
#undef remaining
#undef ctr
#undef chunk_bytes
#undef chunk_halfwords
#undef room
#undef vl
#undef accepted
#undef modulus
#undef mask12
#undef tmp
#undef accept_mask
#undef gather_idx
#undef shift_right
#undef shift_left
#undef input
#undef coeffs
#undef coeffs_next
#undef compressed

/* simpasm: footer-start */
#endif /* MLK_SYS_RISCV64_RVV && MLK_ARITH_BACKEND_RISCV64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
