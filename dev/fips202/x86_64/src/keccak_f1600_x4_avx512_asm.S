/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Keccak-f[1600] permutation of four sequential states with AVX-512
 * (F, VL and DQ), the round constants given as an argument.
 *
 * The four states are transposed into 25 ymm registers, lane i of
 * state j in quadword j of the register i (EVEX encoding gives 32
 * of them), permuted there with vprolq and vpternlogq and no spills,
 * with the same loop as keccak_f1600_x1_avx512_asm, and transposed
 * back. Only 128-bit and 256-bit registers are used: on some
 * processors, 512-bit instructions mixed with the heavy 256-bit
 * instructions of the arithmetic backend lower the clock frequency
 * of the core.
 */

#include "../../../../common.h"

#if defined(MLK_SYS_X86_64_AVX512) && \
    defined(MLK_FIPS202_X86_64_NEED_X4_AVX512) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/*yaml
  Name: keccak_f1600_x4_avx512_asm
  Description: x86_64 AVX-512 Keccak-f[1600] permutation for four sequential states
  Signature: void mlk_keccak_f1600_x4_avx512_asm(uint64_t states[100], const uint64_t rc[24])
  ABI:
    Architecture: x86_64
    CallingConvention: SysV
    Features: [AVX512]
    rdi:
      type: buffer
      size_bytes: 800
      permissions: read/write
      c_parameter: uint64_t states[100]
      description: Four sequential Keccak states (4 x 25 x uint64_t)
    rsi:
      type: buffer
      size_bytes: 192
      permissions: read-only
      c_parameter: const uint64_t rc[24]
      description: Round constants (24 x uint64_t)
*/

/* simpasm: header-end */

#include "keccak_f1600_avx512.inc"

/*
 * 4x4 transpose of quadwords: quadword k of o<j> = quadword j of i<k>.
 * t0..t3 are temporaries; t3 may be i0, and o3 may be t0.
 */
.macro transpose4 i0, i1, i2, i3, t0, t1, t2, t3, o0, o1, o2, o3
        vpunpcklqdq %ymm\i1, %ymm\i0, %ymm\t0
        vpunpckhqdq %ymm\i1, %ymm\i0, %ymm\t1
        vpunpcklqdq %ymm\i3, %ymm\i2, %ymm\t2
        vpunpckhqdq %ymm\i3, %ymm\i2, %ymm\t3
        vshufi64x2 $0x0, %ymm\t2, %ymm\t0, %ymm\o0
        vshufi64x2 $0x0, %ymm\t3, %ymm\t1, %ymm\o1
        vshufi64x2 $0x3, %ymm\t2, %ymm\t0, %ymm\o2
        vshufi64x2 $0x3, %ymm\t3, %ymm\t1, %ymm\o3
.endm

/*
 * Load lanes l..l+3 of the four states, l = off/8, from off+200j(%rdi)
 * for state j, and transpose them: quadword j of r<k> is lane l+k of
 * state j. ymm25..ymm31 are temporaries.
 */
.macro load4 off, r0, r1, r2, r3
        vmovdqu64  \off(%rdi), %ymm25
        vmovdqu64  \off+200(%rdi), %ymm26
        vmovdqu64  \off+400(%rdi), %ymm27
        vmovdqu64  \off+600(%rdi), %ymm28
        transpose4 25, 26, 27, 28, 29, 30, 31, 25, \r0, \r1, \r2, \r3
.endm

/* The inverse of load4 */
.macro store4 off, r0, r1, r2, r3
        transpose4 \r0, \r1, \r2, \r3, 25, 26, 27, 28, 29, 30, 31, 25
        vmovdqu64  %ymm29, \off(%rdi)
        vmovdqu64  %ymm30, \off+200(%rdi)
        vmovdqu64  %ymm31, \off+400(%rdi)
        vmovdqu64  %ymm25, \off+600(%rdi)
.endm

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_avx512_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_avx512_asm)

        /* Load lane i of state j into quadword j of ymm<i> */
        load4      0, 0, 1, 2, 3
        load4      32, 4, 5, 6, 7
        load4      64, 8, 9, 10, 11
        load4      96, 12, 13, 14, 15
        load4      128, 16, 17, 18, 19
        load4      160, 20, 21, 22, 23
        /*
         * Lane 24 by itself. GNU as and LLVM encode vmovq between memory
         * and xmm16..xmm31 differently; scripts/simpasm writes out the
         * bytes of GNU as, which the HOL Light proof is about.
         */
        vmovq      192(%rdi), %xmm24
        vpinsrq    $1, 392(%rdi), %xmm24, %xmm24
        vmovq      592(%rdi), %xmm25
        vpinsrq    $1, 792(%rdi), %xmm25, %xmm25
        vinserti32x4 $1, %xmm25, %ymm24, %ymm24

        /* The 24 rounds, four per iteration; rax is the end of rc */
        lea        192(%rsi), %rax
mlk_keccak_f1600_x4_avx512_loop:
        keccak_f1600_4rounds ymm, 4
        add        $32, %rsi
        cmp        %rax, %rsi
        jne        mlk_keccak_f1600_x4_avx512_loop

        /* Store lane i of state j from quadword j of ymm<i> */
        store4     0, 0, 1, 2, 3
        store4     32, 4, 5, 6, 7
        store4     64, 8, 9, 10, 11
        store4     96, 12, 13, 14, 15
        store4     128, 16, 17, 18, 19
        store4     160, 20, 21, 22, 23
        /* Lane 24 */
        vmovq      %xmm24, 192(%rdi)
        vpextrq    $1, %xmm24, 392(%rdi)
        vextracti32x4 $1, %ymm24, %xmm25
        vmovq      %xmm25, 592(%rdi)
        vpextrq    $1, %xmm25, 792(%rdi)

        /* Clear upper halves of YMM registers to avoid a performance
         * penalty when switching to SSE. */
        vzeroupper
        ret

/* simpasm: footer-start */
#endif /* MLK_SYS_X86_64_AVX512 && MLK_FIPS202_X86_64_NEED_X4_AVX512 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
