/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Keccak-f[1600] permutation of one state with AVX-512, the round
 * constants given as an argument. The code needs only AVX-512F and VL,
 * but is built under MLK_SYS_X86_64_AVX512, which also requires DQ for
 * keccak_f1600_x4_avx512_asm.
 *
 * Lane i of the state is in quadword 0 of the xmm register i (EVEX
 * encoding gives 32 of them), and is permuted there with vprolq and
 * vpternlogq and no spills, pi by renaming the registers: four
 * rounds to an iteration of the loop, at the end of which register
 * moves restore lane i to register i.
 */

#include "../../../../common.h"

#if defined(MLK_SYS_X86_64_AVX512) && \
    defined(MLK_FIPS202_X86_64_NEED_X1_AVX512) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/*yaml
  Name: keccak_f1600_x1_avx512_asm
  Description: x86_64 AVX-512 Keccak-f[1600] permutation for a single state
  Signature: void mlk_keccak_f1600_x1_avx512_asm(uint64_t state[25], const uint64_t rc[24])
  ABI:
    Architecture: x86_64
    CallingConvention: SysV
    Features: [AVX512]
    rdi:
      type: buffer
      size_bytes: 200
      permissions: read/write
      c_parameter: uint64_t state[25]
      description: Keccak state (25 x uint64_t)
    rsi:
      type: buffer
      size_bytes: 192
      permissions: read-only
      c_parameter: const uint64_t rc[24]
      description: Round constants (24 x uint64_t)
*/

/* simpasm: header-end */

#include "keccak_f1600_avx512.inc"

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_avx512_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_avx512_asm)

        /*
         * Load lane i into quadword 0 of xmm<i>. GNU as and LLVM encode
         * vmovq between memory and xmm16..xmm31 differently;
         * scripts/simpasm writes out the bytes of GNU as, which the HOL
         * Light proof is about.
         */
        vmovq      (%rdi), %xmm0
        vmovq      8(%rdi), %xmm1
        vmovq      16(%rdi), %xmm2
        vmovq      24(%rdi), %xmm3
        vmovq      32(%rdi), %xmm4
        vmovq      40(%rdi), %xmm5
        vmovq      48(%rdi), %xmm6
        vmovq      56(%rdi), %xmm7
        vmovq      64(%rdi), %xmm8
        vmovq      72(%rdi), %xmm9
        vmovq      80(%rdi), %xmm10
        vmovq      88(%rdi), %xmm11
        vmovq      96(%rdi), %xmm12
        vmovq      104(%rdi), %xmm13
        vmovq      112(%rdi), %xmm14
        vmovq      120(%rdi), %xmm15
        vmovq      128(%rdi), %xmm16
        vmovq      136(%rdi), %xmm17
        vmovq      144(%rdi), %xmm18
        vmovq      152(%rdi), %xmm19
        vmovq      160(%rdi), %xmm20
        vmovq      168(%rdi), %xmm21
        vmovq      176(%rdi), %xmm22
        vmovq      184(%rdi), %xmm23
        vmovq      192(%rdi), %xmm24

        /* The 24 rounds, four per iteration; rax is the end of rc */
        lea        192(%rsi), %rax
mlk_keccak_f1600_x1_avx512_loop:
        keccak_f1600_4rounds xmm, 2
        add        $32, %rsi
        cmp        %rax, %rsi
        jne        mlk_keccak_f1600_x1_avx512_loop

        /* Store lane i from xmm<i> */
        vmovq      %xmm0, (%rdi)
        vmovq      %xmm1, 8(%rdi)
        vmovq      %xmm2, 16(%rdi)
        vmovq      %xmm3, 24(%rdi)
        vmovq      %xmm4, 32(%rdi)
        vmovq      %xmm5, 40(%rdi)
        vmovq      %xmm6, 48(%rdi)
        vmovq      %xmm7, 56(%rdi)
        vmovq      %xmm8, 64(%rdi)
        vmovq      %xmm9, 72(%rdi)
        vmovq      %xmm10, 80(%rdi)
        vmovq      %xmm11, 88(%rdi)
        vmovq      %xmm12, 96(%rdi)
        vmovq      %xmm13, 104(%rdi)
        vmovq      %xmm14, 112(%rdi)
        vmovq      %xmm15, 120(%rdi)
        vmovq      %xmm16, 128(%rdi)
        vmovq      %xmm17, 136(%rdi)
        vmovq      %xmm18, 144(%rdi)
        vmovq      %xmm19, 152(%rdi)
        vmovq      %xmm20, 160(%rdi)
        vmovq      %xmm21, 168(%rdi)
        vmovq      %xmm22, 176(%rdi)
        vmovq      %xmm23, 184(%rdi)
        vmovq      %xmm24, 192(%rdi)

        /* Clear upper halves of YMM registers to avoid a performance
         * penalty when switching to SSE. */
        vzeroupper
        ret

/* simpasm: footer-start */
#endif /* MLK_SYS_X86_64_AVX512 && MLK_FIPS202_X86_64_NEED_X1_AVX512 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
