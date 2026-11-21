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

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_avx512_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_avx512_asm)

// Load lane i into xmm i

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
        // The loads and stores of the lanes in xmm16 and up are written
        // as bytes: for vmovq with an EVEX-only register, GNU as and
        // clang choose different (equivalent) opcodes, 66 0F 6E/7E and
        // F3 0F 7E/66 0F D6, and no syntax selects one. These are the
        // bytes that GNU as assembles.
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x47,0x10 // vmovq 128(%rdi), %xmm16
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x4f,0x11 // vmovq 136(%rdi), %xmm17
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x57,0x12 // vmovq 144(%rdi), %xmm18
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x5f,0x13 // vmovq 152(%rdi), %xmm19
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x67,0x14 // vmovq 160(%rdi), %xmm20
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x6f,0x15 // vmovq 168(%rdi), %xmm21
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x77,0x16 // vmovq 176(%rdi), %xmm22
        .byte 0x62,0xe1,0xfd,0x08,0x6e,0x7f,0x17 // vmovq 184(%rdi), %xmm23
        .byte 0x62,0x61,0xfd,0x08,0x6e,0x47,0x18 // vmovq 192(%rdi), %xmm24

// The 24 rounds, four at a time

        lea        192(%rsi), %rax
mlk_keccak_f1600_x1_avx512_loop:

// Round 1 of 4: theta

        vmovdqa64  %xmm0, %xmm25
        vpternlogq $0x96, %xmm10, %xmm5, %xmm25
        vpternlogq $0x96, %xmm20, %xmm15, %xmm25
        vmovdqa64  %xmm1, %xmm26
        vpternlogq $0x96, %xmm11, %xmm6, %xmm26
        vpternlogq $0x96, %xmm21, %xmm16, %xmm26
        vmovdqa64  %xmm2, %xmm27
        vpternlogq $0x96, %xmm12, %xmm7, %xmm27
        vpternlogq $0x96, %xmm22, %xmm17, %xmm27
        vmovdqa64  %xmm3, %xmm28
        vpternlogq $0x96, %xmm13, %xmm8, %xmm28
        vpternlogq $0x96, %xmm23, %xmm18, %xmm28
        vmovdqa64  %xmm4, %xmm29
        vpternlogq $0x96, %xmm14, %xmm9, %xmm29
        vpternlogq $0x96, %xmm24, %xmm19, %xmm29
        vprolq     $1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0
        vpternlogq $0x96, %xmm30, %xmm29, %xmm5
        vpternlogq $0x96, %xmm30, %xmm29, %xmm10
        vpternlogq $0x96, %xmm30, %xmm29, %xmm15
        vpternlogq $0x96, %xmm30, %xmm29, %xmm20
        vprolq     $1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm1
        vpternlogq $0x96, %xmm30, %xmm25, %xmm6
        vpternlogq $0x96, %xmm30, %xmm25, %xmm11
        vpternlogq $0x96, %xmm30, %xmm25, %xmm16
        vpternlogq $0x96, %xmm30, %xmm25, %xmm21
        vprolq     $1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm2
        vpternlogq $0x96, %xmm30, %xmm26, %xmm7
        vpternlogq $0x96, %xmm30, %xmm26, %xmm12
        vpternlogq $0x96, %xmm30, %xmm26, %xmm17
        vpternlogq $0x96, %xmm30, %xmm26, %xmm22
        vprolq     $1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm3
        vpternlogq $0x96, %xmm30, %xmm27, %xmm8
        vpternlogq $0x96, %xmm30, %xmm27, %xmm13
        vpternlogq $0x96, %xmm30, %xmm27, %xmm18
        vpternlogq $0x96, %xmm30, %xmm27, %xmm23
        vprolq     $1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm4
        vpternlogq $0x96, %xmm30, %xmm28, %xmm9
        vpternlogq $0x96, %xmm30, %xmm28, %xmm14
        vpternlogq $0x96, %xmm30, %xmm28, %xmm19
        vpternlogq $0x96, %xmm30, %xmm28, %xmm24

// rho

        vprolq     $36, %xmm5, %xmm5
        vprolq     $3, %xmm10, %xmm10
        vprolq     $41, %xmm15, %xmm15
        vprolq     $18, %xmm20, %xmm20
        vprolq     $1, %xmm1, %xmm1
        vprolq     $44, %xmm6, %xmm6
        vprolq     $10, %xmm11, %xmm11
        vprolq     $45, %xmm16, %xmm16
        vprolq     $2, %xmm21, %xmm21
        vprolq     $62, %xmm2, %xmm2
        vprolq     $6, %xmm7, %xmm7
        vprolq     $43, %xmm12, %xmm12
        vprolq     $15, %xmm17, %xmm17
        vprolq     $61, %xmm22, %xmm22
        vprolq     $28, %xmm3, %xmm3
        vprolq     $55, %xmm8, %xmm8
        vprolq     $25, %xmm13, %xmm13
        vprolq     $21, %xmm18, %xmm18
        vprolq     $56, %xmm23, %xmm23
        vprolq     $27, %xmm4, %xmm4
        vprolq     $20, %xmm9, %xmm9
        vprolq     $39, %xmm14, %xmm14
        vprolq     $8, %xmm19, %xmm19
        vprolq     $14, %xmm24, %xmm24

// pi (renaming the registers), chi and iota

        vmovdqa64  %xmm0, %xmm30
        vmovdqa64  %xmm6, %xmm31
        vpternlogq $0xd2, %xmm12, %xmm6, %xmm0
        vpxorq     (%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm18, %xmm12, %xmm6
        vpternlogq $0xd2, %xmm24, %xmm18, %xmm12
        vpternlogq $0xd2, %xmm30, %xmm24, %xmm18
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm24
        vmovdqa64  %xmm3, %xmm30
        vmovdqa64  %xmm9, %xmm31
        vpternlogq $0xd2, %xmm10, %xmm9, %xmm3
        vpternlogq $0xd2, %xmm16, %xmm10, %xmm9
        vpternlogq $0xd2, %xmm22, %xmm16, %xmm10
        vpternlogq $0xd2, %xmm30, %xmm22, %xmm16
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm22
        vmovdqa64  %xmm1, %xmm30
        vmovdqa64  %xmm7, %xmm31
        vpternlogq $0xd2, %xmm13, %xmm7, %xmm1
        vpternlogq $0xd2, %xmm19, %xmm13, %xmm7
        vpternlogq $0xd2, %xmm20, %xmm19, %xmm13
        vpternlogq $0xd2, %xmm30, %xmm20, %xmm19
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm20
        vmovdqa64  %xmm4, %xmm30
        vmovdqa64  %xmm5, %xmm31
        vpternlogq $0xd2, %xmm11, %xmm5, %xmm4
        vpternlogq $0xd2, %xmm17, %xmm11, %xmm5
        vpternlogq $0xd2, %xmm23, %xmm17, %xmm11
        vpternlogq $0xd2, %xmm30, %xmm23, %xmm17
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm23
        vmovdqa64  %xmm2, %xmm30
        vmovdqa64  %xmm8, %xmm31
        vpternlogq $0xd2, %xmm14, %xmm8, %xmm2
        vpternlogq $0xd2, %xmm15, %xmm14, %xmm8
        vpternlogq $0xd2, %xmm21, %xmm15, %xmm14
        vpternlogq $0xd2, %xmm30, %xmm21, %xmm15
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm21

// Round 2 of 4: theta

        vmovdqa64  %xmm0, %xmm25
        vpternlogq $0x96, %xmm1, %xmm3, %xmm25
        vpternlogq $0x96, %xmm2, %xmm4, %xmm25
        vmovdqa64  %xmm6, %xmm26
        vpternlogq $0x96, %xmm7, %xmm9, %xmm26
        vpternlogq $0x96, %xmm8, %xmm5, %xmm26
        vmovdqa64  %xmm12, %xmm27
        vpternlogq $0x96, %xmm13, %xmm10, %xmm27
        vpternlogq $0x96, %xmm14, %xmm11, %xmm27
        vmovdqa64  %xmm18, %xmm28
        vpternlogq $0x96, %xmm19, %xmm16, %xmm28
        vpternlogq $0x96, %xmm15, %xmm17, %xmm28
        vmovdqa64  %xmm24, %xmm29
        vpternlogq $0x96, %xmm20, %xmm22, %xmm29
        vpternlogq $0x96, %xmm21, %xmm23, %xmm29
        vprolq     $1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0
        vpternlogq $0x96, %xmm30, %xmm29, %xmm3
        vpternlogq $0x96, %xmm30, %xmm29, %xmm1
        vpternlogq $0x96, %xmm30, %xmm29, %xmm4
        vpternlogq $0x96, %xmm30, %xmm29, %xmm2
        vprolq     $1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm6
        vpternlogq $0x96, %xmm30, %xmm25, %xmm9
        vpternlogq $0x96, %xmm30, %xmm25, %xmm7
        vpternlogq $0x96, %xmm30, %xmm25, %xmm5
        vpternlogq $0x96, %xmm30, %xmm25, %xmm8
        vprolq     $1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm12
        vpternlogq $0x96, %xmm30, %xmm26, %xmm10
        vpternlogq $0x96, %xmm30, %xmm26, %xmm13
        vpternlogq $0x96, %xmm30, %xmm26, %xmm11
        vpternlogq $0x96, %xmm30, %xmm26, %xmm14
        vprolq     $1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm18
        vpternlogq $0x96, %xmm30, %xmm27, %xmm16
        vpternlogq $0x96, %xmm30, %xmm27, %xmm19
        vpternlogq $0x96, %xmm30, %xmm27, %xmm17
        vpternlogq $0x96, %xmm30, %xmm27, %xmm15
        vprolq     $1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm24
        vpternlogq $0x96, %xmm30, %xmm28, %xmm22
        vpternlogq $0x96, %xmm30, %xmm28, %xmm20
        vpternlogq $0x96, %xmm30, %xmm28, %xmm23
        vpternlogq $0x96, %xmm30, %xmm28, %xmm21

// rho

        vprolq     $36, %xmm3, %xmm3
        vprolq     $3, %xmm1, %xmm1
        vprolq     $41, %xmm4, %xmm4
        vprolq     $18, %xmm2, %xmm2
        vprolq     $1, %xmm6, %xmm6
        vprolq     $44, %xmm9, %xmm9
        vprolq     $10, %xmm7, %xmm7
        vprolq     $45, %xmm5, %xmm5
        vprolq     $2, %xmm8, %xmm8
        vprolq     $62, %xmm12, %xmm12
        vprolq     $6, %xmm10, %xmm10
        vprolq     $43, %xmm13, %xmm13
        vprolq     $15, %xmm11, %xmm11
        vprolq     $61, %xmm14, %xmm14
        vprolq     $28, %xmm18, %xmm18
        vprolq     $55, %xmm16, %xmm16
        vprolq     $25, %xmm19, %xmm19
        vprolq     $21, %xmm17, %xmm17
        vprolq     $56, %xmm15, %xmm15
        vprolq     $27, %xmm24, %xmm24
        vprolq     $20, %xmm22, %xmm22
        vprolq     $39, %xmm20, %xmm20
        vprolq     $8, %xmm23, %xmm23
        vprolq     $14, %xmm21, %xmm21

// pi (renaming the registers), chi and iota

        vmovdqa64  %xmm0, %xmm30
        vmovdqa64  %xmm9, %xmm31
        vpternlogq $0xd2, %xmm13, %xmm9, %xmm0
        vpxorq     8(%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm17, %xmm13, %xmm9
        vpternlogq $0xd2, %xmm21, %xmm17, %xmm13
        vpternlogq $0xd2, %xmm30, %xmm21, %xmm17
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm21
        vmovdqa64  %xmm18, %xmm30
        vmovdqa64  %xmm22, %xmm31
        vpternlogq $0xd2, %xmm1, %xmm22, %xmm18
        vpternlogq $0xd2, %xmm5, %xmm1, %xmm22
        vpternlogq $0xd2, %xmm14, %xmm5, %xmm1
        vpternlogq $0xd2, %xmm30, %xmm14, %xmm5
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm14
        vmovdqa64  %xmm6, %xmm30
        vmovdqa64  %xmm10, %xmm31
        vpternlogq $0xd2, %xmm19, %xmm10, %xmm6
        vpternlogq $0xd2, %xmm23, %xmm19, %xmm10
        vpternlogq $0xd2, %xmm2, %xmm23, %xmm19
        vpternlogq $0xd2, %xmm30, %xmm2, %xmm23
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm2
        vmovdqa64  %xmm24, %xmm30
        vmovdqa64  %xmm3, %xmm31
        vpternlogq $0xd2, %xmm7, %xmm3, %xmm24
        vpternlogq $0xd2, %xmm11, %xmm7, %xmm3
        vpternlogq $0xd2, %xmm15, %xmm11, %xmm7
        vpternlogq $0xd2, %xmm30, %xmm15, %xmm11
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm15
        vmovdqa64  %xmm12, %xmm30
        vmovdqa64  %xmm16, %xmm31
        vpternlogq $0xd2, %xmm20, %xmm16, %xmm12
        vpternlogq $0xd2, %xmm4, %xmm20, %xmm16
        vpternlogq $0xd2, %xmm8, %xmm4, %xmm20
        vpternlogq $0xd2, %xmm30, %xmm8, %xmm4
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm8

// Round 3 of 4: theta

        vmovdqa64  %xmm0, %xmm25
        vpternlogq $0x96, %xmm6, %xmm18, %xmm25
        vpternlogq $0x96, %xmm12, %xmm24, %xmm25
        vmovdqa64  %xmm9, %xmm26
        vpternlogq $0x96, %xmm10, %xmm22, %xmm26
        vpternlogq $0x96, %xmm16, %xmm3, %xmm26
        vmovdqa64  %xmm13, %xmm27
        vpternlogq $0x96, %xmm19, %xmm1, %xmm27
        vpternlogq $0x96, %xmm20, %xmm7, %xmm27
        vmovdqa64  %xmm17, %xmm28
        vpternlogq $0x96, %xmm23, %xmm5, %xmm28
        vpternlogq $0x96, %xmm4, %xmm11, %xmm28
        vmovdqa64  %xmm21, %xmm29
        vpternlogq $0x96, %xmm2, %xmm14, %xmm29
        vpternlogq $0x96, %xmm8, %xmm15, %xmm29
        vprolq     $1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0
        vpternlogq $0x96, %xmm30, %xmm29, %xmm18
        vpternlogq $0x96, %xmm30, %xmm29, %xmm6
        vpternlogq $0x96, %xmm30, %xmm29, %xmm24
        vpternlogq $0x96, %xmm30, %xmm29, %xmm12
        vprolq     $1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm9
        vpternlogq $0x96, %xmm30, %xmm25, %xmm22
        vpternlogq $0x96, %xmm30, %xmm25, %xmm10
        vpternlogq $0x96, %xmm30, %xmm25, %xmm3
        vpternlogq $0x96, %xmm30, %xmm25, %xmm16
        vprolq     $1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm13
        vpternlogq $0x96, %xmm30, %xmm26, %xmm1
        vpternlogq $0x96, %xmm30, %xmm26, %xmm19
        vpternlogq $0x96, %xmm30, %xmm26, %xmm7
        vpternlogq $0x96, %xmm30, %xmm26, %xmm20
        vprolq     $1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm17
        vpternlogq $0x96, %xmm30, %xmm27, %xmm5
        vpternlogq $0x96, %xmm30, %xmm27, %xmm23
        vpternlogq $0x96, %xmm30, %xmm27, %xmm11
        vpternlogq $0x96, %xmm30, %xmm27, %xmm4
        vprolq     $1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm21
        vpternlogq $0x96, %xmm30, %xmm28, %xmm14
        vpternlogq $0x96, %xmm30, %xmm28, %xmm2
        vpternlogq $0x96, %xmm30, %xmm28, %xmm15
        vpternlogq $0x96, %xmm30, %xmm28, %xmm8

// rho

        vprolq     $36, %xmm18, %xmm18
        vprolq     $3, %xmm6, %xmm6
        vprolq     $41, %xmm24, %xmm24
        vprolq     $18, %xmm12, %xmm12
        vprolq     $1, %xmm9, %xmm9
        vprolq     $44, %xmm22, %xmm22
        vprolq     $10, %xmm10, %xmm10
        vprolq     $45, %xmm3, %xmm3
        vprolq     $2, %xmm16, %xmm16
        vprolq     $62, %xmm13, %xmm13
        vprolq     $6, %xmm1, %xmm1
        vprolq     $43, %xmm19, %xmm19
        vprolq     $15, %xmm7, %xmm7
        vprolq     $61, %xmm20, %xmm20
        vprolq     $28, %xmm17, %xmm17
        vprolq     $55, %xmm5, %xmm5
        vprolq     $25, %xmm23, %xmm23
        vprolq     $21, %xmm11, %xmm11
        vprolq     $56, %xmm4, %xmm4
        vprolq     $27, %xmm21, %xmm21
        vprolq     $20, %xmm14, %xmm14
        vprolq     $39, %xmm2, %xmm2
        vprolq     $8, %xmm15, %xmm15
        vprolq     $14, %xmm8, %xmm8

// pi (renaming the registers), chi and iota

        vmovdqa64  %xmm0, %xmm30
        vmovdqa64  %xmm22, %xmm31
        vpternlogq $0xd2, %xmm19, %xmm22, %xmm0
        vpxorq     16(%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm11, %xmm19, %xmm22
        vpternlogq $0xd2, %xmm8, %xmm11, %xmm19
        vpternlogq $0xd2, %xmm30, %xmm8, %xmm11
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm8
        vmovdqa64  %xmm17, %xmm30
        vmovdqa64  %xmm14, %xmm31
        vpternlogq $0xd2, %xmm6, %xmm14, %xmm17
        vpternlogq $0xd2, %xmm3, %xmm6, %xmm14
        vpternlogq $0xd2, %xmm20, %xmm3, %xmm6
        vpternlogq $0xd2, %xmm30, %xmm20, %xmm3
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm20
        vmovdqa64  %xmm9, %xmm30
        vmovdqa64  %xmm1, %xmm31
        vpternlogq $0xd2, %xmm23, %xmm1, %xmm9
        vpternlogq $0xd2, %xmm15, %xmm23, %xmm1
        vpternlogq $0xd2, %xmm12, %xmm15, %xmm23
        vpternlogq $0xd2, %xmm30, %xmm12, %xmm15
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm12
        vmovdqa64  %xmm21, %xmm30
        vmovdqa64  %xmm18, %xmm31
        vpternlogq $0xd2, %xmm10, %xmm18, %xmm21
        vpternlogq $0xd2, %xmm7, %xmm10, %xmm18
        vpternlogq $0xd2, %xmm4, %xmm7, %xmm10
        vpternlogq $0xd2, %xmm30, %xmm4, %xmm7
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm4
        vmovdqa64  %xmm13, %xmm30
        vmovdqa64  %xmm5, %xmm31
        vpternlogq $0xd2, %xmm2, %xmm5, %xmm13
        vpternlogq $0xd2, %xmm24, %xmm2, %xmm5
        vpternlogq $0xd2, %xmm16, %xmm24, %xmm2
        vpternlogq $0xd2, %xmm30, %xmm16, %xmm24
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm16

// Round 4 of 4: theta

        vmovdqa64  %xmm0, %xmm25
        vpternlogq $0x96, %xmm9, %xmm17, %xmm25
        vpternlogq $0x96, %xmm13, %xmm21, %xmm25
        vmovdqa64  %xmm22, %xmm26
        vpternlogq $0x96, %xmm1, %xmm14, %xmm26
        vpternlogq $0x96, %xmm5, %xmm18, %xmm26
        vmovdqa64  %xmm19, %xmm27
        vpternlogq $0x96, %xmm23, %xmm6, %xmm27
        vpternlogq $0x96, %xmm2, %xmm10, %xmm27
        vmovdqa64  %xmm11, %xmm28
        vpternlogq $0x96, %xmm15, %xmm3, %xmm28
        vpternlogq $0x96, %xmm24, %xmm7, %xmm28
        vmovdqa64  %xmm8, %xmm29
        vpternlogq $0x96, %xmm12, %xmm20, %xmm29
        vpternlogq $0x96, %xmm16, %xmm4, %xmm29
        vprolq     $1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0
        vpternlogq $0x96, %xmm30, %xmm29, %xmm17
        vpternlogq $0x96, %xmm30, %xmm29, %xmm9
        vpternlogq $0x96, %xmm30, %xmm29, %xmm21
        vpternlogq $0x96, %xmm30, %xmm29, %xmm13
        vprolq     $1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm22
        vpternlogq $0x96, %xmm30, %xmm25, %xmm14
        vpternlogq $0x96, %xmm30, %xmm25, %xmm1
        vpternlogq $0x96, %xmm30, %xmm25, %xmm18
        vpternlogq $0x96, %xmm30, %xmm25, %xmm5
        vprolq     $1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm19
        vpternlogq $0x96, %xmm30, %xmm26, %xmm6
        vpternlogq $0x96, %xmm30, %xmm26, %xmm23
        vpternlogq $0x96, %xmm30, %xmm26, %xmm10
        vpternlogq $0x96, %xmm30, %xmm26, %xmm2
        vprolq     $1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm11
        vpternlogq $0x96, %xmm30, %xmm27, %xmm3
        vpternlogq $0x96, %xmm30, %xmm27, %xmm15
        vpternlogq $0x96, %xmm30, %xmm27, %xmm7
        vpternlogq $0x96, %xmm30, %xmm27, %xmm24
        vprolq     $1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm8
        vpternlogq $0x96, %xmm30, %xmm28, %xmm20
        vpternlogq $0x96, %xmm30, %xmm28, %xmm12
        vpternlogq $0x96, %xmm30, %xmm28, %xmm4
        vpternlogq $0x96, %xmm30, %xmm28, %xmm16

// rho

        vprolq     $36, %xmm17, %xmm17
        vprolq     $3, %xmm9, %xmm9
        vprolq     $41, %xmm21, %xmm21
        vprolq     $18, %xmm13, %xmm13
        vprolq     $1, %xmm22, %xmm22
        vprolq     $44, %xmm14, %xmm14
        vprolq     $10, %xmm1, %xmm1
        vprolq     $45, %xmm18, %xmm18
        vprolq     $2, %xmm5, %xmm5
        vprolq     $62, %xmm19, %xmm19
        vprolq     $6, %xmm6, %xmm6
        vprolq     $43, %xmm23, %xmm23
        vprolq     $15, %xmm10, %xmm10
        vprolq     $61, %xmm2, %xmm2
        vprolq     $28, %xmm11, %xmm11
        vprolq     $55, %xmm3, %xmm3
        vprolq     $25, %xmm15, %xmm15
        vprolq     $21, %xmm7, %xmm7
        vprolq     $56, %xmm24, %xmm24
        vprolq     $27, %xmm8, %xmm8
        vprolq     $20, %xmm20, %xmm20
        vprolq     $39, %xmm12, %xmm12
        vprolq     $8, %xmm4, %xmm4
        vprolq     $14, %xmm16, %xmm16

// pi (renaming the registers), chi and iota

        vmovdqa64  %xmm0, %xmm30
        vmovdqa64  %xmm14, %xmm31
        vpternlogq $0xd2, %xmm23, %xmm14, %xmm0
        vpxorq     24(%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm7, %xmm23, %xmm14
        vpternlogq $0xd2, %xmm16, %xmm7, %xmm23
        vpternlogq $0xd2, %xmm30, %xmm16, %xmm7
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm16
        vmovdqa64  %xmm11, %xmm30
        vmovdqa64  %xmm20, %xmm31
        vpternlogq $0xd2, %xmm9, %xmm20, %xmm11
        vpternlogq $0xd2, %xmm18, %xmm9, %xmm20
        vpternlogq $0xd2, %xmm2, %xmm18, %xmm9
        vpternlogq $0xd2, %xmm30, %xmm2, %xmm18
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm2
        vmovdqa64  %xmm22, %xmm30
        vmovdqa64  %xmm6, %xmm31
        vpternlogq $0xd2, %xmm15, %xmm6, %xmm22
        vpternlogq $0xd2, %xmm4, %xmm15, %xmm6
        vpternlogq $0xd2, %xmm13, %xmm4, %xmm15
        vpternlogq $0xd2, %xmm30, %xmm13, %xmm4
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm13
        vmovdqa64  %xmm8, %xmm30
        vmovdqa64  %xmm17, %xmm31
        vpternlogq $0xd2, %xmm1, %xmm17, %xmm8
        vpternlogq $0xd2, %xmm10, %xmm1, %xmm17
        vpternlogq $0xd2, %xmm24, %xmm10, %xmm1
        vpternlogq $0xd2, %xmm30, %xmm24, %xmm10
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm24
        vmovdqa64  %xmm19, %xmm30
        vmovdqa64  %xmm3, %xmm31
        vpternlogq $0xd2, %xmm12, %xmm3, %xmm19
        vpternlogq $0xd2, %xmm21, %xmm12, %xmm3
        vpternlogq $0xd2, %xmm5, %xmm21, %xmm12
        vpternlogq $0xd2, %xmm30, %xmm5, %xmm21
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm5

// Restore lane i to register i

        vmovdqa64  %xmm1, %xmm30
        vmovdqa    %xmm14, %xmm1
        vmovdqa    %xmm13, %xmm14
        vmovdqa    %xmm4, %xmm13
        vmovdqa64  %xmm16, %xmm4
        vmovdqa64  %xmm17, %xmm16
        vmovdqa64  %xmm30, %xmm17
        vmovdqa64  %xmm2, %xmm30
        vmovdqa64  %xmm23, %xmm2
        vmovdqa64  %xmm21, %xmm23
        vmovdqa64  %xmm3, %xmm21
        vmovdqa    %xmm7, %xmm3
        vmovdqa    %xmm9, %xmm7
        vmovdqa64  %xmm30, %xmm9
        vmovdqa64  %xmm5, %xmm30
        vmovdqa    %xmm11, %xmm5
        vmovdqa    %xmm6, %xmm11
        vmovdqa64  %xmm20, %xmm6
        vmovdqa64  %xmm19, %xmm20
        vmovdqa64  %xmm24, %xmm19
        vmovdqa64  %xmm30, %xmm24
        vmovdqa64  %xmm8, %xmm30
        vmovdqa64  %xmm18, %xmm8
        vmovdqa64  %xmm10, %xmm18
        vmovdqa64  %xmm22, %xmm10
        vmovdqa64  %xmm12, %xmm22
        vmovdqa    %xmm15, %xmm12
        vmovdqa64  %xmm30, %xmm15

        add        $32, %rsi
        cmp        %rax, %rsi
        jne        mlk_keccak_f1600_x1_avx512_loop

// Store the state

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
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x47,0x10 // vmovq %xmm16, 128(%rdi)
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x4f,0x11 // vmovq %xmm17, 136(%rdi)
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x57,0x12 // vmovq %xmm18, 144(%rdi)
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x5f,0x13 // vmovq %xmm19, 152(%rdi)
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x67,0x14 // vmovq %xmm20, 160(%rdi)
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x6f,0x15 // vmovq %xmm21, 168(%rdi)
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x77,0x16 // vmovq %xmm22, 176(%rdi)
        .byte 0x62,0xe1,0xfd,0x08,0x7e,0x7f,0x17 // vmovq %xmm23, 184(%rdi)
        .byte 0x62,0x61,0xfd,0x08,0x7e,0x47,0x18 // vmovq %xmm24, 192(%rdi)

        vzeroupper
        ret

/* simpasm: footer-start */
#endif /* MLK_SYS_X86_64_AVX512 && MLK_FIPS202_X86_64_NEED_X1_AVX512 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
