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

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_avx512_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_avx512_asm)

// Transpose the four states into ymm0..ymm24, four lanes at a time, and
// lane 24 by itself

        vmovdqu64  (%rdi), %ymm25
        vmovdqu64  200(%rdi), %ymm26
        vmovdqu64  400(%rdi), %ymm27
        vmovdqu64  600(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29
        vpunpckhqdq %ymm26, %ymm25, %ymm30
        vpunpcklqdq %ymm28, %ymm27, %ymm31
        vpunpckhqdq %ymm28, %ymm27, %ymm25
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm0
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm1
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm2
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm3
        vmovdqu64  32(%rdi), %ymm25
        vmovdqu64  232(%rdi), %ymm26
        vmovdqu64  432(%rdi), %ymm27
        vmovdqu64  632(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29
        vpunpckhqdq %ymm26, %ymm25, %ymm30
        vpunpcklqdq %ymm28, %ymm27, %ymm31
        vpunpckhqdq %ymm28, %ymm27, %ymm25
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm4
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm5
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm6
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm7
        vmovdqu64  64(%rdi), %ymm25
        vmovdqu64  264(%rdi), %ymm26
        vmovdqu64  464(%rdi), %ymm27
        vmovdqu64  664(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29
        vpunpckhqdq %ymm26, %ymm25, %ymm30
        vpunpcklqdq %ymm28, %ymm27, %ymm31
        vpunpckhqdq %ymm28, %ymm27, %ymm25
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm8
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm9
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm10
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm11
        vmovdqu64  96(%rdi), %ymm25
        vmovdqu64  296(%rdi), %ymm26
        vmovdqu64  496(%rdi), %ymm27
        vmovdqu64  696(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29
        vpunpckhqdq %ymm26, %ymm25, %ymm30
        vpunpcklqdq %ymm28, %ymm27, %ymm31
        vpunpckhqdq %ymm28, %ymm27, %ymm25
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm12
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm13
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm14
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm15
        vmovdqu64  128(%rdi), %ymm25
        vmovdqu64  328(%rdi), %ymm26
        vmovdqu64  528(%rdi), %ymm27
        vmovdqu64  728(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29
        vpunpckhqdq %ymm26, %ymm25, %ymm30
        vpunpcklqdq %ymm28, %ymm27, %ymm31
        vpunpckhqdq %ymm28, %ymm27, %ymm25
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm16
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm17
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm18
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm19
        vmovdqu64  160(%rdi), %ymm25
        vmovdqu64  360(%rdi), %ymm26
        vmovdqu64  560(%rdi), %ymm27
        vmovdqu64  760(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29
        vpunpckhqdq %ymm26, %ymm25, %ymm30
        vpunpcklqdq %ymm28, %ymm27, %ymm31
        vpunpckhqdq %ymm28, %ymm27, %ymm25
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm20
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm21
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm22
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm23
        // The loads and stores of the lanes in xmm16 and up are written
        // as bytes: for vmovq with an EVEX-only register, GNU as and
        // clang choose different (equivalent) opcodes, 66 0F 6E/7E and
        // F3 0F 7E/66 0F D6, and no syntax selects one. These are the
        // bytes that GNU as assembles.
        .byte 0x62,0x61,0xfd,0x08,0x6e,0x47,0x18 // vmovq 192(%rdi), %xmm24
        vpinsrq    $1, 392(%rdi), %xmm24, %xmm24
        .byte 0x62,0x61,0xfd,0x08,0x6e,0x4f,0x4a // vmovq 592(%rdi), %xmm25
        vpinsrq    $1, 792(%rdi), %xmm25, %xmm25
        vinserti32x4 $1, %xmm25, %ymm24, %ymm24

// The 24 rounds, four at a time

        lea        192(%rsi), %rax
mlk_keccak_f1600_x4_avx512_loop:

// Round 1 of 4: theta

        vmovdqa64  %ymm0, %ymm25
        vpternlogq $0x96, %ymm10, %ymm5, %ymm25
        vpternlogq $0x96, %ymm20, %ymm15, %ymm25
        vmovdqa64  %ymm1, %ymm26
        vpternlogq $0x96, %ymm11, %ymm6, %ymm26
        vpternlogq $0x96, %ymm21, %ymm16, %ymm26
        vmovdqa64  %ymm2, %ymm27
        vpternlogq $0x96, %ymm12, %ymm7, %ymm27
        vpternlogq $0x96, %ymm22, %ymm17, %ymm27
        vmovdqa64  %ymm3, %ymm28
        vpternlogq $0x96, %ymm13, %ymm8, %ymm28
        vpternlogq $0x96, %ymm23, %ymm18, %ymm28
        vmovdqa64  %ymm4, %ymm29
        vpternlogq $0x96, %ymm14, %ymm9, %ymm29
        vpternlogq $0x96, %ymm24, %ymm19, %ymm29
        vprolq     $1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0
        vpternlogq $0x96, %ymm30, %ymm29, %ymm5
        vpternlogq $0x96, %ymm30, %ymm29, %ymm10
        vpternlogq $0x96, %ymm30, %ymm29, %ymm15
        vpternlogq $0x96, %ymm30, %ymm29, %ymm20
        vprolq     $1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm1
        vpternlogq $0x96, %ymm30, %ymm25, %ymm6
        vpternlogq $0x96, %ymm30, %ymm25, %ymm11
        vpternlogq $0x96, %ymm30, %ymm25, %ymm16
        vpternlogq $0x96, %ymm30, %ymm25, %ymm21
        vprolq     $1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm2
        vpternlogq $0x96, %ymm30, %ymm26, %ymm7
        vpternlogq $0x96, %ymm30, %ymm26, %ymm12
        vpternlogq $0x96, %ymm30, %ymm26, %ymm17
        vpternlogq $0x96, %ymm30, %ymm26, %ymm22
        vprolq     $1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm3
        vpternlogq $0x96, %ymm30, %ymm27, %ymm8
        vpternlogq $0x96, %ymm30, %ymm27, %ymm13
        vpternlogq $0x96, %ymm30, %ymm27, %ymm18
        vpternlogq $0x96, %ymm30, %ymm27, %ymm23
        vprolq     $1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm4
        vpternlogq $0x96, %ymm30, %ymm28, %ymm9
        vpternlogq $0x96, %ymm30, %ymm28, %ymm14
        vpternlogq $0x96, %ymm30, %ymm28, %ymm19
        vpternlogq $0x96, %ymm30, %ymm28, %ymm24

// rho

        vprolq     $36, %ymm5, %ymm5
        vprolq     $3, %ymm10, %ymm10
        vprolq     $41, %ymm15, %ymm15
        vprolq     $18, %ymm20, %ymm20
        vprolq     $1, %ymm1, %ymm1
        vprolq     $44, %ymm6, %ymm6
        vprolq     $10, %ymm11, %ymm11
        vprolq     $45, %ymm16, %ymm16
        vprolq     $2, %ymm21, %ymm21
        vprolq     $62, %ymm2, %ymm2
        vprolq     $6, %ymm7, %ymm7
        vprolq     $43, %ymm12, %ymm12
        vprolq     $15, %ymm17, %ymm17
        vprolq     $61, %ymm22, %ymm22
        vprolq     $28, %ymm3, %ymm3
        vprolq     $55, %ymm8, %ymm8
        vprolq     $25, %ymm13, %ymm13
        vprolq     $21, %ymm18, %ymm18
        vprolq     $56, %ymm23, %ymm23
        vprolq     $27, %ymm4, %ymm4
        vprolq     $20, %ymm9, %ymm9
        vprolq     $39, %ymm14, %ymm14
        vprolq     $8, %ymm19, %ymm19
        vprolq     $14, %ymm24, %ymm24

// pi (renaming the registers), chi and iota

        vmovdqa64  %ymm0, %ymm30
        vmovdqa64  %ymm6, %ymm31
        vpternlogq $0xd2, %ymm12, %ymm6, %ymm0
        vpxorq     (%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm18, %ymm12, %ymm6
        vpternlogq $0xd2, %ymm24, %ymm18, %ymm12
        vpternlogq $0xd2, %ymm30, %ymm24, %ymm18
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm24
        vmovdqa64  %ymm3, %ymm30
        vmovdqa64  %ymm9, %ymm31
        vpternlogq $0xd2, %ymm10, %ymm9, %ymm3
        vpternlogq $0xd2, %ymm16, %ymm10, %ymm9
        vpternlogq $0xd2, %ymm22, %ymm16, %ymm10
        vpternlogq $0xd2, %ymm30, %ymm22, %ymm16
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm22
        vmovdqa64  %ymm1, %ymm30
        vmovdqa64  %ymm7, %ymm31
        vpternlogq $0xd2, %ymm13, %ymm7, %ymm1
        vpternlogq $0xd2, %ymm19, %ymm13, %ymm7
        vpternlogq $0xd2, %ymm20, %ymm19, %ymm13
        vpternlogq $0xd2, %ymm30, %ymm20, %ymm19
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm20
        vmovdqa64  %ymm4, %ymm30
        vmovdqa64  %ymm5, %ymm31
        vpternlogq $0xd2, %ymm11, %ymm5, %ymm4
        vpternlogq $0xd2, %ymm17, %ymm11, %ymm5
        vpternlogq $0xd2, %ymm23, %ymm17, %ymm11
        vpternlogq $0xd2, %ymm30, %ymm23, %ymm17
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm23
        vmovdqa64  %ymm2, %ymm30
        vmovdqa64  %ymm8, %ymm31
        vpternlogq $0xd2, %ymm14, %ymm8, %ymm2
        vpternlogq $0xd2, %ymm15, %ymm14, %ymm8
        vpternlogq $0xd2, %ymm21, %ymm15, %ymm14
        vpternlogq $0xd2, %ymm30, %ymm21, %ymm15
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm21

// Round 2 of 4: theta

        vmovdqa64  %ymm0, %ymm25
        vpternlogq $0x96, %ymm1, %ymm3, %ymm25
        vpternlogq $0x96, %ymm2, %ymm4, %ymm25
        vmovdqa64  %ymm6, %ymm26
        vpternlogq $0x96, %ymm7, %ymm9, %ymm26
        vpternlogq $0x96, %ymm8, %ymm5, %ymm26
        vmovdqa64  %ymm12, %ymm27
        vpternlogq $0x96, %ymm13, %ymm10, %ymm27
        vpternlogq $0x96, %ymm14, %ymm11, %ymm27
        vmovdqa64  %ymm18, %ymm28
        vpternlogq $0x96, %ymm19, %ymm16, %ymm28
        vpternlogq $0x96, %ymm15, %ymm17, %ymm28
        vmovdqa64  %ymm24, %ymm29
        vpternlogq $0x96, %ymm20, %ymm22, %ymm29
        vpternlogq $0x96, %ymm21, %ymm23, %ymm29
        vprolq     $1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0
        vpternlogq $0x96, %ymm30, %ymm29, %ymm3
        vpternlogq $0x96, %ymm30, %ymm29, %ymm1
        vpternlogq $0x96, %ymm30, %ymm29, %ymm4
        vpternlogq $0x96, %ymm30, %ymm29, %ymm2
        vprolq     $1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm6
        vpternlogq $0x96, %ymm30, %ymm25, %ymm9
        vpternlogq $0x96, %ymm30, %ymm25, %ymm7
        vpternlogq $0x96, %ymm30, %ymm25, %ymm5
        vpternlogq $0x96, %ymm30, %ymm25, %ymm8
        vprolq     $1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm12
        vpternlogq $0x96, %ymm30, %ymm26, %ymm10
        vpternlogq $0x96, %ymm30, %ymm26, %ymm13
        vpternlogq $0x96, %ymm30, %ymm26, %ymm11
        vpternlogq $0x96, %ymm30, %ymm26, %ymm14
        vprolq     $1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm18
        vpternlogq $0x96, %ymm30, %ymm27, %ymm16
        vpternlogq $0x96, %ymm30, %ymm27, %ymm19
        vpternlogq $0x96, %ymm30, %ymm27, %ymm17
        vpternlogq $0x96, %ymm30, %ymm27, %ymm15
        vprolq     $1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm24
        vpternlogq $0x96, %ymm30, %ymm28, %ymm22
        vpternlogq $0x96, %ymm30, %ymm28, %ymm20
        vpternlogq $0x96, %ymm30, %ymm28, %ymm23
        vpternlogq $0x96, %ymm30, %ymm28, %ymm21

// rho

        vprolq     $36, %ymm3, %ymm3
        vprolq     $3, %ymm1, %ymm1
        vprolq     $41, %ymm4, %ymm4
        vprolq     $18, %ymm2, %ymm2
        vprolq     $1, %ymm6, %ymm6
        vprolq     $44, %ymm9, %ymm9
        vprolq     $10, %ymm7, %ymm7
        vprolq     $45, %ymm5, %ymm5
        vprolq     $2, %ymm8, %ymm8
        vprolq     $62, %ymm12, %ymm12
        vprolq     $6, %ymm10, %ymm10
        vprolq     $43, %ymm13, %ymm13
        vprolq     $15, %ymm11, %ymm11
        vprolq     $61, %ymm14, %ymm14
        vprolq     $28, %ymm18, %ymm18
        vprolq     $55, %ymm16, %ymm16
        vprolq     $25, %ymm19, %ymm19
        vprolq     $21, %ymm17, %ymm17
        vprolq     $56, %ymm15, %ymm15
        vprolq     $27, %ymm24, %ymm24
        vprolq     $20, %ymm22, %ymm22
        vprolq     $39, %ymm20, %ymm20
        vprolq     $8, %ymm23, %ymm23
        vprolq     $14, %ymm21, %ymm21

// pi (renaming the registers), chi and iota

        vmovdqa64  %ymm0, %ymm30
        vmovdqa64  %ymm9, %ymm31
        vpternlogq $0xd2, %ymm13, %ymm9, %ymm0
        vpxorq     8(%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm17, %ymm13, %ymm9
        vpternlogq $0xd2, %ymm21, %ymm17, %ymm13
        vpternlogq $0xd2, %ymm30, %ymm21, %ymm17
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm21
        vmovdqa64  %ymm18, %ymm30
        vmovdqa64  %ymm22, %ymm31
        vpternlogq $0xd2, %ymm1, %ymm22, %ymm18
        vpternlogq $0xd2, %ymm5, %ymm1, %ymm22
        vpternlogq $0xd2, %ymm14, %ymm5, %ymm1
        vpternlogq $0xd2, %ymm30, %ymm14, %ymm5
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm14
        vmovdqa64  %ymm6, %ymm30
        vmovdqa64  %ymm10, %ymm31
        vpternlogq $0xd2, %ymm19, %ymm10, %ymm6
        vpternlogq $0xd2, %ymm23, %ymm19, %ymm10
        vpternlogq $0xd2, %ymm2, %ymm23, %ymm19
        vpternlogq $0xd2, %ymm30, %ymm2, %ymm23
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm2
        vmovdqa64  %ymm24, %ymm30
        vmovdqa64  %ymm3, %ymm31
        vpternlogq $0xd2, %ymm7, %ymm3, %ymm24
        vpternlogq $0xd2, %ymm11, %ymm7, %ymm3
        vpternlogq $0xd2, %ymm15, %ymm11, %ymm7
        vpternlogq $0xd2, %ymm30, %ymm15, %ymm11
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm15
        vmovdqa64  %ymm12, %ymm30
        vmovdqa64  %ymm16, %ymm31
        vpternlogq $0xd2, %ymm20, %ymm16, %ymm12
        vpternlogq $0xd2, %ymm4, %ymm20, %ymm16
        vpternlogq $0xd2, %ymm8, %ymm4, %ymm20
        vpternlogq $0xd2, %ymm30, %ymm8, %ymm4
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm8

// Round 3 of 4: theta

        vmovdqa64  %ymm0, %ymm25
        vpternlogq $0x96, %ymm6, %ymm18, %ymm25
        vpternlogq $0x96, %ymm12, %ymm24, %ymm25
        vmovdqa64  %ymm9, %ymm26
        vpternlogq $0x96, %ymm10, %ymm22, %ymm26
        vpternlogq $0x96, %ymm16, %ymm3, %ymm26
        vmovdqa64  %ymm13, %ymm27
        vpternlogq $0x96, %ymm19, %ymm1, %ymm27
        vpternlogq $0x96, %ymm20, %ymm7, %ymm27
        vmovdqa64  %ymm17, %ymm28
        vpternlogq $0x96, %ymm23, %ymm5, %ymm28
        vpternlogq $0x96, %ymm4, %ymm11, %ymm28
        vmovdqa64  %ymm21, %ymm29
        vpternlogq $0x96, %ymm2, %ymm14, %ymm29
        vpternlogq $0x96, %ymm8, %ymm15, %ymm29
        vprolq     $1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0
        vpternlogq $0x96, %ymm30, %ymm29, %ymm18
        vpternlogq $0x96, %ymm30, %ymm29, %ymm6
        vpternlogq $0x96, %ymm30, %ymm29, %ymm24
        vpternlogq $0x96, %ymm30, %ymm29, %ymm12
        vprolq     $1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm9
        vpternlogq $0x96, %ymm30, %ymm25, %ymm22
        vpternlogq $0x96, %ymm30, %ymm25, %ymm10
        vpternlogq $0x96, %ymm30, %ymm25, %ymm3
        vpternlogq $0x96, %ymm30, %ymm25, %ymm16
        vprolq     $1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm13
        vpternlogq $0x96, %ymm30, %ymm26, %ymm1
        vpternlogq $0x96, %ymm30, %ymm26, %ymm19
        vpternlogq $0x96, %ymm30, %ymm26, %ymm7
        vpternlogq $0x96, %ymm30, %ymm26, %ymm20
        vprolq     $1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm17
        vpternlogq $0x96, %ymm30, %ymm27, %ymm5
        vpternlogq $0x96, %ymm30, %ymm27, %ymm23
        vpternlogq $0x96, %ymm30, %ymm27, %ymm11
        vpternlogq $0x96, %ymm30, %ymm27, %ymm4
        vprolq     $1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm21
        vpternlogq $0x96, %ymm30, %ymm28, %ymm14
        vpternlogq $0x96, %ymm30, %ymm28, %ymm2
        vpternlogq $0x96, %ymm30, %ymm28, %ymm15
        vpternlogq $0x96, %ymm30, %ymm28, %ymm8

// rho

        vprolq     $36, %ymm18, %ymm18
        vprolq     $3, %ymm6, %ymm6
        vprolq     $41, %ymm24, %ymm24
        vprolq     $18, %ymm12, %ymm12
        vprolq     $1, %ymm9, %ymm9
        vprolq     $44, %ymm22, %ymm22
        vprolq     $10, %ymm10, %ymm10
        vprolq     $45, %ymm3, %ymm3
        vprolq     $2, %ymm16, %ymm16
        vprolq     $62, %ymm13, %ymm13
        vprolq     $6, %ymm1, %ymm1
        vprolq     $43, %ymm19, %ymm19
        vprolq     $15, %ymm7, %ymm7
        vprolq     $61, %ymm20, %ymm20
        vprolq     $28, %ymm17, %ymm17
        vprolq     $55, %ymm5, %ymm5
        vprolq     $25, %ymm23, %ymm23
        vprolq     $21, %ymm11, %ymm11
        vprolq     $56, %ymm4, %ymm4
        vprolq     $27, %ymm21, %ymm21
        vprolq     $20, %ymm14, %ymm14
        vprolq     $39, %ymm2, %ymm2
        vprolq     $8, %ymm15, %ymm15
        vprolq     $14, %ymm8, %ymm8

// pi (renaming the registers), chi and iota

        vmovdqa64  %ymm0, %ymm30
        vmovdqa64  %ymm22, %ymm31
        vpternlogq $0xd2, %ymm19, %ymm22, %ymm0
        vpxorq     16(%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm11, %ymm19, %ymm22
        vpternlogq $0xd2, %ymm8, %ymm11, %ymm19
        vpternlogq $0xd2, %ymm30, %ymm8, %ymm11
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm8
        vmovdqa64  %ymm17, %ymm30
        vmovdqa64  %ymm14, %ymm31
        vpternlogq $0xd2, %ymm6, %ymm14, %ymm17
        vpternlogq $0xd2, %ymm3, %ymm6, %ymm14
        vpternlogq $0xd2, %ymm20, %ymm3, %ymm6
        vpternlogq $0xd2, %ymm30, %ymm20, %ymm3
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm20
        vmovdqa64  %ymm9, %ymm30
        vmovdqa64  %ymm1, %ymm31
        vpternlogq $0xd2, %ymm23, %ymm1, %ymm9
        vpternlogq $0xd2, %ymm15, %ymm23, %ymm1
        vpternlogq $0xd2, %ymm12, %ymm15, %ymm23
        vpternlogq $0xd2, %ymm30, %ymm12, %ymm15
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm12
        vmovdqa64  %ymm21, %ymm30
        vmovdqa64  %ymm18, %ymm31
        vpternlogq $0xd2, %ymm10, %ymm18, %ymm21
        vpternlogq $0xd2, %ymm7, %ymm10, %ymm18
        vpternlogq $0xd2, %ymm4, %ymm7, %ymm10
        vpternlogq $0xd2, %ymm30, %ymm4, %ymm7
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm4
        vmovdqa64  %ymm13, %ymm30
        vmovdqa64  %ymm5, %ymm31
        vpternlogq $0xd2, %ymm2, %ymm5, %ymm13
        vpternlogq $0xd2, %ymm24, %ymm2, %ymm5
        vpternlogq $0xd2, %ymm16, %ymm24, %ymm2
        vpternlogq $0xd2, %ymm30, %ymm16, %ymm24
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm16

// Round 4 of 4: theta

        vmovdqa64  %ymm0, %ymm25
        vpternlogq $0x96, %ymm9, %ymm17, %ymm25
        vpternlogq $0x96, %ymm13, %ymm21, %ymm25
        vmovdqa64  %ymm22, %ymm26
        vpternlogq $0x96, %ymm1, %ymm14, %ymm26
        vpternlogq $0x96, %ymm5, %ymm18, %ymm26
        vmovdqa64  %ymm19, %ymm27
        vpternlogq $0x96, %ymm23, %ymm6, %ymm27
        vpternlogq $0x96, %ymm2, %ymm10, %ymm27
        vmovdqa64  %ymm11, %ymm28
        vpternlogq $0x96, %ymm15, %ymm3, %ymm28
        vpternlogq $0x96, %ymm24, %ymm7, %ymm28
        vmovdqa64  %ymm8, %ymm29
        vpternlogq $0x96, %ymm12, %ymm20, %ymm29
        vpternlogq $0x96, %ymm16, %ymm4, %ymm29
        vprolq     $1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0
        vpternlogq $0x96, %ymm30, %ymm29, %ymm17
        vpternlogq $0x96, %ymm30, %ymm29, %ymm9
        vpternlogq $0x96, %ymm30, %ymm29, %ymm21
        vpternlogq $0x96, %ymm30, %ymm29, %ymm13
        vprolq     $1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm22
        vpternlogq $0x96, %ymm30, %ymm25, %ymm14
        vpternlogq $0x96, %ymm30, %ymm25, %ymm1
        vpternlogq $0x96, %ymm30, %ymm25, %ymm18
        vpternlogq $0x96, %ymm30, %ymm25, %ymm5
        vprolq     $1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm19
        vpternlogq $0x96, %ymm30, %ymm26, %ymm6
        vpternlogq $0x96, %ymm30, %ymm26, %ymm23
        vpternlogq $0x96, %ymm30, %ymm26, %ymm10
        vpternlogq $0x96, %ymm30, %ymm26, %ymm2
        vprolq     $1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm11
        vpternlogq $0x96, %ymm30, %ymm27, %ymm3
        vpternlogq $0x96, %ymm30, %ymm27, %ymm15
        vpternlogq $0x96, %ymm30, %ymm27, %ymm7
        vpternlogq $0x96, %ymm30, %ymm27, %ymm24
        vprolq     $1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm8
        vpternlogq $0x96, %ymm30, %ymm28, %ymm20
        vpternlogq $0x96, %ymm30, %ymm28, %ymm12
        vpternlogq $0x96, %ymm30, %ymm28, %ymm4
        vpternlogq $0x96, %ymm30, %ymm28, %ymm16

// rho

        vprolq     $36, %ymm17, %ymm17
        vprolq     $3, %ymm9, %ymm9
        vprolq     $41, %ymm21, %ymm21
        vprolq     $18, %ymm13, %ymm13
        vprolq     $1, %ymm22, %ymm22
        vprolq     $44, %ymm14, %ymm14
        vprolq     $10, %ymm1, %ymm1
        vprolq     $45, %ymm18, %ymm18
        vprolq     $2, %ymm5, %ymm5
        vprolq     $62, %ymm19, %ymm19
        vprolq     $6, %ymm6, %ymm6
        vprolq     $43, %ymm23, %ymm23
        vprolq     $15, %ymm10, %ymm10
        vprolq     $61, %ymm2, %ymm2
        vprolq     $28, %ymm11, %ymm11
        vprolq     $55, %ymm3, %ymm3
        vprolq     $25, %ymm15, %ymm15
        vprolq     $21, %ymm7, %ymm7
        vprolq     $56, %ymm24, %ymm24
        vprolq     $27, %ymm8, %ymm8
        vprolq     $20, %ymm20, %ymm20
        vprolq     $39, %ymm12, %ymm12
        vprolq     $8, %ymm4, %ymm4
        vprolq     $14, %ymm16, %ymm16

// pi (renaming the registers), chi and iota

        vmovdqa64  %ymm0, %ymm30
        vmovdqa64  %ymm14, %ymm31
        vpternlogq $0xd2, %ymm23, %ymm14, %ymm0
        vpxorq     24(%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm7, %ymm23, %ymm14
        vpternlogq $0xd2, %ymm16, %ymm7, %ymm23
        vpternlogq $0xd2, %ymm30, %ymm16, %ymm7
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm16
        vmovdqa64  %ymm11, %ymm30
        vmovdqa64  %ymm20, %ymm31
        vpternlogq $0xd2, %ymm9, %ymm20, %ymm11
        vpternlogq $0xd2, %ymm18, %ymm9, %ymm20
        vpternlogq $0xd2, %ymm2, %ymm18, %ymm9
        vpternlogq $0xd2, %ymm30, %ymm2, %ymm18
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm2
        vmovdqa64  %ymm22, %ymm30
        vmovdqa64  %ymm6, %ymm31
        vpternlogq $0xd2, %ymm15, %ymm6, %ymm22
        vpternlogq $0xd2, %ymm4, %ymm15, %ymm6
        vpternlogq $0xd2, %ymm13, %ymm4, %ymm15
        vpternlogq $0xd2, %ymm30, %ymm13, %ymm4
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm13
        vmovdqa64  %ymm8, %ymm30
        vmovdqa64  %ymm17, %ymm31
        vpternlogq $0xd2, %ymm1, %ymm17, %ymm8
        vpternlogq $0xd2, %ymm10, %ymm1, %ymm17
        vpternlogq $0xd2, %ymm24, %ymm10, %ymm1
        vpternlogq $0xd2, %ymm30, %ymm24, %ymm10
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm24
        vmovdqa64  %ymm19, %ymm30
        vmovdqa64  %ymm3, %ymm31
        vpternlogq $0xd2, %ymm12, %ymm3, %ymm19
        vpternlogq $0xd2, %ymm21, %ymm12, %ymm3
        vpternlogq $0xd2, %ymm5, %ymm21, %ymm12
        vpternlogq $0xd2, %ymm30, %ymm5, %ymm21
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm5

// Restore lane i to register i

        vmovdqa64  %ymm1, %ymm30
        vmovdqa    %ymm14, %ymm1
        vmovdqa    %ymm13, %ymm14
        vmovdqa    %ymm4, %ymm13
        vmovdqa64  %ymm16, %ymm4
        vmovdqa64  %ymm17, %ymm16
        vmovdqa64  %ymm30, %ymm17
        vmovdqa64  %ymm2, %ymm30
        vmovdqa64  %ymm23, %ymm2
        vmovdqa64  %ymm21, %ymm23
        vmovdqa64  %ymm3, %ymm21
        vmovdqa    %ymm7, %ymm3
        vmovdqa    %ymm9, %ymm7
        vmovdqa64  %ymm30, %ymm9
        vmovdqa64  %ymm5, %ymm30
        vmovdqa    %ymm11, %ymm5
        vmovdqa    %ymm6, %ymm11
        vmovdqa64  %ymm20, %ymm6
        vmovdqa64  %ymm19, %ymm20
        vmovdqa64  %ymm24, %ymm19
        vmovdqa64  %ymm30, %ymm24
        vmovdqa64  %ymm8, %ymm30
        vmovdqa64  %ymm18, %ymm8
        vmovdqa64  %ymm10, %ymm18
        vmovdqa64  %ymm22, %ymm10
        vmovdqa64  %ymm12, %ymm22
        vmovdqa    %ymm15, %ymm12
        vmovdqa64  %ymm30, %ymm15

        add        $32, %rsi
        cmp        %rax, %rsi
        jne        mlk_keccak_f1600_x4_avx512_loop

// Transpose back and store the four states

        vpunpcklqdq %ymm1, %ymm0, %ymm25
        vpunpckhqdq %ymm1, %ymm0, %ymm26
        vpunpcklqdq %ymm3, %ymm2, %ymm27
        vpunpckhqdq %ymm3, %ymm2, %ymm28
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25
        vmovdqu64  %ymm29, (%rdi)
        vmovdqu64  %ymm30, 200(%rdi)
        vmovdqu64  %ymm31, 400(%rdi)
        vmovdqu64  %ymm25, 600(%rdi)
        vpunpcklqdq %ymm5, %ymm4, %ymm25
        vpunpckhqdq %ymm5, %ymm4, %ymm26
        vpunpcklqdq %ymm7, %ymm6, %ymm27
        vpunpckhqdq %ymm7, %ymm6, %ymm28
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25
        vmovdqu64  %ymm29, 32(%rdi)
        vmovdqu64  %ymm30, 232(%rdi)
        vmovdqu64  %ymm31, 432(%rdi)
        vmovdqu64  %ymm25, 632(%rdi)
        vpunpcklqdq %ymm9, %ymm8, %ymm25
        vpunpckhqdq %ymm9, %ymm8, %ymm26
        vpunpcklqdq %ymm11, %ymm10, %ymm27
        vpunpckhqdq %ymm11, %ymm10, %ymm28
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25
        vmovdqu64  %ymm29, 64(%rdi)
        vmovdqu64  %ymm30, 264(%rdi)
        vmovdqu64  %ymm31, 464(%rdi)
        vmovdqu64  %ymm25, 664(%rdi)
        vpunpcklqdq %ymm13, %ymm12, %ymm25
        vpunpckhqdq %ymm13, %ymm12, %ymm26
        vpunpcklqdq %ymm15, %ymm14, %ymm27
        vpunpckhqdq %ymm15, %ymm14, %ymm28
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25
        vmovdqu64  %ymm29, 96(%rdi)
        vmovdqu64  %ymm30, 296(%rdi)
        vmovdqu64  %ymm31, 496(%rdi)
        vmovdqu64  %ymm25, 696(%rdi)
        vpunpcklqdq %ymm17, %ymm16, %ymm25
        vpunpckhqdq %ymm17, %ymm16, %ymm26
        vpunpcklqdq %ymm19, %ymm18, %ymm27
        vpunpckhqdq %ymm19, %ymm18, %ymm28
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25
        vmovdqu64  %ymm29, 128(%rdi)
        vmovdqu64  %ymm30, 328(%rdi)
        vmovdqu64  %ymm31, 528(%rdi)
        vmovdqu64  %ymm25, 728(%rdi)
        vpunpcklqdq %ymm21, %ymm20, %ymm25
        vpunpckhqdq %ymm21, %ymm20, %ymm26
        vpunpcklqdq %ymm23, %ymm22, %ymm27
        vpunpckhqdq %ymm23, %ymm22, %ymm28
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25
        vmovdqu64  %ymm29, 160(%rdi)
        vmovdqu64  %ymm30, 360(%rdi)
        vmovdqu64  %ymm31, 560(%rdi)
        vmovdqu64  %ymm25, 760(%rdi)
        .byte 0x62,0x61,0xfd,0x08,0x7e,0x47,0x18 // vmovq %xmm24, 192(%rdi)
        vpextrq    $1, %xmm24, 392(%rdi)
        vextracti32x4 $1, %ymm24, %xmm25
        .byte 0x62,0x61,0xfd,0x08,0x7e,0x4f,0x4a // vmovq %xmm25, 592(%rdi)
        vpextrq    $1, %xmm25, 792(%rdi)

        vzeroupper
        ret

/* simpasm: footer-start */
#endif /* MLK_SYS_X86_64_AVX512 && MLK_FIPS202_X86_64_NEED_X4_AVX512 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
