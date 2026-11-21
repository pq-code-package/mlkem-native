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


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/x86_64/src/keccak_f1600_x1_avx512_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_avx512_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_avx512_asm)

        .cfi_startproc
        vmovq (%rdi), %xmm0
        vmovq 0x8(%rdi), %xmm1
        vmovq 0x10(%rdi), %xmm2
        vmovq 0x18(%rdi), %xmm3
        vmovq 0x20(%rdi), %xmm4
        vmovq 0x28(%rdi), %xmm5
        vmovq 0x30(%rdi), %xmm6
        vmovq 0x38(%rdi), %xmm7
        vmovq 0x40(%rdi), %xmm8
        vmovq 0x48(%rdi), %xmm9
        vmovq 0x50(%rdi), %xmm10
        vmovq 0x58(%rdi), %xmm11
        vmovq 0x60(%rdi), %xmm12
        vmovq 0x68(%rdi), %xmm13
        vmovq 0x70(%rdi), %xmm14
        vmovq 0x78(%rdi), %xmm15
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x47, 0x10 /* vmovq 0x80(%rdi), %xmm16 */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x4f, 0x11 /* vmovq 0x88(%rdi), %xmm17 */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x57, 0x12 /* vmovq 0x90(%rdi), %xmm18 */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x5f, 0x13 /* vmovq 0x98(%rdi), %xmm19 */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x67, 0x14 /* vmovq 0xa0(%rdi), %xmm20 */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x6f, 0x15 /* vmovq 0xa8(%rdi), %xmm21 */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x77, 0x16 /* vmovq 0xb0(%rdi), %xmm22 */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x6e, 0x7f, 0x17 /* vmovq 0xb8(%rdi), %xmm23 */
        .byte 0x62, 0x61, 0xfd, 0x08, 0x6e, 0x47, 0x18 /* vmovq 0xc0(%rdi), %xmm24 */
        leaq 0xc0(%rsi), %rax

Lmlk_keccak_f1600_x1_avx512_loop:
        vmovdqa64 %xmm0, %xmm25
        vpternlogq $0x96, %xmm10, %xmm5, %xmm25 # xmm25 = xmm25 ^ xmm5 ^ xmm10
        vpternlogq $0x96, %xmm20, %xmm15, %xmm25 # xmm25 = xmm25 ^ xmm15 ^ xmm20
        vmovdqa64 %xmm1, %xmm26
        vpternlogq $0x96, %xmm11, %xmm6, %xmm26 # xmm26 = xmm26 ^ xmm6 ^ xmm11
        vpternlogq $0x96, %xmm21, %xmm16, %xmm26 # xmm26 = xmm26 ^ xmm16 ^ xmm21
        vmovdqa64 %xmm2, %xmm27
        vpternlogq $0x96, %xmm12, %xmm7, %xmm27 # xmm27 = xmm27 ^ xmm7 ^ xmm12
        vpternlogq $0x96, %xmm22, %xmm17, %xmm27 # xmm27 = xmm27 ^ xmm17 ^ xmm22
        vmovdqa64 %xmm3, %xmm28
        vpternlogq $0x96, %xmm13, %xmm8, %xmm28 # xmm28 = xmm28 ^ xmm8 ^ xmm13
        vpternlogq $0x96, %xmm23, %xmm18, %xmm28 # xmm28 = xmm28 ^ xmm18 ^ xmm23
        vmovdqa64 %xmm4, %xmm29
        vpternlogq $0x96, %xmm14, %xmm9, %xmm29 # xmm29 = xmm29 ^ xmm9 ^ xmm14
        vpternlogq $0x96, %xmm24, %xmm19, %xmm29 # xmm29 = xmm29 ^ xmm19 ^ xmm24
        vprolq $0x1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0 # xmm0 = xmm0 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm5 # xmm5 = xmm5 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm10 # xmm10 = xmm10 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm15 # xmm15 = xmm15 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm20 # xmm20 = xmm20 ^ xmm29 ^ xmm30
        vprolq $0x1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm1 # xmm1 = xmm1 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm6 # xmm6 = xmm6 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm11 # xmm11 = xmm11 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm16 # xmm16 = xmm16 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm21 # xmm21 = xmm21 ^ xmm25 ^ xmm30
        vprolq $0x1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm2 # xmm2 = xmm2 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm7 # xmm7 = xmm7 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm12 # xmm12 = xmm12 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm17 # xmm17 = xmm17 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm22 # xmm22 = xmm22 ^ xmm26 ^ xmm30
        vprolq $0x1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm3 # xmm3 = xmm3 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm8 # xmm8 = xmm8 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm13 # xmm13 = xmm13 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm18 # xmm18 = xmm18 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm23 # xmm23 = xmm23 ^ xmm27 ^ xmm30
        vprolq $0x1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm4 # xmm4 = xmm4 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm9 # xmm9 = xmm9 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm14 # xmm14 = xmm14 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm19 # xmm19 = xmm19 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm24 # xmm24 = xmm24 ^ xmm28 ^ xmm30
        vprolq $0x24, %xmm5, %xmm5
        vprolq $0x3, %xmm10, %xmm10
        vprolq $0x29, %xmm15, %xmm15
        vprolq $0x12, %xmm20, %xmm20
        vprolq $0x1, %xmm1, %xmm1
        vprolq $0x2c, %xmm6, %xmm6
        vprolq $0xa, %xmm11, %xmm11
        vprolq $0x2d, %xmm16, %xmm16
        vprolq $0x2, %xmm21, %xmm21
        vprolq $0x3e, %xmm2, %xmm2
        vprolq $0x6, %xmm7, %xmm7
        vprolq $0x2b, %xmm12, %xmm12
        vprolq $0xf, %xmm17, %xmm17
        vprolq $0x3d, %xmm22, %xmm22
        vprolq $0x1c, %xmm3, %xmm3
        vprolq $0x37, %xmm8, %xmm8
        vprolq $0x19, %xmm13, %xmm13
        vprolq $0x15, %xmm18, %xmm18
        vprolq $0x38, %xmm23, %xmm23
        vprolq $0x1b, %xmm4, %xmm4
        vprolq $0x14, %xmm9, %xmm9
        vprolq $0x27, %xmm14, %xmm14
        vprolq $0x8, %xmm19, %xmm19
        vprolq $0xe, %xmm24, %xmm24
        vmovdqa64 %xmm0, %xmm30
        vmovdqa64 %xmm6, %xmm31
        vpternlogq $0xd2, %xmm12, %xmm6, %xmm0 # xmm0 = xmm0 ^ (xmm12 & ~xmm6)
        vpxorq (%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm18, %xmm12, %xmm6 # xmm6 = xmm6 ^ (xmm18 & ~xmm12)
        vpternlogq $0xd2, %xmm24, %xmm18, %xmm12 # xmm12 = xmm12 ^ (xmm24 & ~xmm18)
        vpternlogq $0xd2, %xmm30, %xmm24, %xmm18 # xmm18 = xmm18 ^ (xmm30 & ~xmm24)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm24 # xmm24 = xmm24 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm3, %xmm30
        vmovdqa64 %xmm9, %xmm31
        vpternlogq $0xd2, %xmm10, %xmm9, %xmm3 # xmm3 = xmm3 ^ (xmm10 & ~xmm9)
        vpternlogq $0xd2, %xmm16, %xmm10, %xmm9 # xmm9 = xmm9 ^ (xmm16 & ~xmm10)
        vpternlogq $0xd2, %xmm22, %xmm16, %xmm10 # xmm10 = xmm10 ^ (xmm22 & ~xmm16)
        vpternlogq $0xd2, %xmm30, %xmm22, %xmm16 # xmm16 = xmm16 ^ (xmm30 & ~xmm22)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm22 # xmm22 = xmm22 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm1, %xmm30
        vmovdqa64 %xmm7, %xmm31
        vpternlogq $0xd2, %xmm13, %xmm7, %xmm1 # xmm1 = xmm1 ^ (xmm13 & ~xmm7)
        vpternlogq $0xd2, %xmm19, %xmm13, %xmm7 # xmm7 = xmm7 ^ (xmm19 & ~xmm13)
        vpternlogq $0xd2, %xmm20, %xmm19, %xmm13 # xmm13 = xmm13 ^ (xmm20 & ~xmm19)
        vpternlogq $0xd2, %xmm30, %xmm20, %xmm19 # xmm19 = xmm19 ^ (xmm30 & ~xmm20)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm20 # xmm20 = xmm20 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm4, %xmm30
        vmovdqa64 %xmm5, %xmm31
        vpternlogq $0xd2, %xmm11, %xmm5, %xmm4 # xmm4 = xmm4 ^ (xmm11 & ~xmm5)
        vpternlogq $0xd2, %xmm17, %xmm11, %xmm5 # xmm5 = xmm5 ^ (xmm17 & ~xmm11)
        vpternlogq $0xd2, %xmm23, %xmm17, %xmm11 # xmm11 = xmm11 ^ (xmm23 & ~xmm17)
        vpternlogq $0xd2, %xmm30, %xmm23, %xmm17 # xmm17 = xmm17 ^ (xmm30 & ~xmm23)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm23 # xmm23 = xmm23 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm2, %xmm30
        vmovdqa64 %xmm8, %xmm31
        vpternlogq $0xd2, %xmm14, %xmm8, %xmm2 # xmm2 = xmm2 ^ (xmm14 & ~xmm8)
        vpternlogq $0xd2, %xmm15, %xmm14, %xmm8 # xmm8 = xmm8 ^ (xmm15 & ~xmm14)
        vpternlogq $0xd2, %xmm21, %xmm15, %xmm14 # xmm14 = xmm14 ^ (xmm21 & ~xmm15)
        vpternlogq $0xd2, %xmm30, %xmm21, %xmm15 # xmm15 = xmm15 ^ (xmm30 & ~xmm21)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm21 # xmm21 = xmm21 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm0, %xmm25
        vpternlogq $0x96, %xmm1, %xmm3, %xmm25 # xmm25 = xmm25 ^ xmm3 ^ xmm1
        vpternlogq $0x96, %xmm2, %xmm4, %xmm25 # xmm25 = xmm25 ^ xmm4 ^ xmm2
        vmovdqa64 %xmm6, %xmm26
        vpternlogq $0x96, %xmm7, %xmm9, %xmm26 # xmm26 = xmm26 ^ xmm9 ^ xmm7
        vpternlogq $0x96, %xmm8, %xmm5, %xmm26 # xmm26 = xmm26 ^ xmm5 ^ xmm8
        vmovdqa64 %xmm12, %xmm27
        vpternlogq $0x96, %xmm13, %xmm10, %xmm27 # xmm27 = xmm27 ^ xmm10 ^ xmm13
        vpternlogq $0x96, %xmm14, %xmm11, %xmm27 # xmm27 = xmm27 ^ xmm11 ^ xmm14
        vmovdqa64 %xmm18, %xmm28
        vpternlogq $0x96, %xmm19, %xmm16, %xmm28 # xmm28 = xmm28 ^ xmm16 ^ xmm19
        vpternlogq $0x96, %xmm15, %xmm17, %xmm28 # xmm28 = xmm28 ^ xmm17 ^ xmm15
        vmovdqa64 %xmm24, %xmm29
        vpternlogq $0x96, %xmm20, %xmm22, %xmm29 # xmm29 = xmm29 ^ xmm22 ^ xmm20
        vpternlogq $0x96, %xmm21, %xmm23, %xmm29 # xmm29 = xmm29 ^ xmm23 ^ xmm21
        vprolq $0x1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0 # xmm0 = xmm0 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm3 # xmm3 = xmm3 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm1 # xmm1 = xmm1 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm4 # xmm4 = xmm4 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm2 # xmm2 = xmm2 ^ xmm29 ^ xmm30
        vprolq $0x1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm6 # xmm6 = xmm6 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm9 # xmm9 = xmm9 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm7 # xmm7 = xmm7 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm5 # xmm5 = xmm5 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm8 # xmm8 = xmm8 ^ xmm25 ^ xmm30
        vprolq $0x1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm12 # xmm12 = xmm12 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm10 # xmm10 = xmm10 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm13 # xmm13 = xmm13 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm11 # xmm11 = xmm11 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm14 # xmm14 = xmm14 ^ xmm26 ^ xmm30
        vprolq $0x1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm18 # xmm18 = xmm18 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm16 # xmm16 = xmm16 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm19 # xmm19 = xmm19 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm17 # xmm17 = xmm17 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm15 # xmm15 = xmm15 ^ xmm27 ^ xmm30
        vprolq $0x1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm24 # xmm24 = xmm24 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm22 # xmm22 = xmm22 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm20 # xmm20 = xmm20 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm23 # xmm23 = xmm23 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm21 # xmm21 = xmm21 ^ xmm28 ^ xmm30
        vprolq $0x24, %xmm3, %xmm3
        vprolq $0x3, %xmm1, %xmm1
        vprolq $0x29, %xmm4, %xmm4
        vprolq $0x12, %xmm2, %xmm2
        vprolq $0x1, %xmm6, %xmm6
        vprolq $0x2c, %xmm9, %xmm9
        vprolq $0xa, %xmm7, %xmm7
        vprolq $0x2d, %xmm5, %xmm5
        vprolq $0x2, %xmm8, %xmm8
        vprolq $0x3e, %xmm12, %xmm12
        vprolq $0x6, %xmm10, %xmm10
        vprolq $0x2b, %xmm13, %xmm13
        vprolq $0xf, %xmm11, %xmm11
        vprolq $0x3d, %xmm14, %xmm14
        vprolq $0x1c, %xmm18, %xmm18
        vprolq $0x37, %xmm16, %xmm16
        vprolq $0x19, %xmm19, %xmm19
        vprolq $0x15, %xmm17, %xmm17
        vprolq $0x38, %xmm15, %xmm15
        vprolq $0x1b, %xmm24, %xmm24
        vprolq $0x14, %xmm22, %xmm22
        vprolq $0x27, %xmm20, %xmm20
        vprolq $0x8, %xmm23, %xmm23
        vprolq $0xe, %xmm21, %xmm21
        vmovdqa64 %xmm0, %xmm30
        vmovdqa64 %xmm9, %xmm31
        vpternlogq $0xd2, %xmm13, %xmm9, %xmm0 # xmm0 = xmm0 ^ (xmm13 & ~xmm9)
        vpxorq 0x8(%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm17, %xmm13, %xmm9 # xmm9 = xmm9 ^ (xmm17 & ~xmm13)
        vpternlogq $0xd2, %xmm21, %xmm17, %xmm13 # xmm13 = xmm13 ^ (xmm21 & ~xmm17)
        vpternlogq $0xd2, %xmm30, %xmm21, %xmm17 # xmm17 = xmm17 ^ (xmm30 & ~xmm21)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm21 # xmm21 = xmm21 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm18, %xmm30
        vmovdqa64 %xmm22, %xmm31
        vpternlogq $0xd2, %xmm1, %xmm22, %xmm18 # xmm18 = xmm18 ^ (xmm1 & ~xmm22)
        vpternlogq $0xd2, %xmm5, %xmm1, %xmm22 # xmm22 = xmm22 ^ (xmm5 & ~xmm1)
        vpternlogq $0xd2, %xmm14, %xmm5, %xmm1 # xmm1 = xmm1 ^ (xmm14 & ~xmm5)
        vpternlogq $0xd2, %xmm30, %xmm14, %xmm5 # xmm5 = xmm5 ^ (xmm30 & ~xmm14)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm14 # xmm14 = xmm14 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm6, %xmm30
        vmovdqa64 %xmm10, %xmm31
        vpternlogq $0xd2, %xmm19, %xmm10, %xmm6 # xmm6 = xmm6 ^ (xmm19 & ~xmm10)
        vpternlogq $0xd2, %xmm23, %xmm19, %xmm10 # xmm10 = xmm10 ^ (xmm23 & ~xmm19)
        vpternlogq $0xd2, %xmm2, %xmm23, %xmm19 # xmm19 = xmm19 ^ (xmm2 & ~xmm23)
        vpternlogq $0xd2, %xmm30, %xmm2, %xmm23 # xmm23 = xmm23 ^ (xmm30 & ~xmm2)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm2 # xmm2 = xmm2 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm24, %xmm30
        vmovdqa64 %xmm3, %xmm31
        vpternlogq $0xd2, %xmm7, %xmm3, %xmm24 # xmm24 = xmm24 ^ (xmm7 & ~xmm3)
        vpternlogq $0xd2, %xmm11, %xmm7, %xmm3 # xmm3 = xmm3 ^ (xmm11 & ~xmm7)
        vpternlogq $0xd2, %xmm15, %xmm11, %xmm7 # xmm7 = xmm7 ^ (xmm15 & ~xmm11)
        vpternlogq $0xd2, %xmm30, %xmm15, %xmm11 # xmm11 = xmm11 ^ (xmm30 & ~xmm15)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm15 # xmm15 = xmm15 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm12, %xmm30
        vmovdqa64 %xmm16, %xmm31
        vpternlogq $0xd2, %xmm20, %xmm16, %xmm12 # xmm12 = xmm12 ^ (xmm20 & ~xmm16)
        vpternlogq $0xd2, %xmm4, %xmm20, %xmm16 # xmm16 = xmm16 ^ (xmm4 & ~xmm20)
        vpternlogq $0xd2, %xmm8, %xmm4, %xmm20 # xmm20 = xmm20 ^ (xmm8 & ~xmm4)
        vpternlogq $0xd2, %xmm30, %xmm8, %xmm4 # xmm4 = xmm4 ^ (xmm30 & ~xmm8)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm8 # xmm8 = xmm8 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm0, %xmm25
        vpternlogq $0x96, %xmm6, %xmm18, %xmm25 # xmm25 = xmm25 ^ xmm18 ^ xmm6
        vpternlogq $0x96, %xmm12, %xmm24, %xmm25 # xmm25 = xmm25 ^ xmm24 ^ xmm12
        vmovdqa64 %xmm9, %xmm26
        vpternlogq $0x96, %xmm10, %xmm22, %xmm26 # xmm26 = xmm26 ^ xmm22 ^ xmm10
        vpternlogq $0x96, %xmm16, %xmm3, %xmm26 # xmm26 = xmm26 ^ xmm3 ^ xmm16
        vmovdqa64 %xmm13, %xmm27
        vpternlogq $0x96, %xmm19, %xmm1, %xmm27 # xmm27 = xmm27 ^ xmm1 ^ xmm19
        vpternlogq $0x96, %xmm20, %xmm7, %xmm27 # xmm27 = xmm27 ^ xmm7 ^ xmm20
        vmovdqa64 %xmm17, %xmm28
        vpternlogq $0x96, %xmm23, %xmm5, %xmm28 # xmm28 = xmm28 ^ xmm5 ^ xmm23
        vpternlogq $0x96, %xmm4, %xmm11, %xmm28 # xmm28 = xmm28 ^ xmm11 ^ xmm4
        vmovdqa64 %xmm21, %xmm29
        vpternlogq $0x96, %xmm2, %xmm14, %xmm29 # xmm29 = xmm29 ^ xmm14 ^ xmm2
        vpternlogq $0x96, %xmm8, %xmm15, %xmm29 # xmm29 = xmm29 ^ xmm15 ^ xmm8
        vprolq $0x1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0 # xmm0 = xmm0 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm18 # xmm18 = xmm18 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm6 # xmm6 = xmm6 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm24 # xmm24 = xmm24 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm12 # xmm12 = xmm12 ^ xmm29 ^ xmm30
        vprolq $0x1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm9 # xmm9 = xmm9 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm22 # xmm22 = xmm22 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm10 # xmm10 = xmm10 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm3 # xmm3 = xmm3 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm16 # xmm16 = xmm16 ^ xmm25 ^ xmm30
        vprolq $0x1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm13 # xmm13 = xmm13 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm1 # xmm1 = xmm1 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm19 # xmm19 = xmm19 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm7 # xmm7 = xmm7 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm20 # xmm20 = xmm20 ^ xmm26 ^ xmm30
        vprolq $0x1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm17 # xmm17 = xmm17 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm5 # xmm5 = xmm5 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm23 # xmm23 = xmm23 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm11 # xmm11 = xmm11 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm4 # xmm4 = xmm4 ^ xmm27 ^ xmm30
        vprolq $0x1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm21 # xmm21 = xmm21 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm14 # xmm14 = xmm14 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm2 # xmm2 = xmm2 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm15 # xmm15 = xmm15 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm8 # xmm8 = xmm8 ^ xmm28 ^ xmm30
        vprolq $0x24, %xmm18, %xmm18
        vprolq $0x3, %xmm6, %xmm6
        vprolq $0x29, %xmm24, %xmm24
        vprolq $0x12, %xmm12, %xmm12
        vprolq $0x1, %xmm9, %xmm9
        vprolq $0x2c, %xmm22, %xmm22
        vprolq $0xa, %xmm10, %xmm10
        vprolq $0x2d, %xmm3, %xmm3
        vprolq $0x2, %xmm16, %xmm16
        vprolq $0x3e, %xmm13, %xmm13
        vprolq $0x6, %xmm1, %xmm1
        vprolq $0x2b, %xmm19, %xmm19
        vprolq $0xf, %xmm7, %xmm7
        vprolq $0x3d, %xmm20, %xmm20
        vprolq $0x1c, %xmm17, %xmm17
        vprolq $0x37, %xmm5, %xmm5
        vprolq $0x19, %xmm23, %xmm23
        vprolq $0x15, %xmm11, %xmm11
        vprolq $0x38, %xmm4, %xmm4
        vprolq $0x1b, %xmm21, %xmm21
        vprolq $0x14, %xmm14, %xmm14
        vprolq $0x27, %xmm2, %xmm2
        vprolq $0x8, %xmm15, %xmm15
        vprolq $0xe, %xmm8, %xmm8
        vmovdqa64 %xmm0, %xmm30
        vmovdqa64 %xmm22, %xmm31
        vpternlogq $0xd2, %xmm19, %xmm22, %xmm0 # xmm0 = xmm0 ^ (xmm19 & ~xmm22)
        vpxorq 0x10(%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm11, %xmm19, %xmm22 # xmm22 = xmm22 ^ (xmm11 & ~xmm19)
        vpternlogq $0xd2, %xmm8, %xmm11, %xmm19 # xmm19 = xmm19 ^ (xmm8 & ~xmm11)
        vpternlogq $0xd2, %xmm30, %xmm8, %xmm11 # xmm11 = xmm11 ^ (xmm30 & ~xmm8)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm8 # xmm8 = xmm8 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm17, %xmm30
        vmovdqa64 %xmm14, %xmm31
        vpternlogq $0xd2, %xmm6, %xmm14, %xmm17 # xmm17 = xmm17 ^ (xmm6 & ~xmm14)
        vpternlogq $0xd2, %xmm3, %xmm6, %xmm14 # xmm14 = xmm14 ^ (xmm3 & ~xmm6)
        vpternlogq $0xd2, %xmm20, %xmm3, %xmm6 # xmm6 = xmm6 ^ (xmm20 & ~xmm3)
        vpternlogq $0xd2, %xmm30, %xmm20, %xmm3 # xmm3 = xmm3 ^ (xmm30 & ~xmm20)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm20 # xmm20 = xmm20 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm9, %xmm30
        vmovdqa64 %xmm1, %xmm31
        vpternlogq $0xd2, %xmm23, %xmm1, %xmm9 # xmm9 = xmm9 ^ (xmm23 & ~xmm1)
        vpternlogq $0xd2, %xmm15, %xmm23, %xmm1 # xmm1 = xmm1 ^ (xmm15 & ~xmm23)
        vpternlogq $0xd2, %xmm12, %xmm15, %xmm23 # xmm23 = xmm23 ^ (xmm12 & ~xmm15)
        vpternlogq $0xd2, %xmm30, %xmm12, %xmm15 # xmm15 = xmm15 ^ (xmm30 & ~xmm12)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm12 # xmm12 = xmm12 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm21, %xmm30
        vmovdqa64 %xmm18, %xmm31
        vpternlogq $0xd2, %xmm10, %xmm18, %xmm21 # xmm21 = xmm21 ^ (xmm10 & ~xmm18)
        vpternlogq $0xd2, %xmm7, %xmm10, %xmm18 # xmm18 = xmm18 ^ (xmm7 & ~xmm10)
        vpternlogq $0xd2, %xmm4, %xmm7, %xmm10 # xmm10 = xmm10 ^ (xmm4 & ~xmm7)
        vpternlogq $0xd2, %xmm30, %xmm4, %xmm7 # xmm7 = xmm7 ^ (xmm30 & ~xmm4)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm4 # xmm4 = xmm4 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm13, %xmm30
        vmovdqa64 %xmm5, %xmm31
        vpternlogq $0xd2, %xmm2, %xmm5, %xmm13 # xmm13 = xmm13 ^ (xmm2 & ~xmm5)
        vpternlogq $0xd2, %xmm24, %xmm2, %xmm5 # xmm5 = xmm5 ^ (xmm24 & ~xmm2)
        vpternlogq $0xd2, %xmm16, %xmm24, %xmm2 # xmm2 = xmm2 ^ (xmm16 & ~xmm24)
        vpternlogq $0xd2, %xmm30, %xmm16, %xmm24 # xmm24 = xmm24 ^ (xmm30 & ~xmm16)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm16 # xmm16 = xmm16 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm0, %xmm25
        vpternlogq $0x96, %xmm9, %xmm17, %xmm25 # xmm25 = xmm25 ^ xmm17 ^ xmm9
        vpternlogq $0x96, %xmm13, %xmm21, %xmm25 # xmm25 = xmm25 ^ xmm21 ^ xmm13
        vmovdqa64 %xmm22, %xmm26
        vpternlogq $0x96, %xmm1, %xmm14, %xmm26 # xmm26 = xmm26 ^ xmm14 ^ xmm1
        vpternlogq $0x96, %xmm5, %xmm18, %xmm26 # xmm26 = xmm26 ^ xmm18 ^ xmm5
        vmovdqa64 %xmm19, %xmm27
        vpternlogq $0x96, %xmm23, %xmm6, %xmm27 # xmm27 = xmm27 ^ xmm6 ^ xmm23
        vpternlogq $0x96, %xmm2, %xmm10, %xmm27 # xmm27 = xmm27 ^ xmm10 ^ xmm2
        vmovdqa64 %xmm11, %xmm28
        vpternlogq $0x96, %xmm15, %xmm3, %xmm28 # xmm28 = xmm28 ^ xmm3 ^ xmm15
        vpternlogq $0x96, %xmm24, %xmm7, %xmm28 # xmm28 = xmm28 ^ xmm7 ^ xmm24
        vmovdqa64 %xmm8, %xmm29
        vpternlogq $0x96, %xmm12, %xmm20, %xmm29 # xmm29 = xmm29 ^ xmm20 ^ xmm12
        vpternlogq $0x96, %xmm16, %xmm4, %xmm29 # xmm29 = xmm29 ^ xmm4 ^ xmm16
        vprolq $0x1, %xmm26, %xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm0 # xmm0 = xmm0 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm17 # xmm17 = xmm17 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm9 # xmm9 = xmm9 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm21 # xmm21 = xmm21 ^ xmm29 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm29, %xmm13 # xmm13 = xmm13 ^ xmm29 ^ xmm30
        vprolq $0x1, %xmm27, %xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm22 # xmm22 = xmm22 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm14 # xmm14 = xmm14 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm1 # xmm1 = xmm1 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm18 # xmm18 = xmm18 ^ xmm25 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm25, %xmm5 # xmm5 = xmm5 ^ xmm25 ^ xmm30
        vprolq $0x1, %xmm28, %xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm19 # xmm19 = xmm19 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm6 # xmm6 = xmm6 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm23 # xmm23 = xmm23 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm10 # xmm10 = xmm10 ^ xmm26 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm26, %xmm2 # xmm2 = xmm2 ^ xmm26 ^ xmm30
        vprolq $0x1, %xmm29, %xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm11 # xmm11 = xmm11 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm3 # xmm3 = xmm3 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm15 # xmm15 = xmm15 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm7 # xmm7 = xmm7 ^ xmm27 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm27, %xmm24 # xmm24 = xmm24 ^ xmm27 ^ xmm30
        vprolq $0x1, %xmm25, %xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm8 # xmm8 = xmm8 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm20 # xmm20 = xmm20 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm12 # xmm12 = xmm12 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm4 # xmm4 = xmm4 ^ xmm28 ^ xmm30
        vpternlogq $0x96, %xmm30, %xmm28, %xmm16 # xmm16 = xmm16 ^ xmm28 ^ xmm30
        vprolq $0x24, %xmm17, %xmm17
        vprolq $0x3, %xmm9, %xmm9
        vprolq $0x29, %xmm21, %xmm21
        vprolq $0x12, %xmm13, %xmm13
        vprolq $0x1, %xmm22, %xmm22
        vprolq $0x2c, %xmm14, %xmm14
        vprolq $0xa, %xmm1, %xmm1
        vprolq $0x2d, %xmm18, %xmm18
        vprolq $0x2, %xmm5, %xmm5
        vprolq $0x3e, %xmm19, %xmm19
        vprolq $0x6, %xmm6, %xmm6
        vprolq $0x2b, %xmm23, %xmm23
        vprolq $0xf, %xmm10, %xmm10
        vprolq $0x3d, %xmm2, %xmm2
        vprolq $0x1c, %xmm11, %xmm11
        vprolq $0x37, %xmm3, %xmm3
        vprolq $0x19, %xmm15, %xmm15
        vprolq $0x15, %xmm7, %xmm7
        vprolq $0x38, %xmm24, %xmm24
        vprolq $0x1b, %xmm8, %xmm8
        vprolq $0x14, %xmm20, %xmm20
        vprolq $0x27, %xmm12, %xmm12
        vprolq $0x8, %xmm4, %xmm4
        vprolq $0xe, %xmm16, %xmm16
        vmovdqa64 %xmm0, %xmm30
        vmovdqa64 %xmm14, %xmm31
        vpternlogq $0xd2, %xmm23, %xmm14, %xmm0 # xmm0 = xmm0 ^ (xmm23 & ~xmm14)
        vpxorq 0x18(%rsi){1to2}, %xmm0, %xmm0
        vpternlogq $0xd2, %xmm7, %xmm23, %xmm14 # xmm14 = xmm14 ^ (xmm7 & ~xmm23)
        vpternlogq $0xd2, %xmm16, %xmm7, %xmm23 # xmm23 = xmm23 ^ (xmm16 & ~xmm7)
        vpternlogq $0xd2, %xmm30, %xmm16, %xmm7 # xmm7 = xmm7 ^ (xmm30 & ~xmm16)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm16 # xmm16 = xmm16 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm11, %xmm30
        vmovdqa64 %xmm20, %xmm31
        vpternlogq $0xd2, %xmm9, %xmm20, %xmm11 # xmm11 = xmm11 ^ (xmm9 & ~xmm20)
        vpternlogq $0xd2, %xmm18, %xmm9, %xmm20 # xmm20 = xmm20 ^ (xmm18 & ~xmm9)
        vpternlogq $0xd2, %xmm2, %xmm18, %xmm9 # xmm9 = xmm9 ^ (xmm2 & ~xmm18)
        vpternlogq $0xd2, %xmm30, %xmm2, %xmm18 # xmm18 = xmm18 ^ (xmm30 & ~xmm2)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm2 # xmm2 = xmm2 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm22, %xmm30
        vmovdqa64 %xmm6, %xmm31
        vpternlogq $0xd2, %xmm15, %xmm6, %xmm22 # xmm22 = xmm22 ^ (xmm15 & ~xmm6)
        vpternlogq $0xd2, %xmm4, %xmm15, %xmm6 # xmm6 = xmm6 ^ (xmm4 & ~xmm15)
        vpternlogq $0xd2, %xmm13, %xmm4, %xmm15 # xmm15 = xmm15 ^ (xmm13 & ~xmm4)
        vpternlogq $0xd2, %xmm30, %xmm13, %xmm4 # xmm4 = xmm4 ^ (xmm30 & ~xmm13)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm13 # xmm13 = xmm13 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm8, %xmm30
        vmovdqa64 %xmm17, %xmm31
        vpternlogq $0xd2, %xmm1, %xmm17, %xmm8 # xmm8 = xmm8 ^ (xmm1 & ~xmm17)
        vpternlogq $0xd2, %xmm10, %xmm1, %xmm17 # xmm17 = xmm17 ^ (xmm10 & ~xmm1)
        vpternlogq $0xd2, %xmm24, %xmm10, %xmm1 # xmm1 = xmm1 ^ (xmm24 & ~xmm10)
        vpternlogq $0xd2, %xmm30, %xmm24, %xmm10 # xmm10 = xmm10 ^ (xmm30 & ~xmm24)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm24 # xmm24 = xmm24 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm19, %xmm30
        vmovdqa64 %xmm3, %xmm31
        vpternlogq $0xd2, %xmm12, %xmm3, %xmm19 # xmm19 = xmm19 ^ (xmm12 & ~xmm3)
        vpternlogq $0xd2, %xmm21, %xmm12, %xmm3 # xmm3 = xmm3 ^ (xmm21 & ~xmm12)
        vpternlogq $0xd2, %xmm5, %xmm21, %xmm12 # xmm12 = xmm12 ^ (xmm5 & ~xmm21)
        vpternlogq $0xd2, %xmm30, %xmm5, %xmm21 # xmm21 = xmm21 ^ (xmm30 & ~xmm5)
        vpternlogq $0xd2, %xmm31, %xmm30, %xmm5 # xmm5 = xmm5 ^ (xmm31 & ~xmm30)
        vmovdqa64 %xmm1, %xmm30
        vmovdqa %xmm14, %xmm1
        vmovdqa %xmm13, %xmm14
        vmovdqa %xmm4, %xmm13
        vmovdqa64 %xmm16, %xmm4
        vmovdqa64 %xmm17, %xmm16
        vmovdqa64 %xmm30, %xmm17
        vmovdqa64 %xmm2, %xmm30
        vmovdqa64 %xmm23, %xmm2
        vmovdqa64 %xmm21, %xmm23
        vmovdqa64 %xmm3, %xmm21
        vmovdqa %xmm7, %xmm3
        vmovdqa %xmm9, %xmm7
        vmovdqa64 %xmm30, %xmm9
        vmovdqa64 %xmm5, %xmm30
        vmovdqa %xmm11, %xmm5
        vmovdqa %xmm6, %xmm11
        vmovdqa64 %xmm20, %xmm6
        vmovdqa64 %xmm19, %xmm20
        vmovdqa64 %xmm24, %xmm19
        vmovdqa64 %xmm30, %xmm24
        vmovdqa64 %xmm8, %xmm30
        vmovdqa64 %xmm18, %xmm8
        vmovdqa64 %xmm10, %xmm18
        vmovdqa64 %xmm22, %xmm10
        vmovdqa64 %xmm12, %xmm22
        vmovdqa %xmm15, %xmm12
        vmovdqa64 %xmm30, %xmm15
        addq $0x20, %rsi
        cmpq %rax, %rsi
        jne Lmlk_keccak_f1600_x1_avx512_loop
        vmovq %xmm0, (%rdi)
        vmovq %xmm1, 0x8(%rdi)
        vmovq %xmm2, 0x10(%rdi)
        vmovq %xmm3, 0x18(%rdi)
        vmovq %xmm4, 0x20(%rdi)
        vmovq %xmm5, 0x28(%rdi)
        vmovq %xmm6, 0x30(%rdi)
        vmovq %xmm7, 0x38(%rdi)
        vmovq %xmm8, 0x40(%rdi)
        vmovq %xmm9, 0x48(%rdi)
        vmovq %xmm10, 0x50(%rdi)
        vmovq %xmm11, 0x58(%rdi)
        vmovq %xmm12, 0x60(%rdi)
        vmovq %xmm13, 0x68(%rdi)
        vmovq %xmm14, 0x70(%rdi)
        vmovq %xmm15, 0x78(%rdi)
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x47, 0x10 /* vmovq %xmm16, 0x80(%rdi) */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x4f, 0x11 /* vmovq %xmm17, 0x88(%rdi) */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x57, 0x12 /* vmovq %xmm18, 0x90(%rdi) */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x5f, 0x13 /* vmovq %xmm19, 0x98(%rdi) */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x67, 0x14 /* vmovq %xmm20, 0xa0(%rdi) */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x6f, 0x15 /* vmovq %xmm21, 0xa8(%rdi) */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x77, 0x16 /* vmovq %xmm22, 0xb0(%rdi) */
        .byte 0x62, 0xe1, 0xfd, 0x08, 0x7e, 0x7f, 0x17 /* vmovq %xmm23, 0xb8(%rdi) */
        .byte 0x62, 0x61, 0xfd, 0x08, 0x7e, 0x47, 0x18 /* vmovq %xmm24, 0xc0(%rdi) */
        vzeroupper
        retq
        .cfi_endproc

MLK_ASM_FN_SIZE(keccak_f1600_x1_avx512_asm)

#endif /* MLK_SYS_X86_64_AVX512 && MLK_FIPS202_X86_64_NEED_X1_AVX512 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
