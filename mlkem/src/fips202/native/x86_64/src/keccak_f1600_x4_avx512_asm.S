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


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/x86_64/src/keccak_f1600_x4_avx512_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x4_avx512_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x4_avx512_asm)

        .cfi_startproc
        vmovdqu64 (%rdi), %ymm25
        vmovdqu64 0xc8(%rdi), %ymm26
        vmovdqu64 0x190(%rdi), %ymm27
        vmovdqu64 0x258(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29 # ymm29 = ymm25[0],ymm26[0],ymm25[2],ymm26[2]
        vpunpckhqdq %ymm26, %ymm25, %ymm30 # ymm30 = ymm25[1],ymm26[1],ymm25[3],ymm26[3]
        vpunpcklqdq %ymm28, %ymm27, %ymm31 # ymm31 = ymm27[0],ymm28[0],ymm27[2],ymm28[2]
        vpunpckhqdq %ymm28, %ymm27, %ymm25 # ymm25 = ymm27[1],ymm28[1],ymm27[3],ymm28[3]
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm0 # ymm0 = ymm29[0,1],ymm31[0,1]
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm1 # ymm1 = ymm30[0,1],ymm25[0,1]
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm2 # ymm2 = ymm29[2,3],ymm31[2,3]
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm3 # ymm3 = ymm30[2,3],ymm25[2,3]
        vmovdqu64 0x20(%rdi), %ymm25
        vmovdqu64 0xe8(%rdi), %ymm26
        vmovdqu64 0x1b0(%rdi), %ymm27
        vmovdqu64 0x278(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29 # ymm29 = ymm25[0],ymm26[0],ymm25[2],ymm26[2]
        vpunpckhqdq %ymm26, %ymm25, %ymm30 # ymm30 = ymm25[1],ymm26[1],ymm25[3],ymm26[3]
        vpunpcklqdq %ymm28, %ymm27, %ymm31 # ymm31 = ymm27[0],ymm28[0],ymm27[2],ymm28[2]
        vpunpckhqdq %ymm28, %ymm27, %ymm25 # ymm25 = ymm27[1],ymm28[1],ymm27[3],ymm28[3]
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm4 # ymm4 = ymm29[0,1],ymm31[0,1]
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm5 # ymm5 = ymm30[0,1],ymm25[0,1]
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm6 # ymm6 = ymm29[2,3],ymm31[2,3]
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm7 # ymm7 = ymm30[2,3],ymm25[2,3]
        vmovdqu64 0x40(%rdi), %ymm25
        vmovdqu64 0x108(%rdi), %ymm26
        vmovdqu64 0x1d0(%rdi), %ymm27
        vmovdqu64 0x298(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29 # ymm29 = ymm25[0],ymm26[0],ymm25[2],ymm26[2]
        vpunpckhqdq %ymm26, %ymm25, %ymm30 # ymm30 = ymm25[1],ymm26[1],ymm25[3],ymm26[3]
        vpunpcklqdq %ymm28, %ymm27, %ymm31 # ymm31 = ymm27[0],ymm28[0],ymm27[2],ymm28[2]
        vpunpckhqdq %ymm28, %ymm27, %ymm25 # ymm25 = ymm27[1],ymm28[1],ymm27[3],ymm28[3]
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm8 # ymm8 = ymm29[0,1],ymm31[0,1]
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm9 # ymm9 = ymm30[0,1],ymm25[0,1]
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm10 # ymm10 = ymm29[2,3],ymm31[2,3]
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm11 # ymm11 = ymm30[2,3],ymm25[2,3]
        vmovdqu64 0x60(%rdi), %ymm25
        vmovdqu64 0x128(%rdi), %ymm26
        vmovdqu64 0x1f0(%rdi), %ymm27
        vmovdqu64 0x2b8(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29 # ymm29 = ymm25[0],ymm26[0],ymm25[2],ymm26[2]
        vpunpckhqdq %ymm26, %ymm25, %ymm30 # ymm30 = ymm25[1],ymm26[1],ymm25[3],ymm26[3]
        vpunpcklqdq %ymm28, %ymm27, %ymm31 # ymm31 = ymm27[0],ymm28[0],ymm27[2],ymm28[2]
        vpunpckhqdq %ymm28, %ymm27, %ymm25 # ymm25 = ymm27[1],ymm28[1],ymm27[3],ymm28[3]
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm12 # ymm12 = ymm29[0,1],ymm31[0,1]
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm13 # ymm13 = ymm30[0,1],ymm25[0,1]
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm14 # ymm14 = ymm29[2,3],ymm31[2,3]
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm15 # ymm15 = ymm30[2,3],ymm25[2,3]
        vmovdqu64 0x80(%rdi), %ymm25
        vmovdqu64 0x148(%rdi), %ymm26
        vmovdqu64 0x210(%rdi), %ymm27
        vmovdqu64 0x2d8(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29 # ymm29 = ymm25[0],ymm26[0],ymm25[2],ymm26[2]
        vpunpckhqdq %ymm26, %ymm25, %ymm30 # ymm30 = ymm25[1],ymm26[1],ymm25[3],ymm26[3]
        vpunpcklqdq %ymm28, %ymm27, %ymm31 # ymm31 = ymm27[0],ymm28[0],ymm27[2],ymm28[2]
        vpunpckhqdq %ymm28, %ymm27, %ymm25 # ymm25 = ymm27[1],ymm28[1],ymm27[3],ymm28[3]
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm16 # ymm16 = ymm29[0,1],ymm31[0,1]
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm17 # ymm17 = ymm30[0,1],ymm25[0,1]
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm18 # ymm18 = ymm29[2,3],ymm31[2,3]
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm19 # ymm19 = ymm30[2,3],ymm25[2,3]
        vmovdqu64 0xa0(%rdi), %ymm25
        vmovdqu64 0x168(%rdi), %ymm26
        vmovdqu64 0x230(%rdi), %ymm27
        vmovdqu64 0x2f8(%rdi), %ymm28
        vpunpcklqdq %ymm26, %ymm25, %ymm29 # ymm29 = ymm25[0],ymm26[0],ymm25[2],ymm26[2]
        vpunpckhqdq %ymm26, %ymm25, %ymm30 # ymm30 = ymm25[1],ymm26[1],ymm25[3],ymm26[3]
        vpunpcklqdq %ymm28, %ymm27, %ymm31 # ymm31 = ymm27[0],ymm28[0],ymm27[2],ymm28[2]
        vpunpckhqdq %ymm28, %ymm27, %ymm25 # ymm25 = ymm27[1],ymm28[1],ymm27[3],ymm28[3]
        vshufi64x2 $0x0, %ymm31, %ymm29, %ymm20 # ymm20 = ymm29[0,1],ymm31[0,1]
        vshufi64x2 $0x0, %ymm25, %ymm30, %ymm21 # ymm21 = ymm30[0,1],ymm25[0,1]
        vshufi64x2 $0x3, %ymm31, %ymm29, %ymm22 # ymm22 = ymm29[2,3],ymm31[2,3]
        vshufi64x2 $0x3, %ymm25, %ymm30, %ymm23 # ymm23 = ymm30[2,3],ymm25[2,3]
        .byte 0x62, 0x61, 0xfd, 0x08, 0x6e, 0x47, 0x18 /* vmovq 0xc0(%rdi), %xmm24 */
        vpinsrq $0x1, 0x188(%rdi), %xmm24, %xmm24
        .byte 0x62, 0x61, 0xfd, 0x08, 0x6e, 0x4f, 0x4a /* vmovq 0x250(%rdi), %xmm25 */
        vpinsrq $0x1, 0x318(%rdi), %xmm25, %xmm25
        vinserti32x4 $0x1, %xmm25, %ymm24, %ymm24
        leaq 0xc0(%rsi), %rax

Lmlk_keccak_f1600_x4_avx512_loop:
        vmovdqa64 %ymm0, %ymm25
        vpternlogq $0x96, %ymm10, %ymm5, %ymm25 # ymm25 = ymm25 ^ ymm5 ^ ymm10
        vpternlogq $0x96, %ymm20, %ymm15, %ymm25 # ymm25 = ymm25 ^ ymm15 ^ ymm20
        vmovdqa64 %ymm1, %ymm26
        vpternlogq $0x96, %ymm11, %ymm6, %ymm26 # ymm26 = ymm26 ^ ymm6 ^ ymm11
        vpternlogq $0x96, %ymm21, %ymm16, %ymm26 # ymm26 = ymm26 ^ ymm16 ^ ymm21
        vmovdqa64 %ymm2, %ymm27
        vpternlogq $0x96, %ymm12, %ymm7, %ymm27 # ymm27 = ymm27 ^ ymm7 ^ ymm12
        vpternlogq $0x96, %ymm22, %ymm17, %ymm27 # ymm27 = ymm27 ^ ymm17 ^ ymm22
        vmovdqa64 %ymm3, %ymm28
        vpternlogq $0x96, %ymm13, %ymm8, %ymm28 # ymm28 = ymm28 ^ ymm8 ^ ymm13
        vpternlogq $0x96, %ymm23, %ymm18, %ymm28 # ymm28 = ymm28 ^ ymm18 ^ ymm23
        vmovdqa64 %ymm4, %ymm29
        vpternlogq $0x96, %ymm14, %ymm9, %ymm29 # ymm29 = ymm29 ^ ymm9 ^ ymm14
        vpternlogq $0x96, %ymm24, %ymm19, %ymm29 # ymm29 = ymm29 ^ ymm19 ^ ymm24
        vprolq $0x1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0 # ymm0 = ymm0 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm5 # ymm5 = ymm5 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm10 # ymm10 = ymm10 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm15 # ymm15 = ymm15 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm20 # ymm20 = ymm20 ^ ymm29 ^ ymm30
        vprolq $0x1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm1 # ymm1 = ymm1 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm6 # ymm6 = ymm6 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm11 # ymm11 = ymm11 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm16 # ymm16 = ymm16 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm21 # ymm21 = ymm21 ^ ymm25 ^ ymm30
        vprolq $0x1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm2 # ymm2 = ymm2 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm7 # ymm7 = ymm7 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm12 # ymm12 = ymm12 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm17 # ymm17 = ymm17 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm22 # ymm22 = ymm22 ^ ymm26 ^ ymm30
        vprolq $0x1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm3 # ymm3 = ymm3 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm8 # ymm8 = ymm8 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm13 # ymm13 = ymm13 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm18 # ymm18 = ymm18 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm23 # ymm23 = ymm23 ^ ymm27 ^ ymm30
        vprolq $0x1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm4 # ymm4 = ymm4 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm9 # ymm9 = ymm9 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm14 # ymm14 = ymm14 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm19 # ymm19 = ymm19 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm24 # ymm24 = ymm24 ^ ymm28 ^ ymm30
        vprolq $0x24, %ymm5, %ymm5
        vprolq $0x3, %ymm10, %ymm10
        vprolq $0x29, %ymm15, %ymm15
        vprolq $0x12, %ymm20, %ymm20
        vprolq $0x1, %ymm1, %ymm1
        vprolq $0x2c, %ymm6, %ymm6
        vprolq $0xa, %ymm11, %ymm11
        vprolq $0x2d, %ymm16, %ymm16
        vprolq $0x2, %ymm21, %ymm21
        vprolq $0x3e, %ymm2, %ymm2
        vprolq $0x6, %ymm7, %ymm7
        vprolq $0x2b, %ymm12, %ymm12
        vprolq $0xf, %ymm17, %ymm17
        vprolq $0x3d, %ymm22, %ymm22
        vprolq $0x1c, %ymm3, %ymm3
        vprolq $0x37, %ymm8, %ymm8
        vprolq $0x19, %ymm13, %ymm13
        vprolq $0x15, %ymm18, %ymm18
        vprolq $0x38, %ymm23, %ymm23
        vprolq $0x1b, %ymm4, %ymm4
        vprolq $0x14, %ymm9, %ymm9
        vprolq $0x27, %ymm14, %ymm14
        vprolq $0x8, %ymm19, %ymm19
        vprolq $0xe, %ymm24, %ymm24
        vmovdqa64 %ymm0, %ymm30
        vmovdqa64 %ymm6, %ymm31
        vpternlogq $0xd2, %ymm12, %ymm6, %ymm0 # ymm0 = ymm0 ^ (ymm12 & ~ymm6)
        vpxorq (%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm18, %ymm12, %ymm6 # ymm6 = ymm6 ^ (ymm18 & ~ymm12)
        vpternlogq $0xd2, %ymm24, %ymm18, %ymm12 # ymm12 = ymm12 ^ (ymm24 & ~ymm18)
        vpternlogq $0xd2, %ymm30, %ymm24, %ymm18 # ymm18 = ymm18 ^ (ymm30 & ~ymm24)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm24 # ymm24 = ymm24 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm3, %ymm30
        vmovdqa64 %ymm9, %ymm31
        vpternlogq $0xd2, %ymm10, %ymm9, %ymm3 # ymm3 = ymm3 ^ (ymm10 & ~ymm9)
        vpternlogq $0xd2, %ymm16, %ymm10, %ymm9 # ymm9 = ymm9 ^ (ymm16 & ~ymm10)
        vpternlogq $0xd2, %ymm22, %ymm16, %ymm10 # ymm10 = ymm10 ^ (ymm22 & ~ymm16)
        vpternlogq $0xd2, %ymm30, %ymm22, %ymm16 # ymm16 = ymm16 ^ (ymm30 & ~ymm22)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm22 # ymm22 = ymm22 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm1, %ymm30
        vmovdqa64 %ymm7, %ymm31
        vpternlogq $0xd2, %ymm13, %ymm7, %ymm1 # ymm1 = ymm1 ^ (ymm13 & ~ymm7)
        vpternlogq $0xd2, %ymm19, %ymm13, %ymm7 # ymm7 = ymm7 ^ (ymm19 & ~ymm13)
        vpternlogq $0xd2, %ymm20, %ymm19, %ymm13 # ymm13 = ymm13 ^ (ymm20 & ~ymm19)
        vpternlogq $0xd2, %ymm30, %ymm20, %ymm19 # ymm19 = ymm19 ^ (ymm30 & ~ymm20)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm20 # ymm20 = ymm20 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm4, %ymm30
        vmovdqa64 %ymm5, %ymm31
        vpternlogq $0xd2, %ymm11, %ymm5, %ymm4 # ymm4 = ymm4 ^ (ymm11 & ~ymm5)
        vpternlogq $0xd2, %ymm17, %ymm11, %ymm5 # ymm5 = ymm5 ^ (ymm17 & ~ymm11)
        vpternlogq $0xd2, %ymm23, %ymm17, %ymm11 # ymm11 = ymm11 ^ (ymm23 & ~ymm17)
        vpternlogq $0xd2, %ymm30, %ymm23, %ymm17 # ymm17 = ymm17 ^ (ymm30 & ~ymm23)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm23 # ymm23 = ymm23 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm2, %ymm30
        vmovdqa64 %ymm8, %ymm31
        vpternlogq $0xd2, %ymm14, %ymm8, %ymm2 # ymm2 = ymm2 ^ (ymm14 & ~ymm8)
        vpternlogq $0xd2, %ymm15, %ymm14, %ymm8 # ymm8 = ymm8 ^ (ymm15 & ~ymm14)
        vpternlogq $0xd2, %ymm21, %ymm15, %ymm14 # ymm14 = ymm14 ^ (ymm21 & ~ymm15)
        vpternlogq $0xd2, %ymm30, %ymm21, %ymm15 # ymm15 = ymm15 ^ (ymm30 & ~ymm21)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm21 # ymm21 = ymm21 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm0, %ymm25
        vpternlogq $0x96, %ymm1, %ymm3, %ymm25 # ymm25 = ymm25 ^ ymm3 ^ ymm1
        vpternlogq $0x96, %ymm2, %ymm4, %ymm25 # ymm25 = ymm25 ^ ymm4 ^ ymm2
        vmovdqa64 %ymm6, %ymm26
        vpternlogq $0x96, %ymm7, %ymm9, %ymm26 # ymm26 = ymm26 ^ ymm9 ^ ymm7
        vpternlogq $0x96, %ymm8, %ymm5, %ymm26 # ymm26 = ymm26 ^ ymm5 ^ ymm8
        vmovdqa64 %ymm12, %ymm27
        vpternlogq $0x96, %ymm13, %ymm10, %ymm27 # ymm27 = ymm27 ^ ymm10 ^ ymm13
        vpternlogq $0x96, %ymm14, %ymm11, %ymm27 # ymm27 = ymm27 ^ ymm11 ^ ymm14
        vmovdqa64 %ymm18, %ymm28
        vpternlogq $0x96, %ymm19, %ymm16, %ymm28 # ymm28 = ymm28 ^ ymm16 ^ ymm19
        vpternlogq $0x96, %ymm15, %ymm17, %ymm28 # ymm28 = ymm28 ^ ymm17 ^ ymm15
        vmovdqa64 %ymm24, %ymm29
        vpternlogq $0x96, %ymm20, %ymm22, %ymm29 # ymm29 = ymm29 ^ ymm22 ^ ymm20
        vpternlogq $0x96, %ymm21, %ymm23, %ymm29 # ymm29 = ymm29 ^ ymm23 ^ ymm21
        vprolq $0x1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0 # ymm0 = ymm0 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm3 # ymm3 = ymm3 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm1 # ymm1 = ymm1 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm4 # ymm4 = ymm4 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm2 # ymm2 = ymm2 ^ ymm29 ^ ymm30
        vprolq $0x1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm6 # ymm6 = ymm6 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm9 # ymm9 = ymm9 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm7 # ymm7 = ymm7 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm5 # ymm5 = ymm5 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm8 # ymm8 = ymm8 ^ ymm25 ^ ymm30
        vprolq $0x1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm12 # ymm12 = ymm12 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm10 # ymm10 = ymm10 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm13 # ymm13 = ymm13 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm11 # ymm11 = ymm11 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm14 # ymm14 = ymm14 ^ ymm26 ^ ymm30
        vprolq $0x1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm18 # ymm18 = ymm18 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm16 # ymm16 = ymm16 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm19 # ymm19 = ymm19 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm17 # ymm17 = ymm17 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm15 # ymm15 = ymm15 ^ ymm27 ^ ymm30
        vprolq $0x1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm24 # ymm24 = ymm24 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm22 # ymm22 = ymm22 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm20 # ymm20 = ymm20 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm23 # ymm23 = ymm23 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm21 # ymm21 = ymm21 ^ ymm28 ^ ymm30
        vprolq $0x24, %ymm3, %ymm3
        vprolq $0x3, %ymm1, %ymm1
        vprolq $0x29, %ymm4, %ymm4
        vprolq $0x12, %ymm2, %ymm2
        vprolq $0x1, %ymm6, %ymm6
        vprolq $0x2c, %ymm9, %ymm9
        vprolq $0xa, %ymm7, %ymm7
        vprolq $0x2d, %ymm5, %ymm5
        vprolq $0x2, %ymm8, %ymm8
        vprolq $0x3e, %ymm12, %ymm12
        vprolq $0x6, %ymm10, %ymm10
        vprolq $0x2b, %ymm13, %ymm13
        vprolq $0xf, %ymm11, %ymm11
        vprolq $0x3d, %ymm14, %ymm14
        vprolq $0x1c, %ymm18, %ymm18
        vprolq $0x37, %ymm16, %ymm16
        vprolq $0x19, %ymm19, %ymm19
        vprolq $0x15, %ymm17, %ymm17
        vprolq $0x38, %ymm15, %ymm15
        vprolq $0x1b, %ymm24, %ymm24
        vprolq $0x14, %ymm22, %ymm22
        vprolq $0x27, %ymm20, %ymm20
        vprolq $0x8, %ymm23, %ymm23
        vprolq $0xe, %ymm21, %ymm21
        vmovdqa64 %ymm0, %ymm30
        vmovdqa64 %ymm9, %ymm31
        vpternlogq $0xd2, %ymm13, %ymm9, %ymm0 # ymm0 = ymm0 ^ (ymm13 & ~ymm9)
        vpxorq 0x8(%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm17, %ymm13, %ymm9 # ymm9 = ymm9 ^ (ymm17 & ~ymm13)
        vpternlogq $0xd2, %ymm21, %ymm17, %ymm13 # ymm13 = ymm13 ^ (ymm21 & ~ymm17)
        vpternlogq $0xd2, %ymm30, %ymm21, %ymm17 # ymm17 = ymm17 ^ (ymm30 & ~ymm21)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm21 # ymm21 = ymm21 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm18, %ymm30
        vmovdqa64 %ymm22, %ymm31
        vpternlogq $0xd2, %ymm1, %ymm22, %ymm18 # ymm18 = ymm18 ^ (ymm1 & ~ymm22)
        vpternlogq $0xd2, %ymm5, %ymm1, %ymm22 # ymm22 = ymm22 ^ (ymm5 & ~ymm1)
        vpternlogq $0xd2, %ymm14, %ymm5, %ymm1 # ymm1 = ymm1 ^ (ymm14 & ~ymm5)
        vpternlogq $0xd2, %ymm30, %ymm14, %ymm5 # ymm5 = ymm5 ^ (ymm30 & ~ymm14)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm14 # ymm14 = ymm14 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm6, %ymm30
        vmovdqa64 %ymm10, %ymm31
        vpternlogq $0xd2, %ymm19, %ymm10, %ymm6 # ymm6 = ymm6 ^ (ymm19 & ~ymm10)
        vpternlogq $0xd2, %ymm23, %ymm19, %ymm10 # ymm10 = ymm10 ^ (ymm23 & ~ymm19)
        vpternlogq $0xd2, %ymm2, %ymm23, %ymm19 # ymm19 = ymm19 ^ (ymm2 & ~ymm23)
        vpternlogq $0xd2, %ymm30, %ymm2, %ymm23 # ymm23 = ymm23 ^ (ymm30 & ~ymm2)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm2 # ymm2 = ymm2 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm24, %ymm30
        vmovdqa64 %ymm3, %ymm31
        vpternlogq $0xd2, %ymm7, %ymm3, %ymm24 # ymm24 = ymm24 ^ (ymm7 & ~ymm3)
        vpternlogq $0xd2, %ymm11, %ymm7, %ymm3 # ymm3 = ymm3 ^ (ymm11 & ~ymm7)
        vpternlogq $0xd2, %ymm15, %ymm11, %ymm7 # ymm7 = ymm7 ^ (ymm15 & ~ymm11)
        vpternlogq $0xd2, %ymm30, %ymm15, %ymm11 # ymm11 = ymm11 ^ (ymm30 & ~ymm15)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm15 # ymm15 = ymm15 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm12, %ymm30
        vmovdqa64 %ymm16, %ymm31
        vpternlogq $0xd2, %ymm20, %ymm16, %ymm12 # ymm12 = ymm12 ^ (ymm20 & ~ymm16)
        vpternlogq $0xd2, %ymm4, %ymm20, %ymm16 # ymm16 = ymm16 ^ (ymm4 & ~ymm20)
        vpternlogq $0xd2, %ymm8, %ymm4, %ymm20 # ymm20 = ymm20 ^ (ymm8 & ~ymm4)
        vpternlogq $0xd2, %ymm30, %ymm8, %ymm4 # ymm4 = ymm4 ^ (ymm30 & ~ymm8)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm8 # ymm8 = ymm8 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm0, %ymm25
        vpternlogq $0x96, %ymm6, %ymm18, %ymm25 # ymm25 = ymm25 ^ ymm18 ^ ymm6
        vpternlogq $0x96, %ymm12, %ymm24, %ymm25 # ymm25 = ymm25 ^ ymm24 ^ ymm12
        vmovdqa64 %ymm9, %ymm26
        vpternlogq $0x96, %ymm10, %ymm22, %ymm26 # ymm26 = ymm26 ^ ymm22 ^ ymm10
        vpternlogq $0x96, %ymm16, %ymm3, %ymm26 # ymm26 = ymm26 ^ ymm3 ^ ymm16
        vmovdqa64 %ymm13, %ymm27
        vpternlogq $0x96, %ymm19, %ymm1, %ymm27 # ymm27 = ymm27 ^ ymm1 ^ ymm19
        vpternlogq $0x96, %ymm20, %ymm7, %ymm27 # ymm27 = ymm27 ^ ymm7 ^ ymm20
        vmovdqa64 %ymm17, %ymm28
        vpternlogq $0x96, %ymm23, %ymm5, %ymm28 # ymm28 = ymm28 ^ ymm5 ^ ymm23
        vpternlogq $0x96, %ymm4, %ymm11, %ymm28 # ymm28 = ymm28 ^ ymm11 ^ ymm4
        vmovdqa64 %ymm21, %ymm29
        vpternlogq $0x96, %ymm2, %ymm14, %ymm29 # ymm29 = ymm29 ^ ymm14 ^ ymm2
        vpternlogq $0x96, %ymm8, %ymm15, %ymm29 # ymm29 = ymm29 ^ ymm15 ^ ymm8
        vprolq $0x1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0 # ymm0 = ymm0 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm18 # ymm18 = ymm18 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm6 # ymm6 = ymm6 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm24 # ymm24 = ymm24 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm12 # ymm12 = ymm12 ^ ymm29 ^ ymm30
        vprolq $0x1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm9 # ymm9 = ymm9 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm22 # ymm22 = ymm22 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm10 # ymm10 = ymm10 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm3 # ymm3 = ymm3 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm16 # ymm16 = ymm16 ^ ymm25 ^ ymm30
        vprolq $0x1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm13 # ymm13 = ymm13 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm1 # ymm1 = ymm1 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm19 # ymm19 = ymm19 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm7 # ymm7 = ymm7 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm20 # ymm20 = ymm20 ^ ymm26 ^ ymm30
        vprolq $0x1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm17 # ymm17 = ymm17 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm5 # ymm5 = ymm5 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm23 # ymm23 = ymm23 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm11 # ymm11 = ymm11 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm4 # ymm4 = ymm4 ^ ymm27 ^ ymm30
        vprolq $0x1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm21 # ymm21 = ymm21 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm14 # ymm14 = ymm14 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm2 # ymm2 = ymm2 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm15 # ymm15 = ymm15 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm8 # ymm8 = ymm8 ^ ymm28 ^ ymm30
        vprolq $0x24, %ymm18, %ymm18
        vprolq $0x3, %ymm6, %ymm6
        vprolq $0x29, %ymm24, %ymm24
        vprolq $0x12, %ymm12, %ymm12
        vprolq $0x1, %ymm9, %ymm9
        vprolq $0x2c, %ymm22, %ymm22
        vprolq $0xa, %ymm10, %ymm10
        vprolq $0x2d, %ymm3, %ymm3
        vprolq $0x2, %ymm16, %ymm16
        vprolq $0x3e, %ymm13, %ymm13
        vprolq $0x6, %ymm1, %ymm1
        vprolq $0x2b, %ymm19, %ymm19
        vprolq $0xf, %ymm7, %ymm7
        vprolq $0x3d, %ymm20, %ymm20
        vprolq $0x1c, %ymm17, %ymm17
        vprolq $0x37, %ymm5, %ymm5
        vprolq $0x19, %ymm23, %ymm23
        vprolq $0x15, %ymm11, %ymm11
        vprolq $0x38, %ymm4, %ymm4
        vprolq $0x1b, %ymm21, %ymm21
        vprolq $0x14, %ymm14, %ymm14
        vprolq $0x27, %ymm2, %ymm2
        vprolq $0x8, %ymm15, %ymm15
        vprolq $0xe, %ymm8, %ymm8
        vmovdqa64 %ymm0, %ymm30
        vmovdqa64 %ymm22, %ymm31
        vpternlogq $0xd2, %ymm19, %ymm22, %ymm0 # ymm0 = ymm0 ^ (ymm19 & ~ymm22)
        vpxorq 0x10(%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm11, %ymm19, %ymm22 # ymm22 = ymm22 ^ (ymm11 & ~ymm19)
        vpternlogq $0xd2, %ymm8, %ymm11, %ymm19 # ymm19 = ymm19 ^ (ymm8 & ~ymm11)
        vpternlogq $0xd2, %ymm30, %ymm8, %ymm11 # ymm11 = ymm11 ^ (ymm30 & ~ymm8)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm8 # ymm8 = ymm8 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm17, %ymm30
        vmovdqa64 %ymm14, %ymm31
        vpternlogq $0xd2, %ymm6, %ymm14, %ymm17 # ymm17 = ymm17 ^ (ymm6 & ~ymm14)
        vpternlogq $0xd2, %ymm3, %ymm6, %ymm14 # ymm14 = ymm14 ^ (ymm3 & ~ymm6)
        vpternlogq $0xd2, %ymm20, %ymm3, %ymm6 # ymm6 = ymm6 ^ (ymm20 & ~ymm3)
        vpternlogq $0xd2, %ymm30, %ymm20, %ymm3 # ymm3 = ymm3 ^ (ymm30 & ~ymm20)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm20 # ymm20 = ymm20 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm9, %ymm30
        vmovdqa64 %ymm1, %ymm31
        vpternlogq $0xd2, %ymm23, %ymm1, %ymm9 # ymm9 = ymm9 ^ (ymm23 & ~ymm1)
        vpternlogq $0xd2, %ymm15, %ymm23, %ymm1 # ymm1 = ymm1 ^ (ymm15 & ~ymm23)
        vpternlogq $0xd2, %ymm12, %ymm15, %ymm23 # ymm23 = ymm23 ^ (ymm12 & ~ymm15)
        vpternlogq $0xd2, %ymm30, %ymm12, %ymm15 # ymm15 = ymm15 ^ (ymm30 & ~ymm12)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm12 # ymm12 = ymm12 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm21, %ymm30
        vmovdqa64 %ymm18, %ymm31
        vpternlogq $0xd2, %ymm10, %ymm18, %ymm21 # ymm21 = ymm21 ^ (ymm10 & ~ymm18)
        vpternlogq $0xd2, %ymm7, %ymm10, %ymm18 # ymm18 = ymm18 ^ (ymm7 & ~ymm10)
        vpternlogq $0xd2, %ymm4, %ymm7, %ymm10 # ymm10 = ymm10 ^ (ymm4 & ~ymm7)
        vpternlogq $0xd2, %ymm30, %ymm4, %ymm7 # ymm7 = ymm7 ^ (ymm30 & ~ymm4)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm4 # ymm4 = ymm4 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm13, %ymm30
        vmovdqa64 %ymm5, %ymm31
        vpternlogq $0xd2, %ymm2, %ymm5, %ymm13 # ymm13 = ymm13 ^ (ymm2 & ~ymm5)
        vpternlogq $0xd2, %ymm24, %ymm2, %ymm5 # ymm5 = ymm5 ^ (ymm24 & ~ymm2)
        vpternlogq $0xd2, %ymm16, %ymm24, %ymm2 # ymm2 = ymm2 ^ (ymm16 & ~ymm24)
        vpternlogq $0xd2, %ymm30, %ymm16, %ymm24 # ymm24 = ymm24 ^ (ymm30 & ~ymm16)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm16 # ymm16 = ymm16 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm0, %ymm25
        vpternlogq $0x96, %ymm9, %ymm17, %ymm25 # ymm25 = ymm25 ^ ymm17 ^ ymm9
        vpternlogq $0x96, %ymm13, %ymm21, %ymm25 # ymm25 = ymm25 ^ ymm21 ^ ymm13
        vmovdqa64 %ymm22, %ymm26
        vpternlogq $0x96, %ymm1, %ymm14, %ymm26 # ymm26 = ymm26 ^ ymm14 ^ ymm1
        vpternlogq $0x96, %ymm5, %ymm18, %ymm26 # ymm26 = ymm26 ^ ymm18 ^ ymm5
        vmovdqa64 %ymm19, %ymm27
        vpternlogq $0x96, %ymm23, %ymm6, %ymm27 # ymm27 = ymm27 ^ ymm6 ^ ymm23
        vpternlogq $0x96, %ymm2, %ymm10, %ymm27 # ymm27 = ymm27 ^ ymm10 ^ ymm2
        vmovdqa64 %ymm11, %ymm28
        vpternlogq $0x96, %ymm15, %ymm3, %ymm28 # ymm28 = ymm28 ^ ymm3 ^ ymm15
        vpternlogq $0x96, %ymm24, %ymm7, %ymm28 # ymm28 = ymm28 ^ ymm7 ^ ymm24
        vmovdqa64 %ymm8, %ymm29
        vpternlogq $0x96, %ymm12, %ymm20, %ymm29 # ymm29 = ymm29 ^ ymm20 ^ ymm12
        vpternlogq $0x96, %ymm16, %ymm4, %ymm29 # ymm29 = ymm29 ^ ymm4 ^ ymm16
        vprolq $0x1, %ymm26, %ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm0 # ymm0 = ymm0 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm17 # ymm17 = ymm17 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm9 # ymm9 = ymm9 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm21 # ymm21 = ymm21 ^ ymm29 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm29, %ymm13 # ymm13 = ymm13 ^ ymm29 ^ ymm30
        vprolq $0x1, %ymm27, %ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm22 # ymm22 = ymm22 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm14 # ymm14 = ymm14 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm1 # ymm1 = ymm1 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm18 # ymm18 = ymm18 ^ ymm25 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm25, %ymm5 # ymm5 = ymm5 ^ ymm25 ^ ymm30
        vprolq $0x1, %ymm28, %ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm19 # ymm19 = ymm19 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm6 # ymm6 = ymm6 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm23 # ymm23 = ymm23 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm10 # ymm10 = ymm10 ^ ymm26 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm26, %ymm2 # ymm2 = ymm2 ^ ymm26 ^ ymm30
        vprolq $0x1, %ymm29, %ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm11 # ymm11 = ymm11 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm3 # ymm3 = ymm3 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm15 # ymm15 = ymm15 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm7 # ymm7 = ymm7 ^ ymm27 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm27, %ymm24 # ymm24 = ymm24 ^ ymm27 ^ ymm30
        vprolq $0x1, %ymm25, %ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm8 # ymm8 = ymm8 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm20 # ymm20 = ymm20 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm12 # ymm12 = ymm12 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm4 # ymm4 = ymm4 ^ ymm28 ^ ymm30
        vpternlogq $0x96, %ymm30, %ymm28, %ymm16 # ymm16 = ymm16 ^ ymm28 ^ ymm30
        vprolq $0x24, %ymm17, %ymm17
        vprolq $0x3, %ymm9, %ymm9
        vprolq $0x29, %ymm21, %ymm21
        vprolq $0x12, %ymm13, %ymm13
        vprolq $0x1, %ymm22, %ymm22
        vprolq $0x2c, %ymm14, %ymm14
        vprolq $0xa, %ymm1, %ymm1
        vprolq $0x2d, %ymm18, %ymm18
        vprolq $0x2, %ymm5, %ymm5
        vprolq $0x3e, %ymm19, %ymm19
        vprolq $0x6, %ymm6, %ymm6
        vprolq $0x2b, %ymm23, %ymm23
        vprolq $0xf, %ymm10, %ymm10
        vprolq $0x3d, %ymm2, %ymm2
        vprolq $0x1c, %ymm11, %ymm11
        vprolq $0x37, %ymm3, %ymm3
        vprolq $0x19, %ymm15, %ymm15
        vprolq $0x15, %ymm7, %ymm7
        vprolq $0x38, %ymm24, %ymm24
        vprolq $0x1b, %ymm8, %ymm8
        vprolq $0x14, %ymm20, %ymm20
        vprolq $0x27, %ymm12, %ymm12
        vprolq $0x8, %ymm4, %ymm4
        vprolq $0xe, %ymm16, %ymm16
        vmovdqa64 %ymm0, %ymm30
        vmovdqa64 %ymm14, %ymm31
        vpternlogq $0xd2, %ymm23, %ymm14, %ymm0 # ymm0 = ymm0 ^ (ymm23 & ~ymm14)
        vpxorq 0x18(%rsi){1to4}, %ymm0, %ymm0
        vpternlogq $0xd2, %ymm7, %ymm23, %ymm14 # ymm14 = ymm14 ^ (ymm7 & ~ymm23)
        vpternlogq $0xd2, %ymm16, %ymm7, %ymm23 # ymm23 = ymm23 ^ (ymm16 & ~ymm7)
        vpternlogq $0xd2, %ymm30, %ymm16, %ymm7 # ymm7 = ymm7 ^ (ymm30 & ~ymm16)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm16 # ymm16 = ymm16 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm11, %ymm30
        vmovdqa64 %ymm20, %ymm31
        vpternlogq $0xd2, %ymm9, %ymm20, %ymm11 # ymm11 = ymm11 ^ (ymm9 & ~ymm20)
        vpternlogq $0xd2, %ymm18, %ymm9, %ymm20 # ymm20 = ymm20 ^ (ymm18 & ~ymm9)
        vpternlogq $0xd2, %ymm2, %ymm18, %ymm9 # ymm9 = ymm9 ^ (ymm2 & ~ymm18)
        vpternlogq $0xd2, %ymm30, %ymm2, %ymm18 # ymm18 = ymm18 ^ (ymm30 & ~ymm2)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm2 # ymm2 = ymm2 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm22, %ymm30
        vmovdqa64 %ymm6, %ymm31
        vpternlogq $0xd2, %ymm15, %ymm6, %ymm22 # ymm22 = ymm22 ^ (ymm15 & ~ymm6)
        vpternlogq $0xd2, %ymm4, %ymm15, %ymm6 # ymm6 = ymm6 ^ (ymm4 & ~ymm15)
        vpternlogq $0xd2, %ymm13, %ymm4, %ymm15 # ymm15 = ymm15 ^ (ymm13 & ~ymm4)
        vpternlogq $0xd2, %ymm30, %ymm13, %ymm4 # ymm4 = ymm4 ^ (ymm30 & ~ymm13)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm13 # ymm13 = ymm13 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm8, %ymm30
        vmovdqa64 %ymm17, %ymm31
        vpternlogq $0xd2, %ymm1, %ymm17, %ymm8 # ymm8 = ymm8 ^ (ymm1 & ~ymm17)
        vpternlogq $0xd2, %ymm10, %ymm1, %ymm17 # ymm17 = ymm17 ^ (ymm10 & ~ymm1)
        vpternlogq $0xd2, %ymm24, %ymm10, %ymm1 # ymm1 = ymm1 ^ (ymm24 & ~ymm10)
        vpternlogq $0xd2, %ymm30, %ymm24, %ymm10 # ymm10 = ymm10 ^ (ymm30 & ~ymm24)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm24 # ymm24 = ymm24 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm19, %ymm30
        vmovdqa64 %ymm3, %ymm31
        vpternlogq $0xd2, %ymm12, %ymm3, %ymm19 # ymm19 = ymm19 ^ (ymm12 & ~ymm3)
        vpternlogq $0xd2, %ymm21, %ymm12, %ymm3 # ymm3 = ymm3 ^ (ymm21 & ~ymm12)
        vpternlogq $0xd2, %ymm5, %ymm21, %ymm12 # ymm12 = ymm12 ^ (ymm5 & ~ymm21)
        vpternlogq $0xd2, %ymm30, %ymm5, %ymm21 # ymm21 = ymm21 ^ (ymm30 & ~ymm5)
        vpternlogq $0xd2, %ymm31, %ymm30, %ymm5 # ymm5 = ymm5 ^ (ymm31 & ~ymm30)
        vmovdqa64 %ymm1, %ymm30
        vmovdqa %ymm14, %ymm1
        vmovdqa %ymm13, %ymm14
        vmovdqa %ymm4, %ymm13
        vmovdqa64 %ymm16, %ymm4
        vmovdqa64 %ymm17, %ymm16
        vmovdqa64 %ymm30, %ymm17
        vmovdqa64 %ymm2, %ymm30
        vmovdqa64 %ymm23, %ymm2
        vmovdqa64 %ymm21, %ymm23
        vmovdqa64 %ymm3, %ymm21
        vmovdqa %ymm7, %ymm3
        vmovdqa %ymm9, %ymm7
        vmovdqa64 %ymm30, %ymm9
        vmovdqa64 %ymm5, %ymm30
        vmovdqa %ymm11, %ymm5
        vmovdqa %ymm6, %ymm11
        vmovdqa64 %ymm20, %ymm6
        vmovdqa64 %ymm19, %ymm20
        vmovdqa64 %ymm24, %ymm19
        vmovdqa64 %ymm30, %ymm24
        vmovdqa64 %ymm8, %ymm30
        vmovdqa64 %ymm18, %ymm8
        vmovdqa64 %ymm10, %ymm18
        vmovdqa64 %ymm22, %ymm10
        vmovdqa64 %ymm12, %ymm22
        vmovdqa %ymm15, %ymm12
        vmovdqa64 %ymm30, %ymm15
        addq $0x20, %rsi
        cmpq %rax, %rsi
        jne Lmlk_keccak_f1600_x4_avx512_loop
        vpunpcklqdq %ymm1, %ymm0, %ymm25 # ymm25 = ymm0[0],ymm1[0],ymm0[2],ymm1[2]
        vpunpckhqdq %ymm1, %ymm0, %ymm26 # ymm26 = ymm0[1],ymm1[1],ymm0[3],ymm1[3]
        vpunpcklqdq %ymm3, %ymm2, %ymm27 # ymm27 = ymm2[0],ymm3[0],ymm2[2],ymm3[2]
        vpunpckhqdq %ymm3, %ymm2, %ymm28 # ymm28 = ymm2[1],ymm3[1],ymm2[3],ymm3[3]
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29 # ymm29 = ymm25[0,1],ymm27[0,1]
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30 # ymm30 = ymm26[0,1],ymm28[0,1]
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31 # ymm31 = ymm25[2,3],ymm27[2,3]
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25 # ymm25 = ymm26[2,3],ymm28[2,3]
        vmovdqu64 %ymm29, (%rdi)
        vmovdqu64 %ymm30, 0xc8(%rdi)
        vmovdqu64 %ymm31, 0x190(%rdi)
        vmovdqu64 %ymm25, 0x258(%rdi)
        vpunpcklqdq %ymm5, %ymm4, %ymm25 # ymm25 = ymm4[0],ymm5[0],ymm4[2],ymm5[2]
        vpunpckhqdq %ymm5, %ymm4, %ymm26 # ymm26 = ymm4[1],ymm5[1],ymm4[3],ymm5[3]
        vpunpcklqdq %ymm7, %ymm6, %ymm27 # ymm27 = ymm6[0],ymm7[0],ymm6[2],ymm7[2]
        vpunpckhqdq %ymm7, %ymm6, %ymm28 # ymm28 = ymm6[1],ymm7[1],ymm6[3],ymm7[3]
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29 # ymm29 = ymm25[0,1],ymm27[0,1]
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30 # ymm30 = ymm26[0,1],ymm28[0,1]
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31 # ymm31 = ymm25[2,3],ymm27[2,3]
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25 # ymm25 = ymm26[2,3],ymm28[2,3]
        vmovdqu64 %ymm29, 0x20(%rdi)
        vmovdqu64 %ymm30, 0xe8(%rdi)
        vmovdqu64 %ymm31, 0x1b0(%rdi)
        vmovdqu64 %ymm25, 0x278(%rdi)
        vpunpcklqdq %ymm9, %ymm8, %ymm25 # ymm25 = ymm8[0],ymm9[0],ymm8[2],ymm9[2]
        vpunpckhqdq %ymm9, %ymm8, %ymm26 # ymm26 = ymm8[1],ymm9[1],ymm8[3],ymm9[3]
        vpunpcklqdq %ymm11, %ymm10, %ymm27 # ymm27 = ymm10[0],ymm11[0],ymm10[2],ymm11[2]
        vpunpckhqdq %ymm11, %ymm10, %ymm28 # ymm28 = ymm10[1],ymm11[1],ymm10[3],ymm11[3]
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29 # ymm29 = ymm25[0,1],ymm27[0,1]
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30 # ymm30 = ymm26[0,1],ymm28[0,1]
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31 # ymm31 = ymm25[2,3],ymm27[2,3]
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25 # ymm25 = ymm26[2,3],ymm28[2,3]
        vmovdqu64 %ymm29, 0x40(%rdi)
        vmovdqu64 %ymm30, 0x108(%rdi)
        vmovdqu64 %ymm31, 0x1d0(%rdi)
        vmovdqu64 %ymm25, 0x298(%rdi)
        vpunpcklqdq %ymm13, %ymm12, %ymm25 # ymm25 = ymm12[0],ymm13[0],ymm12[2],ymm13[2]
        vpunpckhqdq %ymm13, %ymm12, %ymm26 # ymm26 = ymm12[1],ymm13[1],ymm12[3],ymm13[3]
        vpunpcklqdq %ymm15, %ymm14, %ymm27 # ymm27 = ymm14[0],ymm15[0],ymm14[2],ymm15[2]
        vpunpckhqdq %ymm15, %ymm14, %ymm28 # ymm28 = ymm14[1],ymm15[1],ymm14[3],ymm15[3]
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29 # ymm29 = ymm25[0,1],ymm27[0,1]
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30 # ymm30 = ymm26[0,1],ymm28[0,1]
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31 # ymm31 = ymm25[2,3],ymm27[2,3]
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25 # ymm25 = ymm26[2,3],ymm28[2,3]
        vmovdqu64 %ymm29, 0x60(%rdi)
        vmovdqu64 %ymm30, 0x128(%rdi)
        vmovdqu64 %ymm31, 0x1f0(%rdi)
        vmovdqu64 %ymm25, 0x2b8(%rdi)
        vpunpcklqdq %ymm17, %ymm16, %ymm25 # ymm25 = ymm16[0],ymm17[0],ymm16[2],ymm17[2]
        vpunpckhqdq %ymm17, %ymm16, %ymm26 # ymm26 = ymm16[1],ymm17[1],ymm16[3],ymm17[3]
        vpunpcklqdq %ymm19, %ymm18, %ymm27 # ymm27 = ymm18[0],ymm19[0],ymm18[2],ymm19[2]
        vpunpckhqdq %ymm19, %ymm18, %ymm28 # ymm28 = ymm18[1],ymm19[1],ymm18[3],ymm19[3]
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29 # ymm29 = ymm25[0,1],ymm27[0,1]
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30 # ymm30 = ymm26[0,1],ymm28[0,1]
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31 # ymm31 = ymm25[2,3],ymm27[2,3]
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25 # ymm25 = ymm26[2,3],ymm28[2,3]
        vmovdqu64 %ymm29, 0x80(%rdi)
        vmovdqu64 %ymm30, 0x148(%rdi)
        vmovdqu64 %ymm31, 0x210(%rdi)
        vmovdqu64 %ymm25, 0x2d8(%rdi)
        vpunpcklqdq %ymm21, %ymm20, %ymm25 # ymm25 = ymm20[0],ymm21[0],ymm20[2],ymm21[2]
        vpunpckhqdq %ymm21, %ymm20, %ymm26 # ymm26 = ymm20[1],ymm21[1],ymm20[3],ymm21[3]
        vpunpcklqdq %ymm23, %ymm22, %ymm27 # ymm27 = ymm22[0],ymm23[0],ymm22[2],ymm23[2]
        vpunpckhqdq %ymm23, %ymm22, %ymm28 # ymm28 = ymm22[1],ymm23[1],ymm22[3],ymm23[3]
        vshufi64x2 $0x0, %ymm27, %ymm25, %ymm29 # ymm29 = ymm25[0,1],ymm27[0,1]
        vshufi64x2 $0x0, %ymm28, %ymm26, %ymm30 # ymm30 = ymm26[0,1],ymm28[0,1]
        vshufi64x2 $0x3, %ymm27, %ymm25, %ymm31 # ymm31 = ymm25[2,3],ymm27[2,3]
        vshufi64x2 $0x3, %ymm28, %ymm26, %ymm25 # ymm25 = ymm26[2,3],ymm28[2,3]
        vmovdqu64 %ymm29, 0xa0(%rdi)
        vmovdqu64 %ymm30, 0x168(%rdi)
        vmovdqu64 %ymm31, 0x230(%rdi)
        vmovdqu64 %ymm25, 0x2f8(%rdi)
        .byte 0x62, 0x61, 0xfd, 0x08, 0x7e, 0x47, 0x18 /* vmovq %xmm24, 0xc0(%rdi) */
        vpextrq $0x1, %xmm24, 0x188(%rdi)
        vextracti32x4 $0x1, %ymm24, %xmm25
        .byte 0x62, 0x61, 0xfd, 0x08, 0x7e, 0x4f, 0x4a /* vmovq %xmm25, 0x250(%rdi) */
        vpextrq $0x1, %xmm25, 0x318(%rdi)
        vzeroupper
        retq
        .cfi_endproc

MLK_ASM_FN_SIZE(keccak_f1600_x4_avx512_asm)

#endif /* MLK_SYS_X86_64_AVX512 && MLK_FIPS202_X86_64_NEED_X4_AVX512 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
