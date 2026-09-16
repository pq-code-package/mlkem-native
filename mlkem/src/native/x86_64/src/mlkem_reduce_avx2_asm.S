/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [REF_AVX2]
 *   CRYSTALS-Kyber optimized AVX2 implementation
 *   Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/kyber/tree/main/avx2
 */

/*
 * This file is derived from the public domain
 * AVX2 Kyber implementation @[REF_AVX2].
 *
 * Changes:
 * - Replace Barrett reduction and conditional subtraction by the
 *   plantard_red16 sequence from fq.inc, which produces outputs in
 *   [0,1,...,q-1] directly, matching the semantics of mlk_poly_reduce().
 *   Its constants are those of the multiplier 1: W = (-2^32 mod q) * q^-1
 *   mod 2^32 = 0x0013afb8, split as H = 0x0014 and L = 0xafb8, bias 2.
 * - Use a macro instead of a local function call.
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/*yaml
  Name: reduce_avx2_asm
  Description: x86_64 AVX2 modular reduction
  Signature: void mlk_reduce_avx2_asm(int16_t *r)
  ABI:
    Architecture: x86_64
    CallingConvention: SysV
    Features: [AVX2]
    rdi:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t *r
      description: Input/output polynomial (256 x int16_t)
*/


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/x86_64/src/mlkem_reduce_avx2_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
.global MLK_ASM_NAMESPACE(reduce_avx2_asm)
MLK_ASM_FN_SYMBOL(reduce_avx2_asm)

        .cfi_startproc
        movl $0xd010d01, %eax        # imm = 0xD010D01
        vmovd %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movl $0xafb8afb8, %eax       # imm = 0xAFB8AFB8
        vmovd %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1
        movl $0x140014, %eax         # imm = 0x140014
        vmovd %eax, %xmm2
        vpbroadcastd %xmm2, %ymm2
        movl $0x20002, %eax          # imm = 0x20002
        vmovd %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3
        vmovdqa (%rdi), %ymm4
        vmovdqa 0x20(%rdi), %ymm5
        vmovdqa 0x40(%rdi), %ymm6
        vmovdqa 0x60(%rdi), %ymm7
        vmovdqa 0x80(%rdi), %ymm8
        vmovdqa 0xa0(%rdi), %ymm9
        vmovdqa 0xc0(%rdi), %ymm10
        vmovdqa 0xe0(%rdi), %ymm11
        vpmulhw %ymm1, %ymm4, %ymm12
        vpmullw %ymm2, %ymm4, %ymm4
        vpaddw %ymm12, %ymm4, %ymm4
        vpaddw %ymm3, %ymm4, %ymm4
        vpmulhuw %ymm0, %ymm4, %ymm4
        vpmulhw %ymm1, %ymm5, %ymm12
        vpmullw %ymm2, %ymm5, %ymm5
        vpaddw %ymm12, %ymm5, %ymm5
        vpaddw %ymm3, %ymm5, %ymm5
        vpmulhuw %ymm0, %ymm5, %ymm5
        vpmulhw %ymm1, %ymm6, %ymm12
        vpmullw %ymm2, %ymm6, %ymm6
        vpaddw %ymm12, %ymm6, %ymm6
        vpaddw %ymm3, %ymm6, %ymm6
        vpmulhuw %ymm0, %ymm6, %ymm6
        vpmulhw %ymm1, %ymm7, %ymm12
        vpmullw %ymm2, %ymm7, %ymm7
        vpaddw %ymm12, %ymm7, %ymm7
        vpaddw %ymm3, %ymm7, %ymm7
        vpmulhuw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm1, %ymm8, %ymm12
        vpmullw %ymm2, %ymm8, %ymm8
        vpaddw %ymm12, %ymm8, %ymm8
        vpaddw %ymm3, %ymm8, %ymm8
        vpmulhuw %ymm0, %ymm8, %ymm8
        vpmulhw %ymm1, %ymm9, %ymm12
        vpmullw %ymm2, %ymm9, %ymm9
        vpaddw %ymm12, %ymm9, %ymm9
        vpaddw %ymm3, %ymm9, %ymm9
        vpmulhuw %ymm0, %ymm9, %ymm9
        vpmulhw %ymm1, %ymm10, %ymm12
        vpmullw %ymm2, %ymm10, %ymm10
        vpaddw %ymm12, %ymm10, %ymm10
        vpaddw %ymm3, %ymm10, %ymm10
        vpmulhuw %ymm0, %ymm10, %ymm10
        vpmulhw %ymm1, %ymm11, %ymm12
        vpmullw %ymm2, %ymm11, %ymm11
        vpaddw %ymm12, %ymm11, %ymm11
        vpaddw %ymm3, %ymm11, %ymm11
        vpmulhuw %ymm0, %ymm11, %ymm11
        vmovdqa %ymm4, (%rdi)
        vmovdqa %ymm5, 0x20(%rdi)
        vmovdqa %ymm6, 0x40(%rdi)
        vmovdqa %ymm7, 0x60(%rdi)
        vmovdqa %ymm8, 0x80(%rdi)
        vmovdqa %ymm9, 0xa0(%rdi)
        vmovdqa %ymm10, 0xc0(%rdi)
        vmovdqa %ymm11, 0xe0(%rdi)
        vmovdqa 0x100(%rdi), %ymm4
        vmovdqa 0x120(%rdi), %ymm5
        vmovdqa 0x140(%rdi), %ymm6
        vmovdqa 0x160(%rdi), %ymm7
        vmovdqa 0x180(%rdi), %ymm8
        vmovdqa 0x1a0(%rdi), %ymm9
        vmovdqa 0x1c0(%rdi), %ymm10
        vmovdqa 0x1e0(%rdi), %ymm11
        vpmulhw %ymm1, %ymm4, %ymm12
        vpmullw %ymm2, %ymm4, %ymm4
        vpaddw %ymm12, %ymm4, %ymm4
        vpaddw %ymm3, %ymm4, %ymm4
        vpmulhuw %ymm0, %ymm4, %ymm4
        vpmulhw %ymm1, %ymm5, %ymm12
        vpmullw %ymm2, %ymm5, %ymm5
        vpaddw %ymm12, %ymm5, %ymm5
        vpaddw %ymm3, %ymm5, %ymm5
        vpmulhuw %ymm0, %ymm5, %ymm5
        vpmulhw %ymm1, %ymm6, %ymm12
        vpmullw %ymm2, %ymm6, %ymm6
        vpaddw %ymm12, %ymm6, %ymm6
        vpaddw %ymm3, %ymm6, %ymm6
        vpmulhuw %ymm0, %ymm6, %ymm6
        vpmulhw %ymm1, %ymm7, %ymm12
        vpmullw %ymm2, %ymm7, %ymm7
        vpaddw %ymm12, %ymm7, %ymm7
        vpaddw %ymm3, %ymm7, %ymm7
        vpmulhuw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm1, %ymm8, %ymm12
        vpmullw %ymm2, %ymm8, %ymm8
        vpaddw %ymm12, %ymm8, %ymm8
        vpaddw %ymm3, %ymm8, %ymm8
        vpmulhuw %ymm0, %ymm8, %ymm8
        vpmulhw %ymm1, %ymm9, %ymm12
        vpmullw %ymm2, %ymm9, %ymm9
        vpaddw %ymm12, %ymm9, %ymm9
        vpaddw %ymm3, %ymm9, %ymm9
        vpmulhuw %ymm0, %ymm9, %ymm9
        vpmulhw %ymm1, %ymm10, %ymm12
        vpmullw %ymm2, %ymm10, %ymm10
        vpaddw %ymm12, %ymm10, %ymm10
        vpaddw %ymm3, %ymm10, %ymm10
        vpmulhuw %ymm0, %ymm10, %ymm10
        vpmulhw %ymm1, %ymm11, %ymm12
        vpmullw %ymm2, %ymm11, %ymm11
        vpaddw %ymm12, %ymm11, %ymm11
        vpaddw %ymm3, %ymm11, %ymm11
        vpmulhuw %ymm0, %ymm11, %ymm11
        vmovdqa %ymm4, 0x100(%rdi)
        vmovdqa %ymm5, 0x120(%rdi)
        vmovdqa %ymm6, 0x140(%rdi)
        vmovdqa %ymm7, 0x160(%rdi)
        vmovdqa %ymm8, 0x180(%rdi)
        vmovdqa %ymm9, 0x1a0(%rdi)
        vmovdqa %ymm10, 0x1c0(%rdi)
        vmovdqa %ymm11, 0x1e0(%rdi)
        retq
        .cfi_endproc

MLK_ASM_FN_SIZE(reduce_avx2_asm)

#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
