/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*************************************************
 * Name:        mlk_rej_uniform_asm
 *
 * Description: Run rejection sampling on uniform random bytes to generate
 *              uniform random integers mod q
 *
 * Arguments:   - int16_t *r:          pointer to output buffer of MLKEM_N
 *                                     16-bit coefficients.
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned buflen:     length of input buffer in bytes.
 *                                     Must be a multiple of 12.
 *
 * Returns number of sampled 16-bit integers (at most MLKEM_N).
 **************************************************/
#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#define MLK_IN %rsi
#define MLK_OUT %rdi
#define MLK_LEN %rdx
#define MLK_TAB %rcx

#define MLK_CNT %rax
#define MLK_ECNT %eax
#define MLK_POS %r8

#define MLK_GOOD %r11
#define MLK_PEXT_MASK %r9
#define MLK_TABLE_IDX %r10

#define MLK_BOUND %xmm0
#define MLK_TEMP0 %xmm1
#define MLK_TEMP1 %xmm3
#define MLK_VALS %xmm2
#define MLK_SHUFFLE_OUT_MASK %xmm3
#define MLK_SHUFFLE_IN_MASK %xmm4
#define MLK_AND_MASK %xmm5

//  High level overview of the algorithm:
//  For every 96 bits (12 bytes) of the input:
//    1. Split 96 bits into eight 12-bit integers where each integer
//       occupies a corresponding 16-bit element of `MLK_VALS` xmm register,
//    2. Compute an 8-bit value `MLK_GOOD` such that
//         MLK_GOOD[i] = MLK_VALS[i] < MLKEM_Q ? 1 : 0, for i in [0, 7],
//    3. Shuffle the elements in `MLK_VALS` such that all MLK_GOOD elements
//       are ordered consecutivelly, and store them.
//
//  Notes:
//    - We exit early if we find the required number of MLK_GOOD values,
//    - We use the stack as a temporary storage and copy to the actual
//      output buffer only in the end. This is because the algorithm
//      can overwrite up to 14 bytes (we use 16B for alignment), 
//    - The implementation uses x86 SSE and BMI2 extensions.

#define MLK_STACK_SIZE (2*MLKEM_N + 16)

.text
.global MLK_ASM_NAMESPACE(rej_uniform_asm)
.balign 4
MLK_ASM_FN_SYMBOL(rej_uniform_asm)
  subq $MLK_STACK_SIZE, %rsp

  // Return if input length is 0
  xorl MLK_ECNT, MLK_ECNT
  testq MLK_LEN, MLK_LEN
  jz rej_uniform_asm_end

  // Broadcast MLKEM_Q (3329) to all 16-bit elements of bound reg.
  movq $0x0D010D010D010D01, %rax
  movq %rax, MLK_BOUND
  pinsrq $1, %rax, MLK_BOUND

  // Broadcast 12-bit mask 0xFFF to all 16-bit elements of MLK_BOUND reg.
  movq $0x0FFF0FFF0FFF0FFF, %rax
  movq %rax, MLK_AND_MASK
  pinsrq $1, %rax, MLK_AND_MASK

  // Load shuffle mask:
  //   0, 1, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8, 9, 10, 10, 11.
  movq $0x0504040302010100, %rax
  movq %rax, MLK_SHUFFLE_IN_MASK
  movq $0x0B0A0A0908070706, %rax
  pinsrq $1, %rax, MLK_SHUFFLE_IN_MASK

  movq $0, MLK_CNT // MLK_CNT counts the number of MLK_GOOD values we've found.
  movq $0, MLK_POS // MLK_POS is the current position in the input buffer.
  movq $0x5555, MLK_PEXT_MASK // 0x5555 mask to extract every second bit.

rej_uniform_asm_loop_start:
  // 1. Split 96 bits into eight 12-bit integers where each integer.
  //    We explain the algorithm by considering the lowest 64 bits of MLK_VALS.
  movdqu  (MLK_IN, MLK_POS), MLK_VALS
  //    MLK_VALS: [ 63..48 | 47..32 | 31..16 | 15..0 ]
  pshufb  MLK_SHUFFLE_IN_MASK, MLK_VALS
  //    MLK_VALS: [ 47..32 | 39..24 | 23..8 | 15..0 ]
  movdqa  MLK_VALS, MLK_TEMP1
  //    temp: [ 47..32 | 39..24 | 23..8 | 15..0 ]
  psrlw   $4, MLK_TEMP1
  //    temp: [ 47..36 | 39..28 | 23..12 | 15..4 ]
  pblendw $0xAA, MLK_TEMP1, MLK_VALS
  //    MLK_VALS: [ 47..36 | 39..24 | 23..12 | 15..0]
  pand    MLK_AND_MASK, MLK_VALS
  //    MLK_VALS: [ 47..36 | 35..24 | 23..12 | 12..0]

  // 2. Compute an 8-bit value `MLK_GOOD` such that
  //      MLK_GOOD[i] = MLK_VALS[i] < MLKEM_Q ? 1 : 0, for i in [0, 7],
  movdqa   MLK_BOUND, MLK_TEMP0
  pcmpgtw  MLK_VALS, MLK_TEMP0
  pmovmskb MLK_TEMP0, MLK_GOOD
  pext     MLK_PEXT_MASK, MLK_GOOD, MLK_GOOD

  // 3. Shuffle the elements in `MLK_VALS` such that all MLK_GOOD elements
  //    are ordered consecutivelly, and store them.
  movq   MLK_GOOD, MLK_TABLE_IDX
  shl    $4, MLK_TABLE_IDX
  movdqu (MLK_TAB, MLK_TABLE_IDX), MLK_SHUFFLE_OUT_MASK
  pshufb MLK_SHUFFLE_OUT_MASK, MLK_VALS
  movdqu MLK_VALS, (%rsp, MLK_CNT, 2)

  // Update the counter and check if we are done.
  popcnt MLK_GOOD, MLK_GOOD
  addq MLK_GOOD, MLK_CNT

  cmpq $256, MLK_CNT
  jnb rej_uniform_asm_final_copy

  addq $12, MLK_POS
  cmpq MLK_POS, MLK_LEN
  ja rej_uniform_asm_loop_start

rej_uniform_asm_final_copy:
  // Copy up to 256 values to the output: min(MLK_CNT, 256).
  mov   $256, %rcx
  cmp   $256, MLK_CNT
  cmova %rcx, MLK_CNT

  movq %rsp, %rsi
  movq MLK_CNT, %rcx
  shlq $1, %rcx
  rep  movsb

rej_uniform_asm_end:

  addq $MLK_STACK_SIZE, %rsp
  ret

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef MLK_IN
#undef MLK_OUT
#undef MLK_LEN
#undef MLK_TAB
#undef MLK_CNT
#undef MLK_ECNT
#undef MLK_POS
#undef MLK_GOOD
#undef MLK_PEXT_MASK
#undef MLK_TABLE_IDX
#undef MLK_BOUND
#undef MLK_TEMP0
#undef MLK_TEMP1
#undef MLK_VALS
#undef MLK_SHUFFLE_OUT_MASK
#undef MLK_SHUFFLE_IN_MASK
#undef MLK_AND_MASK
#undef MLK_STACK_SIZE

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
        */
