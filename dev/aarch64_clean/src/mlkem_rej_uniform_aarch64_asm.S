/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: rej_uniform_aarch64_asm
  Description: Run rejection sampling on uniform random bytes to generate uniform random integers mod q
  Signature: uint64_t mlk_rej_uniform_aarch64_asm(int16_t r[256], const uint8_t *buf, uint64_t buflen, const uint8_t table[4096])
  ABI:
    Architecture: aarch64
    CallingConvention: AAPCS64
    Features: [NEON]
    x0:
      type: buffer
      size_bytes: 512
      permissions: write-only
      c_parameter: int16_t r[256]
      description: Output buffer
    x1:
      type: buffer
      size_bytes: x2
      permissions: read-only
      c_parameter: const uint8_t *buf
      description: Input buffer
    x2:
      type: scalar
      c_parameter: uint64_t buflen
      description: Length of input buffer (must be multiple of 24)
      test_with: 504  # MLKEM_GEN_MATRIX_NBLOCKS * MLK_XOF_RATE
    x3:
      type: buffer
      size_bytes: 4096
      permissions: read-only
      c_parameter: const uint8_t table[4096]
      description: Lookup table
  Stack:
    bytes: 576
    description: register preservation and temporary storage
*/

#include "../../../common.h"
#if defined(MLK_SYS_AARCH64_NEON) && \
    defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

// We save the output on the stack first, and copy to the actual
// output buffer only in the end. This is because the main loop can overwrite
// by up to 62 bytes, which we account for here (we use 64 bytes for alignment).
#define STACK_SIZE (2*MLKEM_N + 64)

.macro push_stack
        sub sp, sp, #STACK_SIZE
.endm

.macro pop_stack
        add sp, sp, #STACK_SIZE
.endm

    /* Parameters */
    output                      .req x0
    buf                         .req x1
    buflen                      .req x2
    table_idx                   .req x3

    len                         .req x4

    /* Temporary output on the stack */
    xtmp                        .req x7
    xtmp0                       .req x7
    xtmp1                       .req x11
    output_tmp                  .req x7
    output_tmp_base             .req x8

    /* Number of coefficients sampled so far */
    count                       .req x9
    buf_consumed                .req x10

    /* Temporary registers */
    tmp                         .req w11
    initial_zero_count          .req x11
    final_copy_count            .req x11

    rec_idx_0                   .req x12
    rec_idx_1                   .req x13
    rec_idx_2                   .req x14
    rec_idx_3                   .req x15

    rec_idx_0_w                 .req w12
    rec_idx_1_w                 .req w13
    rec_idx_2_w                 .req w14
    rec_idx_3_w                 .req w15

    ctr0                        .req x12
    ctr1                        .req x13
    ctr2                        .req x14
    ctr3                        .req x15

    ctr0_w                      .req w12
    ctr1_w                      .req w13
    ctr2_w                      .req w14
    ctr3_w                      .req w15

    ctr01                       .req ctr0
    ctr23                       .req ctr2

    /* Vector registers */

    buf0                        .req v0
    buf0q                       .req q0
    buf1                        .req v1
    buf1q                       .req q1
    buf1d                       .req d1
    buf2                        .req v2
    buf2q                       .req q2

    tmp0                        .req v4
    tmp1                        .req v5
    tmp2                        .req v6
    tmp3                        .req v7

    sign0                       .req v4
    sign1                       .req v5
    sign2                       .req v6
    sign3                       .req v7

    val0                        .req v16
    val0q                       .req q16
    val1                        .req v17
    val1q                       .req q17
    val2                        .req v18
    val2q                       .req q18
    val3                        .req v19
    val3q                       .req q19

    t0                          .req s0
    t1                          .req s1
    t0d                         .req d0

    unpack0                     .req v20
    unpack0d                    .req d20
    unpack1                     .req v21
    unpack2                     .req v22
    unpack3                     .req v23

    table0                      .req v24
    table0q                     .req q24
    table1                      .req v25
    table1q                     .req q25
    table2                      .req v26
    table2q                     .req q26
    table3                      .req v27
    table3q                     .req q27

    packed_bits_even            .req v28
    packed_bits_odd             .req v29
    mlkem_q                     .req v30
    bits                        .req v31

    .text
    .global MLK_ASM_NAMESPACE(rej_uniform_aarch64_asm)
    .balign 4
MLK_ASM_FN_SYMBOL(rej_uniform_aarch64_asm)
    push_stack

    // Load 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80
    movz xtmp, 0x1
    movk xtmp, 0x2, lsl 16
    movk xtmp, 0x4, lsl 32
    movk xtmp, 0x8, lsl 48
    mov bits.d[0], xtmp

    movz xtmp, 0x10
    movk xtmp, 0x20, lsl 16
    movk xtmp, 0x40, lsl 32
    movk xtmp, 0x80, lsl 48
    mov bits.d[1], xtmp

    // Expand [1, 4, 16, 64] and [2, 8, 32, 128] into 32-bit lanes whose
    // four bytes hold the same value.
    movi tmp0.16b, #1
    shl packed_bits_even.4s, bits.4s, #16
    ushr packed_bits_even.4s, packed_bits_even.4s, #16
    ushr packed_bits_odd.4s, bits.4s, #16
    mul packed_bits_even.4s, packed_bits_even.4s, tmp0.4s
    mul packed_bits_odd.4s, packed_bits_odd.4s, tmp0.4s

    movz tmp, #MLKEM_Q
    dup  mlkem_q.8h, tmp

    // Each 3-byte group b0,b1,b2 encodes two samples:
    // x0 = b0 | ((b1 & 0x0f) << 8), x1 = (b1 >> 4) | (b2 << 4).
    // TBL indices for the first sample, x0, from each group.
    // [0, 1, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18, 19, 21, 22].
    movz xtmp0, #0x0100
    movk xtmp0, #0x0403, lsl #16
    movk xtmp0, #0x0706, lsl #32
    movk xtmp0, #0x0a09, lsl #48
    movz xtmp1, #0x0d0c
    movk xtmp1, #0x100f, lsl #16
    movk xtmp1, #0x1312, lsl #32
    movk xtmp1, #0x1615, lsl #48
    fmov unpack0d, xtmp0
    mov unpack0.d[1], xtmp1

    // Increment the indices for the second sample, x1, or for the second
    // 24 bytes.
    movi tmp0.16b, #1
    movi tmp1.16b, #8
    add unpack1.16b, unpack0.16b, tmp0.16b
    add unpack2.16b, unpack0.16b, tmp1.16b
    add unpack3.16b, unpack2.16b, tmp0.16b

    mov output_tmp_base, sp
    mov output_tmp, output_tmp_base

    // The entire temporary stack buffer is copied to the output buffer
    // at the end of this routine. To avoid leaking original stack contents
    // in case not enough bytes have been sampled, zero the temporary buffer.
    mov initial_zero_count, #0
    eor val0.16b, val0.16b, val0.16b
mlk_rej_uniform_initial_zero:
        str val0q, [output_tmp], #64
        str val0q, [output_tmp, #-48]
        str val0q, [output_tmp, #-32]
        str val0q, [output_tmp, #-16]
        add initial_zero_count, initial_zero_count, #32
        cmp initial_zero_count, #MLKEM_N
        b.lt mlk_rej_uniform_initial_zero

    mov output_tmp, output_tmp_base

    mov count, #0
    mov len, #MLKEM_N

    cmp buflen, #48
    b.lo mlk_rej_uniform_loop48_end

mlk_rej_uniform_loop48:
        // Finish once we've generated sufficiently many coefficients
        cmp     count, len
        b.hs    mlk_rej_uniform_memory_copy

        sub     buflen, buflen, #48

        // Load sixteen packed pairs of 12-bit samples. TBL de-interleaves
        // the first and second samples from each 3-byte group into 16-bit
        // lanes.
        ldp     buf0q, buf1q, [buf]
        ldr     buf2q, [buf, #32]
        add     buf, buf, #48

        tbl     tmp0.16b, {buf0.16b, buf1.16b}, unpack0.16b
        tbl     tmp1.16b, {buf1.16b, buf2.16b}, unpack2.16b
        tbl     tmp2.16b, {buf0.16b, buf1.16b}, unpack1.16b
        tbl     tmp3.16b, {buf1.16b, buf2.16b}, unpack3.16b

        bic     tmp0.8h, #0xf0, lsl 8
        bic     tmp1.8h, #0xf0, lsl 8
        ushr    tmp2.8h, tmp2.8h, #4
        ushr    tmp3.8h, tmp3.8h, #4

        zip1    val0.8h, tmp0.8h, tmp2.8h
        zip2    val1.8h, tmp0.8h, tmp2.8h
        zip1    val2.8h, tmp1.8h, tmp3.8h
        zip2    val3.8h, tmp1.8h, tmp3.8h

        // Build an 8-bit validity bitmap for each vector, then use it to look
        // up a TBL permutation that moves valid lanes to the front of the
        // vector. Store each vector and advance the output by its valid count.

        // Set valid lanes to -1 (0b1...1)
        cmhi    sign0.8h, mlkem_q.8h, val0.8h
        cmhi    sign1.8h, mlkem_q.8h, val1.8h
        cmhi    sign2.8h, mlkem_q.8h, val2.8h
        cmhi    sign3.8h, mlkem_q.8h, val3.8h

        // Let mV[i] be 0xff if lane i of valV is valid, and 0 otherwise.
        // Each 16-bit CMHI result contains two copies of mV[i]. The byte
        // transposes keep one copy and pair val0/val1 and val2/val3. The
        // halfword transposes then put one mask from each vector in a
        // 32-bit word:
        //
        // sign0.s[k] = {m0[2k],   m1[2k],   m2[2k],   m3[2k]}
        // sign2.s[k] = {m0[2k+1], m1[2k+1], m2[2k+1], m3[2k+1]}
        //
        // for k = 0,...,3.
        trn1    sign0.16b, sign0.16b, sign1.16b
        trn1    sign1.16b, sign2.16b, sign3.16b
        trn2    sign2.8h, sign0.8h, sign1.8h
        trn1    sign0.8h, sign0.8h, sign1.8h

        // In word k, map lanes 2k and 2k+1 to bits 2k and 2k+1 of each
        // vector's byte, then combine the pair. Each byte is at most 255,
        // so carries cannot cross byte boundaries.
        and     sign0.16b, sign0.16b, packed_bits_even.16b
        and     sign2.16b, sign2.16b, packed_bits_odd.16b
        add     sign0.4s, sign0.4s, sign2.4s

        // Sum the four words. Byte V of t0d is the validity bitmap for valV.
        uaddlv  t0d, sign0.4s

        fmov    rec_idx_3, t0d
        ubfx    rec_idx_0, rec_idx_3, #0, #8
        ubfx    rec_idx_1, rec_idx_3, #8, #8
        ubfx    rec_idx_2, rec_idx_3, #16, #8
        ubfx    rec_idx_3, rec_idx_3, #24, #8

        ldr     table0q, [table_idx, rec_idx_0, lsl #4]
        ldr     table1q, [table_idx, rec_idx_1, lsl #4]
        ldr     table2q, [table_idx, rec_idx_2, lsl #4]
        ldr     table3q, [table_idx, rec_idx_3, lsl #4]

        // Count the valid lanes in each pair and sum the four words. Byte V
        // of t0d is the valid count for valV, between zero and eight.
        cnt     sign0.16b, sign0.16b
        uaddlv  t0d, sign0.4s

        fmov    ctr3, t0d
        ubfx    ctr0, ctr3, #0, #4
        ubfx    ctr1, ctr3, #8, #4
        ubfx    ctr2, ctr3, #16, #4
        ubfx    ctr3, ctr3, #24, #4

        // Move valid coefficients to the front.
        tbl     val0.16b, {val0.16b}, table0.16b
        tbl     val1.16b, {val1.16b}, table1.16b
        tbl     val2.16b, {val2.16b}, table2.16b
        tbl     val3.16b, {val3.16b}, table3.16b

        st1     {val0.8h}, [output_tmp]
        add     output_tmp, output_tmp, ctr0, lsl #1

        st1     {val1.8h}, [output_tmp]
        add     output_tmp, output_tmp, ctr1, lsl #1

        st1     {val2.8h}, [output_tmp]
        add     output_tmp, output_tmp, ctr2, lsl #1

        st1     {val3.8h}, [output_tmp]
        add     output_tmp, output_tmp, ctr3, lsl #1

        add     ctr01, ctr0, ctr1
        add     ctr23, ctr2, ctr3
        add     count, count, ctr01
        add     count, count, ctr23

        cmp buflen, #48
        b.hs mlk_rej_uniform_loop48
mlk_rej_uniform_loop48_end:

    // Finish once we've generated sufficiently many coefficients
    cmp     count, len
    b.hs    mlk_rej_uniform_memory_copy

    cmp buflen, #24
    b.lo mlk_rej_uniform_memory_copy

        // Load eight packed pairs of 12-bit samples and de-interleave them.
        ldr     buf0q, [buf]
        ldr     buf1d, [buf, #16]
        add     buf, buf, #24

        tbl     tmp0.16b, {buf0.16b, buf1.16b}, unpack0.16b
        tbl     tmp1.16b, {buf0.16b, buf1.16b}, unpack1.16b

        bic     tmp0.8h, #0xf0, lsl 8
        ushr    tmp1.8h, tmp1.8h, #4

        zip1    val0.8h, tmp0.8h, tmp1.8h
        zip2    val1.8h, tmp0.8h, tmp1.8h

        cmhi    sign0.8h, mlkem_q.8h, val0.8h
        cmhi    sign1.8h, mlkem_q.8h, val1.8h

        and     sign0.16b, sign0.16b, bits.16b
        and     sign1.16b, sign1.16b, bits.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h

        fmov    rec_idx_0_w, t0
        fmov    rec_idx_1_w, t1

        ldr     table0q, [table_idx, rec_idx_0, lsl #4]
        ldr     table1q, [table_idx, rec_idx_1, lsl #4]

        cnt     sign0.16b, sign0.16b
        cnt     sign1.16b, sign1.16b

        uaddlv  t0, sign0.8h
        uaddlv  t1, sign1.8h

        fmov    ctr0_w, t0
        fmov    ctr1_w, t1

        tbl     val0.16b, {val0.16b}, table0.16b
        tbl     val1.16b, {val1.16b}, table1.16b

        st1     {val0.8h}, [output_tmp]
        add     output_tmp, output_tmp, ctr0, lsl #1

        st1     {val1.8h}, [output_tmp]

        add     count, count, ctr0
        add     count, count, ctr1

mlk_rej_uniform_memory_copy:
    // min = min(count,len)
    cmp  count, len
    csel count, count, len, lo

    // Always copy MLKEM_N coefficients from the stack to the destination,
    // even if not all of them may be valid. This simplifies the loop and
    // allows us to stick to vectorized code.
    mov final_copy_count, #0
    mov output_tmp, output_tmp_base
mlk_rej_uniform_final_copy:
        ldr val0q, [output_tmp], #64
        ldr val1q, [output_tmp, #-48]
        ldr val2q, [output_tmp, #-32]
        ldr val3q, [output_tmp, #-16]
        str val0q, [output], #64
        str val1q, [output, #-48]
        str val2q, [output, #-32]
        str val3q, [output, #-16]
        add final_copy_count, final_copy_count, #32
        cmp final_copy_count, #MLKEM_N
        b.lt mlk_rej_uniform_final_copy

    mov x0, count

mlk_rej_uniform_return:
    pop_stack
    ret


/****************** REGISTER DEALLOCATIONS *******************/
    .unreq output
    .unreq buf
    .unreq buflen
    .unreq table_idx
    .unreq len
    .unreq output_tmp
    .unreq output_tmp_base
    .unreq count
    .unreq buf_consumed
    .unreq tmp
    .unreq xtmp
    .unreq xtmp0
    .unreq xtmp1
    .unreq final_copy_count
    .unreq initial_zero_count
    .unreq rec_idx_0
    .unreq rec_idx_1
    .unreq rec_idx_2
    .unreq rec_idx_3
    .unreq ctr0
    .unreq ctr1
    .unreq ctr2
    .unreq ctr3
    .unreq ctr01
    .unreq ctr23
    .unreq buf0
    .unreq buf0q
    .unreq buf1
    .unreq buf1q
    .unreq buf1d
    .unreq buf2
    .unreq buf2q
    .unreq tmp0
    .unreq tmp1
    .unreq tmp2
    .unreq tmp3
    .unreq sign0
    .unreq sign1
    .unreq sign2
    .unreq sign3
    .unreq val0
    .unreq val0q
    .unreq val1
    .unreq val1q
    .unreq val2
    .unreq val2q
    .unreq val3
    .unreq val3q
    .unreq t0
    .unreq t1
    .unreq t0d
    .unreq unpack0
    .unreq unpack0d
    .unreq unpack1
    .unreq unpack2
    .unreq unpack3
    .unreq table0
    .unreq table0q
    .unreq table1
    .unreq table1q
    .unreq table2
    .unreq table2q
    .unreq table3
    .unreq table3q
    .unreq packed_bits_even
    .unreq packed_bits_odd
    .unreq mlkem_q
    .unreq bits
    .unreq rec_idx_0_w
    .unreq rec_idx_1_w
    .unreq rec_idx_2_w
    .unreq rec_idx_3_w
    .unreq ctr0_w
    .unreq ctr1_w
    .unreq ctr2_w
    .unreq ctr3_w

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef STACK_SIZE

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
