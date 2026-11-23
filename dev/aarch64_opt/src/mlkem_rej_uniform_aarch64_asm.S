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
      description: Output buffer, disjoint from buf and table. The return value is its valid prefix length.
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
*/

#include "../../../common.h"
#if defined(MLK_SYS_AARCH64_NEON) && \
    defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

    /* Parameters */
    output                      .req x0
    buf                         .req x1
    buflen                      .req x2
    table_idx                   .req x3

    /* Number of coefficients sampled so far */
    count                       .req x9

    /* Temporary registers */
    xtmp0                       .req x7
    xtmp1                       .req x11
    q_scalar                    .req w4
    sample0                     .req w5
    sample1                     .req w6

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
    val1                        .req v17
    val2                        .req v18
    val3                        .req v19

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
    // Load 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80
    movz xtmp0, 0x1
    movk xtmp0, 0x2, lsl 16
    movk xtmp0, 0x4, lsl 32
    movk xtmp0, 0x8, lsl 48
    mov bits.d[0], xtmp0

    movz xtmp0, 0x10
    movk xtmp0, 0x20, lsl 16
    movk xtmp0, 0x40, lsl 32
    movk xtmp0, 0x80, lsl 48
    mov bits.d[1], xtmp0

    // Expand [1, 4, 16, 64] and [2, 8, 32, 128] into 32-bit lanes whose
    // four bytes hold the same value.
    movi tmp0.16b, #1
    shl packed_bits_even.4s, bits.4s, #16
    ushr packed_bits_even.4s, packed_bits_even.4s, #16
    ushr packed_bits_odd.4s, bits.4s, #16
    mul packed_bits_even.4s, packed_bits_even.4s, tmp0.4s
    mul packed_bits_odd.4s, packed_bits_odd.4s, tmp0.4s

    movz q_scalar, #MLKEM_Q
    dup  mlkem_q.8h, q_scalar

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

    mov count, #0

    cmp buflen, #48
    b.lo mlk_rej_uniform_block16

mlk_rej_uniform_loop48:
        // Four full vector stores need room for 32 coefficients.
        cmp     count, #(MLKEM_N - 32)
        b.hi    mlk_rej_uniform_block16

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

        st1     {val0.8h}, [output]
        add     output, output, ctr0, lsl #1

        st1     {val1.8h}, [output]
        add     output, output, ctr1, lsl #1

        st1     {val2.8h}, [output]
        add     output, output, ctr2, lsl #1

        st1     {val3.8h}, [output]
        add     output, output, ctr3, lsl #1

        add     ctr01, ctr0, ctr1
        add     ctr23, ctr2, ctr3
        add     count, count, ctr01
        add     count, count, ctr23

        cmp buflen, #48
        b.hs mlk_rej_uniform_loop48
mlk_rej_uniform_block16:
    // The half block needs 16 output slots and 24 input bytes.
    cmp     buflen, #24
    b.lo    mlk_rej_uniform_return
    cmp     count, #(MLKEM_N - 16)
    b.hi    mlk_rej_uniform_scalar_loop

        sub     buflen, buflen, #24
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

        st1     {val0.8h}, [output]
        add     output, output, ctr0, lsl #1

        st1     {val1.8h}, [output]
        add     output, output, ctr1, lsl #1

        add     count, count, ctr0
        add     count, count, ctr1

mlk_rej_uniform_scalar_loop:
    // Two overlapping halfword loads read one three-byte group.
    cmp     count, #MLKEM_N
    b.hs    mlk_rej_uniform_return
    cbz     buflen, mlk_rej_uniform_return
    ldrh    sample0, [buf]
    ldurh   sample1, [buf, #1]
    add     buf, buf, #3
    sub     buflen, buflen, #3
    and     sample0, sample0, #0xfff
    lsr     sample1, sample1, #4
    cmp     sample0, q_scalar
    b.hs    mlk_rej_uniform_second_sample
    strh    sample0, [output], #2
    add     count, count, #1
    cmp     count, #MLKEM_N
    b.hs    mlk_rej_uniform_scalar_loop

mlk_rej_uniform_second_sample:
    cmp     sample1, q_scalar
    b.hs    mlk_rej_uniform_scalar_loop
    strh    sample1, [output], #2
    add     count, count, #1
    b       mlk_rej_uniform_scalar_loop

mlk_rej_uniform_return:
    mov     x0, count
    ret


/****************** REGISTER DEALLOCATIONS *******************/
    .unreq output
    .unreq buf
    .unreq buflen
    .unreq table_idx
    .unreq count
    .unreq xtmp0
    .unreq xtmp1
    .unreq q_scalar
    .unreq sample0
    .unreq sample1
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
    .unreq val1
    .unreq val2
    .unreq val3
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

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
