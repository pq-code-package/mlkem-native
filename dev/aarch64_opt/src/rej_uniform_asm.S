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
 *                                     Must be a multiple of 24.
 *
 * Returns number of sampled 16-bit integers (at most MLKEM_N).
 **************************************************/
#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
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
    buf1                        .req v1
    buf2                        .req v2

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

    t0                          .req s20
    t1                          .req s21
    t2                          .req s22
    t3                          .req s23

    table0                      .req v24
    table0q                     .req q24
    table1                      .req v25
    table1q                     .req q25
    table2                      .req v26
    table2q                     .req q26
    table3                      .req v27
    table3q                     .req q27

    mlkem_q                     .req v30
    bits                        .req v31

    .text
    .global MLK_ASM_NAMESPACE(rej_uniform_asm)
    .balign 4
MLK_ASM_FN_SYMBOL(rej_uniform_asm)
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

    movz tmp, #MLKEM_Q
    dup  mlkem_q.8h, tmp

    mov output_tmp_base, sp
    mov output_tmp, output_tmp_base

    // The entire temporary stack buffer is copied to the output buffer
    // at the end of this routine. To avoid leaking original stack contents
    // in case not enough bytes have been sampled, zero the temporary buffer.
    mov initial_zero_count, #0
    eor val0.16b, val0.16b, val0.16b
rej_uniform_initial_zero:
        str val0q, [output_tmp], #64
        str val0q, [output_tmp, #-48]
        str val0q, [output_tmp, #-32]
        str val0q, [output_tmp, #-16]
        add initial_zero_count, initial_zero_count, #32
        cmp initial_zero_count, #MLKEM_N
        b.lt rej_uniform_initial_zero

    mov output_tmp, output_tmp_base

    mov count, #0
    mov len, #MLKEM_N

    cmp buflen, #48
    b.lo rej_uniform_loop48_end

rej_uniform_loop48:
        // Finish once we've generated sufficiently many coefficients
        cmp     count, len
        b.hs    rej_uniform_memory_copy
        // First, we unpack the byte stream into a stream of signed
        // coefficients, interpreting each consecutive 3 bytes as two
        // signed 12-bit coefficients, presented as 16-bit integers.

        // We handle 16 such triples a time, and use ld3 for the required
        // de-interleaving of the byte stream.
        rej_uniform_slothy_start:
                                                       // Instructions:    62
                                                       // Expected cycles: 65
                                                       // Expected IPC:    0.95
                                                       //
                                                       // Cycle bound:     65.0
                                                       // IPC bound:       0.95
                                                       //
                                                       // Wall time:     1.20s
                                                       // User time:     1.20s
                                                       //
                                                       // ----------------------- cycle (expected) ----------------------->
                                                       // 0                        25                       50
                                                       // |------------------------|------------------------|--------------
        ld3 {v0.16B, v1.16B, v2.16B}, [x1], #48        // *................................................................
        sub x2, x2, #48                                // ......*..........................................................
        zip1 v27.16B, v1.16B, v2.16B                   // ........*........................................................
        zip1 v18.16B, v0.16B, v1.16B                   // .........*.......................................................
        ushr v25.8H, v27.8H, #4                        // ..........*......................................................
        bic v18.8H, #0xf0, lsl #8                      // ...........*.....................................................
        zip2 v16.16B, v0.16B, v1.16B                   // ............*....................................................
        zip1 v17.8H, v18.8H, v25.8H                    // .............*...................................................
        bic v16.8H, #0xf0, lsl #8                      // ..............*..................................................
        cmhi v0.8H, v30.8H, v17.8H                     // ...............*.................................................
        zip2 v24.8H, v18.8H, v25.8H                    // ................*................................................
        and v0.16B, v0.16B, v31.16B                    // .................*...............................................
        uaddlv s23, v0.8H                              // ..................*..............................................
        cmhi v27.8H, v30.8H, v24.8H                    // ...................*.............................................
        cnt v21.16B, v0.16B                            // ....................*............................................
        fmov w12, s23                                  // .....................*...........................................
        ldr q25, [x3, x12, lsl #4]                     // ......................*..........................................
        zip2 v0.16B, v1.16B, v2.16B                    // ........................*........................................
        uaddlv s20, v21.8H                             // .........................*.......................................
        tbl v6.16B, {v17.16B}, v25.16B                 // ..........................*......................................
        ushr v29.8H, v0.8H, #4                         // ...........................*.....................................
        str q6, [x7]                                   // ............................*....................................
        and v27.16B, v27.16B, v31.16B                  // .............................*...................................
        zip1 v0.8H, v16.8H, v29.8H                     // ..............................*..................................
        fmov w12, s20                                  // ...............................*.................................
        cmhi v20.8H, v30.8H, v0.8H                     // ................................*................................
        add x16, x7, x12, lsl #1                       // ................................*................................
        cnt v21.16B, v27.16B                           // .................................*...............................
        and v22.16B, v20.16B, v31.16B                  // ..................................*..............................
        uaddlv s19, v22.8H                             // ...................................*.............................
        uaddlv s27, v27.8H                             // ....................................*............................
        cnt v5.16B, v22.16B                            // .....................................*...........................
        fmov w14, s19                                  // ......................................*..........................
        ldr q2, [x3, x14, lsl #4]                      // .......................................*.........................
        zip2 v18.8H, v16.8H, v29.8H                    // .........................................*.......................
        uaddlv s4, v5.8H                               // ..........................................*......................
        tbl v17.16B, {v0.16B}, v2.16B                  // ...........................................*.....................
        cmhi v20.8H, v30.8H, v18.8H                    // ............................................*....................
        fmov w14, s4                                   // .............................................*...................
        and v28.16B, v20.16B, v31.16B                  // ..............................................*..................
        uaddlv s16, v28.8H                             // ...............................................*.................
        cnt v22.16B, v28.16B                           // ................................................*................
        uaddlv s21, v21.8H                             // .................................................*...............
        fmov w13, s27                                  // ..................................................*..............
        ldr q27, [x3, x13, lsl #4]                     // ...................................................*.............
        fmov w13, s21                                  // .....................................................*...........
        fmov w15, s16                                  // ......................................................*..........
        add x12, x12, x13                              // ......................................................*..........
        uaddlv s28, v22.8H                             // .......................................................*.........
        add x5, x9, x12                                // .......................................................*.........
        tbl v24.16B, {v24.16B}, v27.16B                // ........................................................*........
        add x6, x16, x13, lsl #1                       // ........................................................*........
        ldr q5, [x3, x15, lsl #4]                      // .........................................................*.......
        add x10, x6, x14, lsl #1                       // ..........................................................*......
        fmov w15, s28                                  // ...........................................................*.....
        str q24, [x16]                                 // ............................................................*....
        add x7, x10, x15, lsl #1                       // ............................................................*....
        tbl v7.16B, {v18.16B}, v5.16B                  // .............................................................*...
        add x14, x14, x15                              // .............................................................*...
        str q17, [x6]                                  // ..............................................................*..
        add x9, x5, x14                                // ..............................................................*..
        str q7, [x10]                                  // ................................................................*

                                                            // ----------------------- cycle (expected) ----------------------->
                                                            // 0                        25                       50
                                                            // |------------------------|------------------------|--------------
        // sub     x2, x2, #48                              // ......*..........................................................
        // ld3     {v0.16b, v1.16b, v2.16b}, [x1], #48      // *................................................................
        // zip1    v4.16b, v0.16b, v1.16b                   // .........*.......................................................
        // zip2    v5.16b, v0.16b, v1.16b                   // ............*....................................................
        // zip1    v6.16b, v1.16b, v2.16b                   // ........*........................................................
        // zip2    v7.16b, v1.16b, v2.16b                   // ........................*........................................
        // bic     v4.8h, #0xf0, lsl #8                     // ...........*.....................................................
        // bic     v5.8h, #0xf0, lsl #8                     // ..............*..................................................
        // ushr    v6.8h, v6.8h, #4                         // ..........*......................................................
        // ushr    v7.8h, v7.8h, #4                         // ...........................*.....................................
        // zip1    v16.8h, v4.8h, v6.8h                     // .............*...................................................
        // zip2    v17.8h, v4.8h, v6.8h                     // ................*................................................
        // zip1    v18.8h, v5.8h, v7.8h                     // ..............................*..................................
        // zip2    v19.8h, v5.8h, v7.8h                     // .........................................*.......................
        // cmhi    v4.8h, v30.8h, v16.8h                    // ...............*.................................................
        // cmhi    v5.8h, v30.8h, v17.8h                    // ...................*.............................................
        // cmhi    v6.8h, v30.8h, v18.8h                    // ................................*................................
        // cmhi    v7.8h, v30.8h, v19.8h                    // ............................................*....................
        // and     v4.16b, v4.16b, v31.16b                  // .................*...............................................
        // and     v5.16b, v5.16b, v31.16b                  // .............................*...................................
        // and     v6.16b, v6.16b, v31.16b                  // ..................................*..............................
        // and     v7.16b, v7.16b, v31.16b                  // ..............................................*..................
        // uaddlv  s20, v4.8h                               // ..................*..............................................
        // uaddlv  s21, v5.8h                               // ....................................*............................
        // uaddlv  s22, v6.8h                               // ...................................*.............................
        // uaddlv  s23, v7.8h                               // ...............................................*.................
        // fmov    w12, s20                                 // .....................*...........................................
        // fmov    w13, s21                                 // ..................................................*..............
        // fmov    w14, s22                                 // ......................................*..........................
        // fmov    w15, s23                                 // ......................................................*..........
        // ldr     q24, [x3, x12, lsl #4]                   // ......................*..........................................
        // ldr     q25, [x3, x13, lsl #4]                   // ...................................................*.............
        // ldr     q26, [x3, x14, lsl #4]                   // .......................................*.........................
        // ldr     q27, [x3, x15, lsl #4]                   // .........................................................*.......
        // cnt     v4.16b, v4.16b                           // ....................*............................................
        // cnt     v5.16b, v5.16b                           // .................................*...............................
        // cnt     v6.16b, v6.16b                           // .....................................*...........................
        // cnt     v7.16b, v7.16b                           // ................................................*................
        // uaddlv  s20, v4.8h                               // .........................*.......................................
        // uaddlv  s21, v5.8h                               // .................................................*...............
        // uaddlv  s22, v6.8h                               // ..........................................*......................
        // uaddlv  s23, v7.8h                               // .......................................................*.........
        // fmov    w12, s20                                 // ...............................*.................................
        // fmov    w13, s21                                 // .....................................................*...........
        // fmov    w14, s22                                 // .............................................*...................
        // fmov    w15, s23                                 // ...........................................................*.....
        // tbl     v16.16b, {v16.16b}, v24.16b              // ..........................*......................................
        // tbl     v17.16b, {v17.16b}, v25.16b              // ........................................................*........
        // tbl     v18.16b, {v18.16b}, v26.16b              // ...........................................*.....................
        // tbl     v19.16b, {v19.16b}, v27.16b              // .............................................................*...
        // str     q16, [x7]                                // ............................*....................................
        // add     x7, x7, x12, lsl #1                      // ................................*................................
        // str     q17, [x7]                                // ............................................................*....
        // add     x7, x7, x13, lsl #1                      // ........................................................*........
        // str     q18, [x7]                                // ..............................................................*..
        // add     x7, x7, x14, lsl #1                      // ..........................................................*......
        // str     q19, [x7]                                // ................................................................*
        // add     x7, x7, x15, lsl #1                      // ............................................................*....
        // add     x12, x12, x13                            // ......................................................*..........
        // add     x14, x14, x15                            // .............................................................*...
        // add     x9, x9, x12                              // .......................................................*.........
        // add     x9, x9, x14                              // ..............................................................*..

        rej_uniform_slothy_end:

        cmp buflen, #48
        b.hs rej_uniform_loop48
rej_uniform_loop48_end:

    // Finish once we've generated sufficiently many coefficients
    cmp     count, len
    b.hs    rej_uniform_memory_copy

    cmp buflen, #24
    b.lo rej_uniform_memory_copy

        sub     buflen, buflen, #24
        ld3     {buf0.8b, buf1.8b, buf2.8b}, [buf], #24

        zip1    tmp0.16b, buf0.16b, buf1.16b
        zip1    tmp1.16b, buf1.16b, buf2.16b

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

        str     val0q, [output_tmp]
        add     output_tmp, output_tmp, ctr0, lsl #1

        str     val1q, [output_tmp]
        add     output_tmp, output_tmp, ctr1, lsl #1

        add     count, count, ctr0
        add     count, count, ctr1

rej_uniform_memory_copy:
    // min = min(count,len)
    cmp  count, len
    csel count, count, len, lo

    // Always copy MLKEM_N coefficients from the stack to the destination,
    // even if not all of them may be valid. This simplifies the loop and
    // allows us to stick to vectorized code.
    mov final_copy_count, #0
    mov output_tmp, output_tmp_base
rej_uniform_final_copy:
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
        b.lt rej_uniform_final_copy

    mov x0, count
    b rej_uniform_return

rej_uniform_return:
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
    .unreq buf1
    .unreq buf2
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
    .unreq t2
    .unreq t3
    .unreq table0
    .unreq table0q
    .unreq table1
    .unreq table1q
    .unreq table2
    .unreq table2q
    .unreq table3
    .unreq table3q
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
#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
