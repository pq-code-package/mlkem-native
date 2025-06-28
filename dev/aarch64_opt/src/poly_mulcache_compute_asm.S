/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

/* Montgomery multiplication, with precomputed Montgomery twist
 * Expects modulus in consts.h[0]. */
.macro mulmod dst, src, const, const_twisted
        sqrdmulh tmp0.8h,    \src\().8h, \const_twisted\().8h
        mul      \dst\().8h, \src\().8h, \const\().8h
        mls      \dst\().8h, tmp0.8h,    modulus.h[0]
.endm

/********************************************
 *      mlk_poly_mulcache_compute()         *
 ********************************************/

        cache_ptr         .req x0
        data_ptr          .req x1
        zeta_ptr          .req x2
        zeta_twisted_ptr  .req x3
        count             .req x4
        wtmp              .req w5

        data_odd          .req v0
        zeta              .req v1
        q_zeta            .req q1
        zeta_twisted      .req v2
        q_zeta_twisted    .req q2

        tmp0              .req v3
        q_tmp0            .req q3
        tmp1              .req v4
        q_tmp1            .req q4
        dst               .req v5
        q_dst             .req q5

        modulus           .req v6
        modulus_twisted   .req v7

        .global MLK_ASM_NAMESPACE(poly_mulcache_compute_asm)
        .text
        .balign 4
MLK_ASM_FN_SYMBOL(poly_mulcache_compute_asm)
        mov wtmp, #3329
        dup modulus.8h, wtmp

        mov wtmp, #20159
        dup modulus_twisted.8h, wtmp

        mov count, #16
                                             // Instructions:    10
                                             // Expected cycles: 9
                                             // Expected IPC:    1.11
                                             //
                                             // Cycle bound:     9.0
                                             // IPC bound:       1.11
                                             //
                                             // Wall time:     0.05s
                                             // User time:     0.05s
                                             //
                                             // ----- cycle (expected) ------>
                                             // 0                        25
                                             // |------------------------|----
        ldr q18, [x1], #32                   // *.............................
        ldr q0, [x1, #-16]                   // *.............................
        ldr q4, [x3], #16                    // .*............................
        ldr q26, [x2], #16                   // .*............................
        ldr q29, [x1, #16]                   // ..*...........................
        ldr q5, [x1], #32                    // ..*...........................
        uzp2 v17.8H, v18.8H, v0.8H           // ....*.........................
        ldr q18, [x3], #16                   // ....*.........................
        sqrdmulh v0.8H, v17.8H, v4.8H        // ......*.......................
        mul v26.8H, v17.8H, v26.8H           // ........*.....................

                                               // ------ cycle (expected) ------>
                                               // 0                        25
                                               // |------------------------|-----
        // ldr q5, [x1], #32                   // *..............................
        // ldr q29, [x1, #-16]                 // *..............................
        // ldr q18, [x3], #16                  // .*.............................
        // uzp2 v17.8H, v5.8H, v29.8H          // ....*..........................
        // ldr q16, [x2], #16                  // .*.............................
        // ldr q5, [x1], #32                   // ..*............................
        // sqrdmulh v0.8H, v17.8H, v18.8H      // ......*........................
        // ldr q29, [x1, #-16]                 // ..*............................
        // ldr q18, [x3], #16                  // ....*..........................
        // mul v26.8H, v17.8H, v16.8H          // ........*......................

        sub count, count, #2
poly_mulcache_compute_loop_start:
                                              // Instructions:    9
                                              // Expected cycles: 7
                                              // Expected IPC:    1.29
                                              //
                                              // Cycle bound:     7.0
                                              // IPC bound:       1.29
                                              //
                                              // Wall time:     0.07s
                                              // User time:     0.07s
                                              //
                                              // ----- cycle (expected) ------>
                                              // 0                        25
                                              // |------------------------|----
        uzp2 v17.8H, v5.8H, v29.8H            // *.............................
        mls v26.8H, v0.8H, v6.H[0]            // l.............................
        ldr q16, [x2], #16                    // .*............................
        ldr q5, [x1], #32                     // ..e...........................
        sqrdmulh v0.8H, v17.8H, v18.8H        // ..*...........................
        ldr q29, [x1, #-16]                   // ...e..........................
        ldr q18, [x3], #16                    // ....e.........................
        str q26, [x0], #16                    // .....l........................
        mul v26.8H, v17.8H, v16.8H            // .....*........................

                                                  // ------ cycle (expected) ------>
                                                  // 0                        25
                                                  // |------------------------|-----
        // ldr q3, [x1], #32                      // e....'.~....'.~....'.~....'.~..
        // ldr q4, [x1, #-16]                     // .e...'..~...'..~...'..~...'..~.
        // ldr q1, [x2], #16                      // .....'*.....'~.....'~.....'~...
        // ldr q2, [x3], #16                      // ..e..'...~..'...~..'...~..'....
        // uzp2 v0.8h, v3.8h, v4.8h               // .....*......~......~......~....
        // sqrdmulh v3.8h,    v0.8h, v2.8h        // ~....'.*....'.~....'.~....'.~..
        // mul      v5.8h, v0.8h, v1.8h           // ...~.'....*.'....~.'....~.'....
        // mls      v5.8h, v3.8h,    v6.h[0]      // .....~......l......~......~....
        // str q5, [x0], #16                      // ...~.'....~.'....l.'....~.'....

        subs count, count, 1
        cbnz count, poly_mulcache_compute_loop_start
                                              // Instructions:    8
                                              // Expected cycles: 13
                                              // Expected IPC:    0.62
                                              //
                                              // Cycle bound:     13.0
                                              // IPC bound:       0.62
                                              //
                                              // Wall time:     0.05s
                                              // User time:     0.05s
                                              //
                                              // ----- cycle (expected) ------>
                                              // 0                        25
                                              // |------------------------|----
        mls v26.8H, v0.8H, v6.H[0]            // *.............................
        uzp2 v16.8H, v5.8H, v29.8H            // *.............................
        ldr q4, [x2], #16                     // .*............................
        sqrdmulh v2.8H, v16.8H, v18.8H        // ..*...........................
        str q26, [x0], #16                    // .....*........................
        mul v29.8H, v16.8H, v4.8H             // .....*........................
        mls v29.8H, v2.8H, v6.H[0]            // .......*......................
        str q29, [x0], #16                    // ............*.................

                                               // ------ cycle (expected) ------>
                                               // 0                        25
                                               // |------------------------|-----
        // uzp2 v17.8H, v5.8H, v29.8H          // *..............................
        // mls v26.8H, v0.8H, v6.H[0]          // *..............................
        // ldr q16, [x2], #16                  // .*.............................
        // sqrdmulh v0.8H, v17.8H, v18.8H      // ..*............................
        // str q26, [x0], #16                  // .....*.........................
        // mul v26.8H, v17.8H, v16.8H          // .....*.........................
        // mls v26.8H, v0.8H, v6.H[0]          // .......*.......................
        // str q26, [x0], #16                  // ............*..................


        ret

        .unreq cache_ptr
        .unreq data_ptr
        .unreq zeta_ptr
        .unreq zeta_twisted_ptr
        .unreq count
        .unreq wtmp

        .unreq data_odd
        .unreq zeta
        .unreq q_zeta
        .unreq zeta_twisted
        .unreq q_zeta_twisted

        .unreq tmp0
        .unreq q_tmp0
        .unreq tmp1
        .unreq q_tmp1
        .unreq dst
        .unreq q_dst

        .unreq modulus
        .unreq modulus_twisted

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
