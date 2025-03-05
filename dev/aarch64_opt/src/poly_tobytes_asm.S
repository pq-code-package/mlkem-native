/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64_OPT) && \
    !defined(MLK_MULTILEVEL_BUILD_NO_SHARED)
/* simpasm: header-end */

/********************************************
 *         mlk_poly_tobytes()               *
 ********************************************/

        data0 .req v0
        data1 .req v1
        out0  .req v2
        out1  .req v3
        out2  .req v4
        tmp   .req v5

        dst   .req x0
        src   .req x1
        count .req x2

        .text
        .global MLK_ASM_NAMESPACE(poly_tobytes_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_tobytes_asm)

        mov count, #16
                                               // Instructions:    6
                                               // Expected cycles: 13
                                               // Expected IPC:    0.46
                                               //
                                               // Cycle bound:     13.0
                                               // IPC bound:       0.46
                                               //
                                               // Wall time:     0.01s
                                               // User time:     0.01s
                                               //
                                               // ----- cycle (expected) ------>
                                               // 0                        25
                                               // |------------------------|----
        ld2 {v11.8H, v12.8H}, [x1], #32        // *.............................
        xtn v2.8B, v12.8H                      // ......*.......................
        shrn v14.8B, v12.8H, #4                // .......*......................
        xtn v12.8B, v11.8H                     // .........*....................
        shrn v13.8B, v11.8H, #8                // ..........*...................
        sli v13.8B, v2.8B, #4                  // ............*.................

                                                // ------ cycle (expected) ------>
                                                // 0                        25
                                                // |------------------------|-----
        // ld2 {v24.8H, v25.8H}, [x1], #32      // *..............................
        // xtn v12.8B, v25.8H                   // ......*........................
        // shrn v13.8B, v24.8H, #8              // ..........*....................
        // sli v13.8B, v12.8B, #4               // ............*..................
        // shrn v14.8B, v25.8H, #4              // .......*.......................
        // xtn v12.8B, v24.8H                   // .........*.....................

        sub count, count, #1
poly_tobytes_asm_asm_loop_start:
                                                       // Instructions:    7
                                                       // Expected cycles: 15
                                                       // Expected IPC:    0.47
                                                       //
                                                       // Cycle bound:     15.0
                                                       // IPC bound:       0.47
                                                       //
                                                       // Wall time:     0.11s
                                                       // User time:     0.11s
                                                       //
                                                       // ----- cycle (expected) ------>
                                                       // 0                        25
                                                       // |------------------------|----
        ld2 {v24.8H, v25.8H}, [x1], #32                // *.............................
        st3 {v12.8B, v13.8B, v14.8B}, [x0], #24        // ....l.........................
        xtn v12.8B, v25.8H                             // .......*......................
        shrn v13.8B, v24.8H, #8                        // ........*.....................
        sli v13.8B, v12.8B, #4                         // ..........*...................
        shrn v14.8B, v25.8H, #4                        // ............*.................
        xtn v12.8B, v24.8H                             // ..............*...............

                                                     // ------ cycle (expected) ------>
                                                     // 0                        25
                                                     // |------------------------|-----
        // ld2 {v0.8h, v1.8h}, [x1], #32             // *..............~...............
        // xtn v2.8b, v0.8h                          // ..............*'.............~.
        // shrn v3.8b, v0.8h, #8                     // ........*......'.......~.......
        // xtn v5.8b, v1.8h                          // .......*.......'......~........
        // sli v3.8b, v5.8b, #4                      // ..........*....'.........~.....
        // shrn v4.8b, v1.8h, #4                     // ............*..'...........~...
        // st3 {v2.8b, v3.8b, v4.8b}, [x0], #24      // ....~..........'...l...........

        sub count, count, 1
        cbnz count, poly_tobytes_asm_asm_loop_start
                                                       // Instructions:    1
                                                       // Expected cycles: 1
                                                       // Expected IPC:    1.00
                                                       //
                                                       // Cycle bound:     1.0
                                                       // IPC bound:       1.00
                                                       //
                                                       // Wall time:     0.00s
                                                       // User time:     0.00s
                                                       //
                                                       // ----- cycle (expected) ------>
                                                       // 0                        25
                                                       // |------------------------|----
        st3 {v12.8B, v13.8B, v14.8B}, [x0], #24        // *.............................

                                                        // ------ cycle (expected) ------>
                                                        // 0                        25
                                                        // |------------------------|-----
        // st3 {v12.8B, v13.8B, v14.8B}, [x0], #24      // *..............................

        ret

        .unreq data0
        .unreq data1
        .unreq out0
        .unreq out1
        .unreq out2
        .unreq tmp
        .unreq dst
        .unreq src
        .unreq count

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_AARCH64_OPT &&
          !MLK_MULTILEVEL_BUILD_NO_SHARED */
