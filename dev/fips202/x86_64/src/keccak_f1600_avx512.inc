/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Keccak-f[1600] rounds for keccak_f1600_x1_avx512_asm (one state, in
 * xmm registers) and keccak_f1600_x4_avx512_asm (four states, in ymm
 * registers).
 *
 * The macros take the register class V (xmm or ymm), and some also the
 * number n of quadwords in it (2 or 4). x86 assemblers have no register
 * aliases (.req), so registers are passed as numbers: with V = xmm and
 * a0 = 5, %\V\a0 is %xmm5, and %\V\()30 is %xmm30.
 *
 * Register allocation: every lane of the state has a register of its
 * own, with state j in quadword j, and there are no spills.
 *
 *   V0..V24    the 25 lanes; lane x+5y is A[x,y] in FIPS 202
 *   V25..V29   theta: C[x], the parity of column x, in V(25+x)
 *   V30        theta: D[x]; chi: copy of A[0,y]; restore: temporary
 *   V31        chi: copy of A[1,y]
 *
 * pi by register renaming: pi sets A[x,y] = A[x+3y,x] (indices mod 5),
 * that is, lane i of the new state is lane sigma(i) of the old one, where
 *
 *   sigma = (0, 6, 12, 18, 24,  3,  9, 10, 16, 22,  1,  7, 13, 19, 20,
 *            4, 5, 11, 17, 23,  2,  8, 14, 15, 21)
 *
 * keccak_round moves no data for pi. It takes the numbers a0..a24 of
 * the registers that hold lanes 0..24, and chi works on row y of the
 * new state in registers a<sigma(5y)> to a<sigma(5y+4)>. Lane i of the
 * result is then in register a<sigma(i)>, and the next round is called
 * with that list.
 *
 * Four rounds per loop iteration: keccak_f1600_4rounds calls
 * keccak_round with the identity, sigma, sigma^2 and sigma^3 as the
 * list, and then moves lane i back to register i for the next
 * iteration (the restore). sigma is one cycle of length 24 on lanes
 * 1..24, so only all 24 rounds unrolled would need no restore.
 */

/* C = A0 ^ A1 ^ A2 ^ A3 ^ A4, for one column */
.macro xor5 V, c, a0, a1, a2, a3, a4
        vmovdqa64  %\V\a0, %\V\c
        vpternlogq $0x96, %\V\a2, %\V\a1, %\V\c
        vpternlogq $0x96, %\V\a4, %\V\a3, %\V\c
.endm

/* D = C[x-1] ^ rol(C[x+1], 1) and A[x,y] ^= D, for column x */
.macro theta_col V, cprev, cnext, a0, a1, a2, a3, a4
        vprolq     $1, %\V\cnext, %\V\()30
        vpternlogq $0x96, %\V\()30, %\V\cprev, %\V\a0
        vpternlogq $0x96, %\V\()30, %\V\cprev, %\V\a1
        vpternlogq $0x96, %\V\()30, %\V\cprev, %\V\a2
        vpternlogq $0x96, %\V\()30, %\V\cprev, %\V\a3
        vpternlogq $0x96, %\V\()30, %\V\cprev, %\V\a4
.endm

/*
 * chi on one row: A[x] ^= ~A[x+1] & A[x+2] (0xd2), with the first two
 * lanes saved in V30 and V31 for the last two. If rc is not `none`, also
 * iota: A[0] ^= the round constant at rc(%rsi), broadcast to n quadwords.
 */
.macro chi_row V, n, rc, a0, a1, a2, a3, a4
        vmovdqa64  %\V\a0, %\V\()30
        vmovdqa64  %\V\a1, %\V\()31
        vpternlogq $0xd2, %\V\a2, %\V\a1, %\V\a0
.ifnc \rc, none
        vpxorq     \rc(%rsi){1to\n}, %\V\a0, %\V\a0
.endif
        vpternlogq $0xd2, %\V\a3, %\V\a2, %\V\a1
        vpternlogq $0xd2, %\V\a4, %\V\a3, %\V\a2
        vpternlogq $0xd2, %\V\()30, %\V\a4, %\V\a3
        vpternlogq $0xd2, %\V\()31, %\V\()30, %\V\a4
.endm

/*
 * One round, with lane i in register \a<i> and the round constant at
 * rc(%rsi). Lane i of the result is in register \a<sigma(i)>.
 */
.macro keccak_round V, n, rc, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24
        /* theta */
        xor5       \V, 25, \a0, \a5, \a10, \a15, \a20
        xor5       \V, 26, \a1, \a6, \a11, \a16, \a21
        xor5       \V, 27, \a2, \a7, \a12, \a17, \a22
        xor5       \V, 28, \a3, \a8, \a13, \a18, \a23
        xor5       \V, 29, \a4, \a9, \a14, \a19, \a24
        theta_col  \V, 29, 26, \a0, \a5, \a10, \a15, \a20
        theta_col  \V, 25, 27, \a1, \a6, \a11, \a16, \a21
        theta_col  \V, 26, 28, \a2, \a7, \a12, \a17, \a22
        theta_col  \V, 27, 29, \a3, \a8, \a13, \a18, \a23
        theta_col  \V, 28, 25, \a4, \a9, \a14, \a19, \a24
        /* rho, column by column; A[0,0] is not rotated */
        vprolq     $36, %\V\a5, %\V\a5
        vprolq     $3, %\V\a10, %\V\a10
        vprolq     $41, %\V\a15, %\V\a15
        vprolq     $18, %\V\a20, %\V\a20
        vprolq     $1, %\V\a1, %\V\a1
        vprolq     $44, %\V\a6, %\V\a6
        vprolq     $10, %\V\a11, %\V\a11
        vprolq     $45, %\V\a16, %\V\a16
        vprolq     $2, %\V\a21, %\V\a21
        vprolq     $62, %\V\a2, %\V\a2
        vprolq     $6, %\V\a7, %\V\a7
        vprolq     $43, %\V\a12, %\V\a12
        vprolq     $15, %\V\a17, %\V\a17
        vprolq     $61, %\V\a22, %\V\a22
        vprolq     $28, %\V\a3, %\V\a3
        vprolq     $55, %\V\a8, %\V\a8
        vprolq     $25, %\V\a13, %\V\a13
        vprolq     $21, %\V\a18, %\V\a18
        vprolq     $56, %\V\a23, %\V\a23
        vprolq     $27, %\V\a4, %\V\a4
        vprolq     $20, %\V\a9, %\V\a9
        vprolq     $39, %\V\a14, %\V\a14
        vprolq     $8, %\V\a19, %\V\a19
        vprolq     $14, %\V\a24, %\V\a24
        /* pi, by renaming; chi on the rows of the result; iota */
        chi_row    \V, \n, \rc, \a0, \a6, \a12, \a18, \a24
        chi_row    \V, \n, none, \a3, \a9, \a10, \a16, \a22
        chi_row    \V, \n, none, \a1, \a7, \a13, \a19, \a20
        chi_row    \V, \n, none, \a4, \a5, \a11, \a17, \a23
        chi_row    \V, \n, none, \a2, \a8, \a14, \a15, \a21
.endm

/*
 * V\d = V\s, for the restore. If both registers are below 16, this is
 * the VEX vmovdqa, otherwise the EVEX vmovdqa64. GNU as -O2 assembles
 * vmovdqa64 of registers below 16 as vmovdqa, while GNU as without -O2
 * and LLVM keep it; writing vmovdqa gives the same code with all of
 * them. GNU as and LLVM also agree on the encoding of vmovdqa itself:
 * from one of V8..V15 to one of V0..V7, both choose the store form
 * (opcode 7F), which has the 2-byte VEX prefix.
 */
.macro vmov V, s, d
.if \s < 16 && \d < 16
        vmovdqa    %\V\s, %\V\d
.else
        vmovdqa64  %\V\s, %\V\d
.endif
.endm

/*
 * Lane r0 is in register r1, lane r1 in r2, ..., lane r5 in r0: move
 * each of them to its own register, with V30 as the temporary.
 */
.macro cycle6 V, r0, r1, r2, r3, r4, r5
        vmov       \V, \r0, 30
        vmov       \V, \r1, \r0
        vmov       \V, \r2, \r1
        vmov       \V, \r3, \r2
        vmov       \V, \r4, \r3
        vmov       \V, \r5, \r4
        vmov       \V, 30, \r5
.endm

/*
 * Four rounds, with the round constants at 0(%rsi) to 24(%rsi). Lane i
 * is in register i before and after.
 */
.macro keccak_f1600_4rounds V, n
        keccak_round \V, \n, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24
        keccak_round \V, \n, 8, 0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21
        keccak_round \V, \n, 16, 0, 9, 13, 17, 21, 18, 22, 1, 5, 14, 6, 10, 19, 23, 2, 24, 3, 7, 11, 15, 12, 16, 20, 4, 8
        keccak_round \V, \n, 24, 0, 22, 19, 11, 8, 17, 14, 6, 3, 20, 9, 1, 23, 15, 12, 21, 18, 10, 7, 4, 13, 5, 2, 24, 16
        /*
         * Lane i is now in register sigma^4(i). sigma^4 keeps lane 0 in
         * place and moves the others in four cycles of length 6.
         */
        cycle6     \V, 1, 14, 13, 4, 16, 17
        cycle6     \V, 2, 23, 21, 3, 7, 9
        cycle6     \V, 5, 11, 6, 20, 19, 24
        cycle6     \V, 8, 18, 10, 22, 12, 15
.endm
