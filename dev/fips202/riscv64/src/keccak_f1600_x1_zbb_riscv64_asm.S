/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*yaml
  Name: keccak_f1600_x1_zbb_riscv64_asm
  Description: RV64 scalar implementation of the Keccak-f[1600] permutation for a single state, using Zbb
  Signature: void mlk_keccak_f1600_x1_zbb_riscv64_asm(uint64_t state[25], const uint64_t rc[24])
  ABI:
    Architecture: riscv64
    CallingConvention: LP64D
    Features: [ZBB]
    a0:
      type: buffer
      size_bytes: 200
      permissions: read/write
      c_parameter: uint64_t state[25]
      description: Keccak state (25 x uint64_t)
    a1:
      type: buffer
      size_bytes: 192
      permissions: read-only
      c_parameter: const uint64_t rc[24]
      description: Round constants (24 x uint64_t)
  Stack:
    bytes: 144
    description: register preservation and temporary storage
*/

#include "../../../../common.h"
#if defined(MLK_SYS_RISCV64) && defined(__riscv_zbb) && \
    defined(MLK_FIPS202_RISCV64_NEED_X1_ZBB) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

/*
 * The 25 lanes of the state are held in registers throughout, lane
 * A[x,y] in register Axy with x in {a,e,i,o,u} and y in {b,g,k,m,s}. This
 * leaves three temporaries. Each round is computed in place:
 *
 * - theta: the column parities C[0] and C[2] are kept on the stack while
 *   the others are computed. D[x] = C[x-1] ^ ROL(C[x+1], 1) is applied to
 *   column x only after C[x] has been computed. A parity is rotated in
 *   place once its unrotated value is no longer needed.
 * - rho and pi: pi permutes the 24 lanes other than A[0,0] in a single
 *   cycle. Following the cycle backwards, each lane is overwritten by the
 *   rotated lane it receives, which has not been overwritten yet. The
 *   start of the cycle, A[1,0], is left in a temporary by theta.
 * - chi: per plane, the two terms that need the original A[0] and A[1]
 *   are computed first; the plane is then overwritten in place.
 * - iota: the round constants are loaded via a pointer kept on the stack.
 *   The loop body computes two rounds.
 *
 * Zbb provides the rotation (rori) and AND-NOT (andn) instructions.
 */

#define Aba             a0
#define Abe             a1
#define Abi             a2
#define Abo             a3
#define Abu             a4
#define Aga             a5
#define Age             a6
#define Agi             a7
#define Ago             s2
#define Agu             s3
#define Aka             s4
#define Ake             s5
#define Aki             s6
#define Ako             s7
#define Aku             s8
#define Ama             s9
#define Ame             s10
#define Ami             s11
#define Amo             s0
#define Amu             s1
#define Asa             t3
#define Ase             t4
#define Asi             t5
#define Aso             t6
#define Asu             ra

#define tmp0            t0
#define tmp1            t1
#define tmp2            t2

/* Stack layout */
#define STACK_SIZE      144
#define STACK_GPRS      0     /* ra, s0-s11 */
#define STACK_STATE     104   /* state pointer */
#define STACK_RC        112   /* pointer to the next round constant */
#define STACK_RC_END    120   /* end of the round constants */
#define STACK_C0        128   /* column parity C[0] */
#define STACK_C2        136   /* column parity C[2] */

.macro save_gprs
        sd          ra, (STACK_GPRS + 0)(sp)
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
        sd          s\i, (STACK_GPRS + 8 + 8*\i)(sp)
        .endr
.endm

.macro restore_gprs
        ld          ra, (STACK_GPRS + 0)(sp)
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
        ld          s\i, (STACK_GPRS + 8 + 8*\i)(sp)
        .endr
.endm

/* \d = \a ^ \b ^ \c ^ \e ^ \f */
.macro xor5 d, a, b, c, e, f
        xor         \d, \a, \b
        xor         \d, \d, \c
        xor         \d, \d, \e
        xor         \d, \d, \f
.endm

/* Column x ^= \d, for the lanes \a, \b, \c, \e, \f of column x */
.macro xorcol d, a, b, c, e, f
        xor         \a, \a, \d
        xor         \b, \b, \d
        xor         \c, \c, \d
        xor         \e, \e, \d
        xor         \f, \f, \d
.endm

.macro theta
        /* Park C[0] and C[2] on the stack */
        xor5        tmp0, Aba, Aga, Aka, Ama, Asa
        sd          tmp0, STACK_C0(sp)
        xor5        tmp0, Abi, Agi, Aki, Ami, Asi
        sd          tmp0, STACK_C2(sp)

        /* tmp0 = C[1], tmp1 = C[4] */
        xor5        tmp0, Abe, Age, Ake, Ame, Ase
        xor5        tmp1, Abu, Agu, Aku, Amu, Asu

        /* D[0] = C[4] ^ ROL(C[1], 1). Afterwards, C[4] is only needed
         * rotated, so rotate it in place. */
        rori        tmp2, tmp0, 63
        xor         tmp2, tmp2, tmp1
        rori        tmp1, tmp1, 63
        xorcol      tmp2, Aba, Aga, Aka, Ama, Asa

        /* D[3] = C[2] ^ ROL(C[4], 1) in tmp1; then tmp2 = C[3], computed
         * before column 3 changes */
        ld          tmp2, STACK_C2(sp)
        xor         tmp1, tmp1, tmp2
        xor5        tmp2, Abo, Ago, Ako, Amo, Aso
        xorcol      tmp1, Abo, Ago, Ako, Amo, Aso

        /* D[2] = C[1] ^ ROL(C[3], 1) in tmp0; tmp1 = C[0] */
        rori        tmp1, tmp2, 63
        xor         tmp0, tmp0, tmp1
        ld          tmp1, STACK_C0(sp)
        xorcol      tmp0, Abi, Agi, Aki, Ami, Asi

        /* D[4] = C[3] ^ ROL(C[0], 1) in tmp2; tmp0 = C[2] */
        rori        tmp0, tmp1, 63
        xor         tmp2, tmp2, tmp0
        ld          tmp0, STACK_C2(sp)
        xorcol      tmp2, Abu, Agu, Aku, Amu, Asu

        /* D[1] = C[0] ^ ROL(C[2], 1); the new A[1,0] goes to tmp2 for
         * rho_pi. */
        rori        tmp0, tmp0, 63
        xor         tmp0, tmp0, tmp1
        xor         tmp2, Abe, tmp0
        xor         Age, Age, tmp0
        xor         Ake, Ake, tmp0
        xor         Ame, Ame, tmp0
        xor         Ase, Ase, tmp0
.endm

/* Lane A[x,y] moves to A[y,2x+3y] and is rotated left by r[x,y].
 * Expects A[1,0] in tmp2. */
.macro rho_pi
        rori        Abe, Age, 20            // Abe = ROL(Age, 44)
        rori        Age, Agu, 44            // Age = ROL(Agu, 20)
        rori        Agu, Asi, 3             // Agu = ROL(Asi, 61)
        rori        Asi, Aku, 25            // Asi = ROL(Aku, 39)
        rori        Aku, Asa, 46            // Aku = ROL(Asa, 18)
        rori        Asa, Abi, 2             // Asa = ROL(Abi, 62)
        rori        Abi, Aki, 21            // Abi = ROL(Aki, 43)
        rori        Aki, Ako, 39            // Aki = ROL(Ako, 25)
        rori        Ako, Amu, 56            // Ako = ROL(Amu, 8)
        rori        Amu, Aso, 8             // Amu = ROL(Aso, 56)
        rori        Aso, Ama, 23            // Aso = ROL(Ama, 41)
        rori        Ama, Abu, 37            // Ama = ROL(Abu, 27)
        rori        Abu, Asu, 50            // Abu = ROL(Asu, 14)
        rori        Asu, Ase, 62            // Asu = ROL(Ase, 2)
        rori        Ase, Ago, 9             // Ase = ROL(Ago, 55)
        rori        Ago, Ame, 19            // Ago = ROL(Ame, 45)
        rori        Ame, Aga, 28            // Ame = ROL(Aga, 36)
        rori        Aga, Abo, 36            // Aga = ROL(Abo, 28)
        rori        Abo, Amo, 43            // Abo = ROL(Amo, 21)
        rori        Amo, Ami, 49            // Amo = ROL(Ami, 15)
        rori        Ami, Ake, 54            // Ami = ROL(Ake, 10)
        rori        Ake, Agi, 58            // Ake = ROL(Agi, 6)
        rori        Agi, Aka, 61            // Agi = ROL(Aka, 3)
        rori        Aka, tmp2, 63           // Aka = ROL(Abe, 1)
.endm

/* A[x] ^= ~A[x+1] & A[x+2] for the lanes \a0..\a4 of one plane. The terms
 * for A[3] and A[4], which need the original A[0] and A[1], are computed
 * first; A[0], A[1], A[2] are then updated in place. */
.macro chi_plane a0, a1, a2, a3, a4
        andn        tmp0, \a0, \a4
        andn        tmp1, \a1, \a0
        andn        tmp2, \a2, \a1
        xor         \a0, \a0, tmp2
        andn        tmp2, \a3, \a2
        xor         \a1, \a1, tmp2
        andn        tmp2, \a4, \a3
        xor         \a2, \a2, tmp2
        xor         \a3, \a3, tmp0
        xor         \a4, \a4, tmp1
.endm

.macro chi
        chi_plane   Aba, Abe, Abi, Abo, Abu
        chi_plane   Aga, Age, Agi, Ago, Agu
        chi_plane   Aka, Ake, Aki, Ako, Aku
        chi_plane   Ama, Ame, Ami, Amo, Amu
        chi_plane   Asa, Ase, Asi, Aso, Asu
.endm

/* Load or store the state from/to the address in \base. The lane Aba is
 * also the state pointer register, so it is accessed last. */
.macro access_state op, base
        \op         Abe, 8(\base)
        \op         Abi, 16(\base)
        \op         Abo, 24(\base)
        \op         Abu, 32(\base)
        \op         Aga, 40(\base)
        \op         Age, 48(\base)
        \op         Agi, 56(\base)
        \op         Ago, 64(\base)
        \op         Agu, 72(\base)
        \op         Aka, 80(\base)
        \op         Ake, 88(\base)
        \op         Aki, 96(\base)
        \op         Ako, 104(\base)
        \op         Aku, 112(\base)
        \op         Ama, 120(\base)
        \op         Ame, 128(\base)
        \op         Ami, 136(\base)
        \op         Amo, 144(\base)
        \op         Amu, 152(\base)
        \op         Asa, 160(\base)
        \op         Ase, 168(\base)
        \op         Asi, 176(\base)
        \op         Aso, 184(\base)
        \op         Asu, 192(\base)
        \op         Aba, 0(\base)
.endm

.text
.option push
.option norvc
.option norelax
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_zbb_riscv64_asm)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_zbb_riscv64_asm)

        addi        sp, sp, -STACK_SIZE
        save_gprs
        sd          a0, STACK_STATE(sp)
        sd          a1, STACK_RC(sp)
        addi        tmp0, a1, (24 * 8)
        sd          tmp0, STACK_RC_END(sp)
        access_state ld, a0

mlk_keccak_f1600_x1_zbb_riscv64_loop:
        theta
        rho_pi
        chi
        /* iota */
        ld          tmp0, STACK_RC(sp)
        ld          tmp1, 0(tmp0)
        xor         Aba, Aba, tmp1

        theta
        rho_pi
        chi
        /* iota */
        ld          tmp0, STACK_RC(sp)
        ld          tmp1, 8(tmp0)
        xor         Aba, Aba, tmp1
        addi        tmp0, tmp0, 16
        sd          tmp0, STACK_RC(sp)
        ld          tmp1, STACK_RC_END(sp)
        bne         tmp0, tmp1, mlk_keccak_f1600_x1_zbb_riscv64_loop

        ld          tmp0, STACK_STATE(sp)
        access_state sd, tmp0
        restore_gprs
        addi        sp, sp, STACK_SIZE
        ret
.option pop

MLK_ASM_FN_SIZE(keccak_f1600_x1_zbb_riscv64_asm)

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef Aba
#undef Abe
#undef Abi
#undef Abo
#undef Abu
#undef Aga
#undef Age
#undef Agi
#undef Ago
#undef Agu
#undef Aka
#undef Ake
#undef Aki
#undef Ako
#undef Aku
#undef Ama
#undef Ame
#undef Ami
#undef Amo
#undef Amu
#undef Asa
#undef Ase
#undef Asi
#undef Aso
#undef Asu
#undef tmp0
#undef tmp1
#undef tmp2
#undef STACK_SIZE
#undef STACK_GPRS
#undef STACK_STATE
#undef STACK_RC
#undef STACK_RC_END
#undef STACK_C0
#undef STACK_C2

/* simpasm: footer-start */
#endif /* MLK_SYS_RISCV64 && __riscv_zbb && MLK_FIPS202_RISCV64_NEED_X1_ZBB && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
