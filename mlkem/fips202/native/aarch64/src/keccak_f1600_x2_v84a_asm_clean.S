/*
 * Copyright (c) 2024 The mlkem-native project authors
 * Copyright (c) 2021-2022 Arm Limited
 * Copyright (c) 2022 Matthias Kannwischer
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

//
// Author: Hanno Becker <hanno.becker@arm.com>
// Author: Matthias Kannwischer <matthias@kannwischer.eu>
//
// This implementation is essentially from the paper
//
//   Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64
//   https://eprint.iacr.org/2022/1243
//
// The only difference is interleaving/deinterleaving of Keccak state
// during load and store, so that the caller need not do this.
//

#include "../../../../common.h"
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT) || \
    defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55)

#if defined(__ARM_FEATURE_SHA3)

/****************** REGISTER ALLOCATIONS *******************/

    input_addr    .req x0
    input_rc      .req x1
    const_addr    .req x1
    count         .req x2
    cur_const     .req x3

    /* Mapping of Kecck-f1600 state to vector registers
     * at the beginning and end of each round. */
    Aba     .req v0
    Abe     .req v1
    Abi     .req v2
    Abo     .req v3
    Abu     .req v4
    Aga     .req v5
    Age     .req v6
    Agi     .req v7
    Ago     .req v8
    Agu     .req v9
    Aka     .req v10
    Ake     .req v11
    Aki     .req v12
    Ako     .req v13
    Aku     .req v14
    Ama     .req v15
    Ame     .req v16
    Ami     .req v17
    Amo     .req v18
    Amu     .req v19
    Asa     .req v20
    Ase     .req v21
    Asi     .req v22
    Aso     .req v23
    Asu     .req v24

    /* q-form of the above mapping */
    Abaq    .req q0
    Abeq    .req q1
    Abiq    .req q2
    Aboq    .req q3
    Abuq    .req q4
    Agaq    .req q5
    Ageq    .req q6
    Agiq    .req q7
    Agoq    .req q8
    Aguq    .req q9
    Akaq    .req q10
    Akeq    .req q11
    Akiq    .req q12
    Akoq    .req q13
    Akuq    .req q14
    Amaq    .req q15
    Ameq    .req q16
    Amiq    .req q17
    Amoq    .req q18
    Amuq    .req q19
    Asaq    .req q20
    Aseq    .req q21
    Asiq    .req q22
    Asoq    .req q23
    Asuq    .req q24

    /* C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4],   for x in 0..4 */
    C0 .req v30
    C1 .req v29
    C2 .req v28
    C3 .req v27
    C4 .req v26

    /* E[x] = C[x-1] xor rot(C[x+1],1), for x in 0..4 */
    E0 .req v26
    E1 .req v25
    E2 .req v29
    E3 .req v28
    E4 .req v27

    /* A_[y,2*x+3*y] = rot(A[x,y]) */
    Abi_ .req v2
    Abo_ .req v3
    Abu_ .req v4
    Aga_ .req v10
    Age_ .req v11
    Agi_ .req v7
    Ago_ .req v8
    Agu_ .req v9
    Aka_ .req v15
    Ake_ .req v16
    Aki_ .req v12
    Ako_ .req v13
    Aku_ .req v14
    Ama_ .req v20
    Ame_ .req v21
    Ami_ .req v17
    Amo_ .req v18
    Amu_ .req v19
    Asa_ .req v0
    Ase_ .req v1
    Asi_ .req v22
    Aso_ .req v23
    Asu_ .req v24
    Aba_ .req v30
    Abe_ .req v27

/************************ MACROS ****************************/

.macro load_input
    ld2 {Aba.d, Abe.d}[0], [input_addr], #16
    ld2 {Abi.d, Abo.d}[0], [input_addr], #16
    ld2 {Abu.d, Aga.d}[0], [input_addr], #16
    ld2 {Age.d, Agi.d}[0], [input_addr], #16
    ld2 {Ago.d, Agu.d}[0], [input_addr], #16
    ld2 {Aka.d, Ake.d}[0], [input_addr], #16
    ld2 {Aki.d, Ako.d}[0], [input_addr], #16
    ld2 {Aku.d, Ama.d}[0], [input_addr], #16
    ld2 {Ame.d, Ami.d}[0], [input_addr], #16
    ld2 {Amo.d, Amu.d}[0], [input_addr], #16
    ld2 {Asa.d, Ase.d}[0], [input_addr], #16
    ld2 {Asi.d, Aso.d}[0], [input_addr], #16
    ld1 {Asu.d}[0], [input_addr], #8

    ld2 {Aba.d, Abe.d}[1], [input_addr], #16
    ld2 {Abi.d, Abo.d}[1], [input_addr], #16
    ld2 {Abu.d, Aga.d}[1], [input_addr], #16
    ld2 {Age.d, Agi.d}[1], [input_addr], #16
    ld2 {Ago.d, Agu.d}[1], [input_addr], #16
    ld2 {Aka.d, Ake.d}[1], [input_addr], #16
    ld2 {Aki.d, Ako.d}[1], [input_addr], #16
    ld2 {Aku.d, Ama.d}[1], [input_addr], #16
    ld2 {Ame.d, Ami.d}[1], [input_addr], #16
    ld2 {Amo.d, Amu.d}[1], [input_addr], #16
    ld2 {Asa.d, Ase.d}[1], [input_addr], #16
    ld2 {Asi.d, Aso.d}[1], [input_addr], #16
    ld1 {Asu.d}[1], [input_addr], #8

    sub input_addr, input_addr, #(25*8*2)
.endm

.macro store_input
    st2 {Aba.d, Abe.d}[0], [input_addr], #16
    st2 {Abi.d, Abo.d}[0], [input_addr], #16
    st2 {Abu.d, Aga.d}[0], [input_addr], #16
    st2 {Age.d, Agi.d}[0], [input_addr], #16
    st2 {Ago.d, Agu.d}[0], [input_addr], #16
    st2 {Aka.d, Ake.d}[0], [input_addr], #16
    st2 {Aki.d, Ako.d}[0], [input_addr], #16
    st2 {Aku.d, Ama.d}[0], [input_addr], #16
    st2 {Ame.d, Ami.d}[0], [input_addr], #16
    st2 {Amo.d, Amu.d}[0], [input_addr], #16
    st2 {Asa.d, Ase.d}[0], [input_addr], #16
    st2 {Asi.d, Aso.d}[0], [input_addr], #16
    st1 {Asu.d}[0], [input_addr], #8

    st2 {Aba.d, Abe.d}[1], [input_addr], #16
    st2 {Abi.d, Abo.d}[1], [input_addr], #16
    st2 {Abu.d, Aga.d}[1], [input_addr], #16
    st2 {Age.d, Agi.d}[1], [input_addr], #16
    st2 {Ago.d, Agu.d}[1], [input_addr], #16
    st2 {Aka.d, Ake.d}[1], [input_addr], #16
    st2 {Aki.d, Ako.d}[1], [input_addr], #16
    st2 {Aku.d, Ama.d}[1], [input_addr], #16
    st2 {Ame.d, Ami.d}[1], [input_addr], #16
    st2 {Amo.d, Amu.d}[1], [input_addr], #16
    st2 {Asa.d, Ase.d}[1], [input_addr], #16
    st2 {Asi.d, Aso.d}[1], [input_addr], #16
    st1 {Asu.d}[1], [input_addr], #8
.endm

#define STACK_SIZE (16*4 + 16*6) /* VREGS (16*4) + GPRS (TODO: Remove) */

#define STACK_BASE_GPRS (16*4)
.macro alloc_stack
    sub sp, sp, #(STACK_SIZE)
.endm

.macro free_stack
    add sp, sp, #(STACK_SIZE)
	.endm

.macro save_vregs
    stp  d8,  d9, [sp, #(16*0)]
    stp d10, d11, [sp, #(16*1)]
    stp d12, d13, [sp, #(16*2)]
    stp d14, d15, [sp, #(16*3)]
.endm

.macro restore_vregs
    ldp  d8,  d9, [sp, #(16*0)]
    ldp d10, d11, [sp, #(16*1)]
    ldp d12, d13, [sp, #(16*2)]
    ldp d14, d15, [sp, #(16*3)]
.endm

/* Macros using v8.4-A SHA-3 instructions */

.macro eor3_m0 d s0 s1 s2
    eor3 \d\().16b, \s0\().16b, \s1\().16b, \s2\().16b
.endm

.macro rax1_m0 d s0 s1
    rax1 \d\().2d, \s0\().2d, \s1\().2d
.endm

.macro xar_m0 d s0 s1 imm
    xar \d\().2d, \s0\().2d, \s1\().2d, #\imm
.endm

.macro bcax_m0 d s0 s1 s2
    bcax \d\().16b, \s0\().16b, \s1\().16b, \s2\().16b
.endm

/* Keccak-f1600 round */

.macro keccak_f1600_round

    eor3_m0 C0, Aba, Aga, Aka
    eor3_m0 C1, Abe, Age, Ake
    eor3_m0 C2, Abi, Agi, Aki
    eor3_m0 C3, Abo, Ago, Ako
    eor3_m0 C4, Abu, Agu, Aku
    eor3_m0 C0, C0, Ama,  Asa
    eor3_m0 C1, C1, Ame,  Ase
    eor3_m0 C2, C2, Ami,  Asi
    eor3_m0 C3, C3, Amo,  Aso
    eor3_m0 C4, C4, Amu,  Asu

    rax1_m0 E1, C0, C2
    rax1_m0 E3, C2, C4
    rax1_m0 E0, C4, C1
    rax1_m0 E2, C1, C3
    rax1_m0 E4, C3, C0

    eor Aba_.16b, Aba.16b, E0.16b
    xar_m0 Asa_, Abi, E2, 2
    xar_m0 Abi_, Aki, E2, 21
    xar_m0 Aki_, Ako, E3, 39
    xar_m0 Ako_, Amu, E4, 56
    xar_m0 Amu_, Aso, E3, 8
    xar_m0 Aso_, Ama, E0, 23
    xar_m0 Aka_, Abe, E1, 63
    xar_m0 Ase_, Ago, E3, 9
    xar_m0 Ago_, Ame, E1, 19
    xar_m0 Ake_, Agi, E2, 58
    xar_m0 Agi_, Aka, E0, 61
    xar_m0 Aga_, Abo, E3, 36
    xar_m0 Abo_, Amo, E3, 43
    xar_m0 Amo_, Ami, E2, 49
    xar_m0 Ami_, Ake, E1, 54
    xar_m0 Age_, Agu, E4, 44
    xar_m0 Agu_, Asi, E2, 3
    xar_m0 Asi_, Aku, E4, 25
    xar_m0 Aku_, Asa, E0, 46
    xar_m0 Ama_, Abu, E4, 37
    xar_m0 Abu_, Asu, E4, 50
    xar_m0 Asu_, Ase, E1, 62
    xar_m0 Ame_, Aga, E0, 28
    xar_m0 Abe_, Age, E1, 20

    ld1r {v31.2d}, [const_addr], #8

    bcax_m0 Aga, Aga_, Agi_, Age_
    bcax_m0 Age, Age_, Ago_, Agi_
    bcax_m0 Agi, Agi_, Agu_, Ago_
    bcax_m0 Ago, Ago_, Aga_, Agu_
    bcax_m0 Agu, Agu_, Age_, Aga_
    bcax_m0 Aka, Aka_, Aki_, Ake_
    bcax_m0 Ake, Ake_, Ako_, Aki_
    bcax_m0 Aki, Aki_, Aku_, Ako_
    bcax_m0 Ako, Ako_, Aka_, Aku_
    bcax_m0 Aku, Aku_, Ake_, Aka_
    bcax_m0 Ama, Ama_, Ami_, Ame_
    bcax_m0 Ame, Ame_, Amo_, Ami_
    bcax_m0 Ami, Ami_, Amu_, Amo_
    bcax_m0 Amo, Amo_, Ama_, Amu_
    bcax_m0 Amu, Amu_, Ame_, Ama_
    bcax_m0 Asa, Asa_, Asi_, Ase_
    bcax_m0 Ase, Ase_, Aso_, Asi_
    bcax_m0 Asi, Asi_, Asu_, Aso_
    bcax_m0 Aso, Aso_, Asa_, Asu_
    bcax_m0 Asu, Asu_, Ase_, Asa_
    bcax_m0 Aba, Aba_, Abi_, Abe_
    bcax_m0 Abe, Abe_, Abo_, Abi_
    bcax_m0 Abi, Abi_, Abu_, Abo_
    bcax_m0 Abo, Abo_, Aba_, Abu_
    bcax_m0 Abu, Abu_, Abe_, Aba_

    // iota step
    eor Aba.16b, Aba.16b, v31.16b

.endm

#define KECCAK_F1600_ROUNDS 24

.text
.align 4
.global FIPS202_ASM_NAMESPACE(keccak_f1600_x2_v84a_asm_clean)

FIPS202_ASM_NAMESPACE(keccak_f1600_x2_v84a_asm_clean):
    alloc_stack
    save_vregs
    mov const_addr, input_rc
    load_input

    mov count, #(KECCAK_F1600_ROUNDS)
loop:
    keccak_f1600_round
    sub count, count, #1
    cbnz count, loop

    store_input
    restore_vregs
    free_stack
    ret

#endif

#endif
