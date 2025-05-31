/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) 2021-2022 Arm Limited
 * Copyright (c) 2022 Matthias Kannwischer
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

//
// Author: Hanno Becker <hanno.becker@arm.com>
// Author: Matthias Kannwischer <matthias@kannwischer.eu>
//

#include "../../../../common.h"
#if defined(MLK_FIPS202_AARCH64_NEED_X1_SCALAR) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

/****************** REGISTER ALLOCATIONS *******************/

    input_addr     .req x0
    input_rc       .req x1
    const_addr     .req x26

    /* Mapping of Kecck-f1600 state to scalar registers
     * at the beginning and end of each round. */
    Aba     .req x1
    Abe     .req x6
    Abi     .req x11
    Abo     .req x16
    Abu     .req x21
    Aga     .req x2
    Age     .req x7
    Agi     .req x12
    Ago     .req x17
    Agu     .req x22
    Aka     .req x3
    Ake     .req x8
    Aki     .req x13
    Ako     .req x28
    Aku     .req x23
    Ama     .req x4
    Ame     .req x9
    Ami     .req x14
    Amo     .req x19
    Amu     .req x24
    Asa     .req x5
    Ase     .req x10
    Asi     .req x15
    Aso     .req x20
    Asu     .req x25

/************************ MACROS ****************************/

/* Allocate a large number of stack slots by default so one can quickly
 * check functional correctness by stopping SLOTHY's register allocation
 * and stack spilling process while still using a large number of spills.
 *
 * NOTE:
 * This should to be manually trimmed to the number of stack locations
 * actually used after running SLOTHY.
 */
#define STACK_LOCS 40

// GPRs (16*6), count (8), const (8), input (8), padding (8)
#define STACK_SIZE (16*6 + 3*8 + 8 + (STACK_LOCS) * 8)
#define STACK_BASE_GPRS (3*8+8)
#define STACK_LOC_INPUT (0*8)
#define STACK_LOC_CONST (1*8)
#define STACK_LOC_COUNT (2*8)
#define STACK_LOC_MISC  (16*6 + 4*8)

#define STACK_LOC_0 ((STACK_LOC_MISC) + 0*8)
#define STACK_LOC_1 ((STACK_LOC_MISC) + 1*8)
#define STACK_LOC_2 ((STACK_LOC_MISC) + 2*8)
#define STACK_LOC_3 ((STACK_LOC_MISC) + 3*8)
#define STACK_LOC_4 ((STACK_LOC_MISC) + 4*8)
#define STACK_LOC_5 ((STACK_LOC_MISC) + 5*8)
#define STACK_LOC_6 ((STACK_LOC_MISC) + 6*8)
#define STACK_LOC_7 ((STACK_LOC_MISC) + 7*8)
#define STACK_LOC_8 ((STACK_LOC_MISC) + 8*8)
#define STACK_LOC_9 ((STACK_LOC_MISC) + 9*8)
#define STACK_LOC_10 ((STACK_LOC_MISC) + 10*8)
#define STACK_LOC_11 ((STACK_LOC_MISC) + 11*8)
#define STACK_LOC_12 ((STACK_LOC_MISC) + 12*8)
#define STACK_LOC_13 ((STACK_LOC_MISC) + 13*8)
#define STACK_LOC_14 ((STACK_LOC_MISC) + 14*8)
#define STACK_LOC_15 ((STACK_LOC_MISC) + 15*8)
#define STACK_LOC_16 ((STACK_LOC_MISC) + 16*8)
#define STACK_LOC_17 ((STACK_LOC_MISC) + 17*8)
#define STACK_LOC_18 ((STACK_LOC_MISC) + 18*8)
#define STACK_LOC_19 ((STACK_LOC_MISC) + 19*8)
#define STACK_LOC_20 ((STACK_LOC_MISC) + 20*8)
#define STACK_LOC_21 ((STACK_LOC_MISC) + 21*8)
#define STACK_LOC_22 ((STACK_LOC_MISC) + 22*8)
#define STACK_LOC_23 ((STACK_LOC_MISC) + 23*8)
#define STACK_LOC_24 ((STACK_LOC_MISC) + 24*8)
#define STACK_LOC_25 ((STACK_LOC_MISC) + 25*8)
#define STACK_LOC_26 ((STACK_LOC_MISC) + 26*8)
#define STACK_LOC_27 ((STACK_LOC_MISC) + 27*8)
#define STACK_LOC_28 ((STACK_LOC_MISC) + 28*8)
#define STACK_LOC_29 ((STACK_LOC_MISC) + 29*8)
#define STACK_LOC_30 ((STACK_LOC_MISC) + 30*8)
#define STACK_LOC_31 ((STACK_LOC_MISC) + 31*8)
#define STACK_LOC_32 ((STACK_LOC_MISC) + 32*8)
#define STACK_LOC_33 ((STACK_LOC_MISC) + 33*8)
#define STACK_LOC_34 ((STACK_LOC_MISC) + 34*8)
#define STACK_LOC_35 ((STACK_LOC_MISC) + 35*8)
#define STACK_LOC_36 ((STACK_LOC_MISC) + 36*8)
#define STACK_LOC_37 ((STACK_LOC_MISC) + 37*8)
#define STACK_LOC_38 ((STACK_LOC_MISC) + 38*8)
#define STACK_LOC_39 ((STACK_LOC_MISC) + 39*8)

.macro alloc_stack
    sub sp, sp, #(STACK_SIZE)
.endm

.macro free_stack
    add sp, sp, #(STACK_SIZE)
.endm

.macro save_gprs
    stp x19, x20, [sp, #(STACK_BASE_GPRS + 16*0)]
    stp x21, x22, [sp, #(STACK_BASE_GPRS + 16*1)]
    stp x23, x24, [sp, #(STACK_BASE_GPRS + 16*2)]
    stp x25, x26, [sp, #(STACK_BASE_GPRS + 16*3)]
    stp x27, x28, [sp, #(STACK_BASE_GPRS + 16*4)]
    stp x29, x30, [sp, #(STACK_BASE_GPRS + 16*5)]
.endm

.macro restore_gprs
    ldp x19, x20, [sp, #(STACK_BASE_GPRS + 16*0)]
    ldp x21, x22, [sp, #(STACK_BASE_GPRS + 16*1)]
    ldp x23, x24, [sp, #(STACK_BASE_GPRS + 16*2)]
    ldp x25, x26, [sp, #(STACK_BASE_GPRS + 16*3)]
    ldp x27, x28, [sp, #(STACK_BASE_GPRS + 16*4)]
    ldp x29, x30, [sp, #(STACK_BASE_GPRS + 16*5)]
.endm

.macro eor5 dst, src0, src1, src2, src3, src4
    eor \dst, \src0, \src1
    eor \dst, \dst,  \src2
    eor \dst, \dst,  \src3
    eor \dst, \dst,  \src4
.endm

.macro  chi_step_ror out, a, b, c, r1, r2
    bic X<tmp>, \b\(), \c\(), ror #\r1
    eor \out\(), X<tmp>, \a\(), ror #\r2
.endm

.macro  chi_step_ror2 out, a, b, c, r1, r2
    bic X<tmp>, \b\(), \c\(), ror #\r1
    eor \out\(), \a\(), X<tmp>, ror #\r2
.endm

.macro keccak_f1600_round_initial
    eor5 X<C0>, Ama, Asa, Aba, Aga, Aka
    eor5 X<C1>, Ame, Ase, Abe, Age, Ake
    eor5 X<C2>, Ami, Asi, Abi, Agi, Aki
    eor5 X<C3>, Amo, Aso, Abo, Ago, Ako
    eor5 X<C4>, Amu, Asu, Abu, Agu, Aku

    eor X<E1>, X<C0>, X<C2>, ror #63
    eor X<E3>, X<C2>, X<C4>, ror #63
    eor X<E0>, X<C4>, X<C1>, ror #63
    eor X<E2>, X<C1>, X<C3>, ror #63
    eor X<E4>, X<C3>, X<C0>, ror #63

    eor X<Bba>, Aba, X<E0>
    eor X<Bsa>, Abi, X<E2>
    eor X<Bbi>, Aki, X<E2>
    eor X<Bki>, Ako, X<E3>
    eor X<Bko>, Amu, X<E4>
    eor X<Bmu>, Aso, X<E3>
    eor X<Bso>, Ama, X<E0>
    eor X<Bka>, Abe, X<E1>
    eor X<Bse>, Ago, X<E3>
    eor X<Bgo>, Ame, X<E1>
    eor X<Bke>, Agi, X<E2>
    eor X<Bgi>, Aka, X<E0>
    eor X<Bga>, Abo, X<E3>
    eor X<Bbo>, Amo, X<E3>
    eor X<Bmo>, Ami, X<E2>
    eor X<Bmi>, Ake, X<E1>
    eor X<Bge>, Agu, X<E4>
    eor X<Bgu>, Asi, X<E2>
    eor X<Bsi>, Aku, X<E4>
    eor X<Bku>, Asa, X<E0>
    eor X<Bma>, Abu, X<E4>
    eor X<Bbu>, Asu, X<E4>
    eor X<Bsu>, Ase, X<E1>
    eor X<Bme>, Aga, X<E0>
    eor X<Bbe>, Age, X<E1>

    ldr X<caddr>, [sp, #STACK_LOC_CONST]
    ldr X<cur_const>, [X<caddr>]
    mov X<count>, #1
    str X<count>, [sp, #STACK_LOC_COUNT] // @slothy:writes=STACK_LOC_COUNT

    chi_step_ror Aga, X<Bga>, X<Bgi>, X<Bge>, 47, 39
    chi_step_ror Age, X<Bge>, X<Bgo>, X<Bgi>, 42, 25
    chi_step_ror Agi, X<Bgi>, X<Bgu>, X<Bgo>, 16, 58
    chi_step_ror Ago, X<Bgo>, X<Bga>, X<Bgu>, 31, 47
    chi_step_ror Agu, X<Bgu>, X<Bge>, X<Bga>, 56, 23
    chi_step_ror Aka, X<Bka>, X<Bki>, X<Bke>, 19, 24
    chi_step_ror Ake, X<Bke>, X<Bko>, X<Bki>, 47, 2
    chi_step_ror Aki, X<Bki>, X<Bku>, X<Bko>, 10, 57
    chi_step_ror Ako, X<Bko>, X<Bka>, X<Bku>, 47, 57
    chi_step_ror Aku, X<Bku>, X<Bke>, X<Bka>, 5,  52
    chi_step_ror Ama, X<Bma>, X<Bmi>, X<Bme>, 38, 47
    chi_step_ror Ame, X<Bme>, X<Bmo>, X<Bmi>, 5,  43
    chi_step_ror Ami, X<Bmi>, X<Bmu>, X<Bmo>, 41, 46
    chi_step_ror Amo, X<Bmo>, X<Bma>, X<Bmu>, 35, 12
    chi_step_ror Amu, X<Bmu>, X<Bme>, X<Bma>, 9,  44
    chi_step_ror Asa, X<Bsa>, X<Bsi>, X<Bse>, 48, 41
    chi_step_ror Ase, X<Bse>, X<Bso>, X<Bsi>, 2,  50
    chi_step_ror Asi, X<Bsi>, X<Bsu>, X<Bso>, 25, 27
    chi_step_ror Aso, X<Bso>, X<Bsa>, X<Bsu>, 60, 21
    chi_step_ror Asu, X<Bsu>, X<Bse>, X<Bsa>, 57, 53
    chi_step_ror2 Aba, X<Bba>, X<Bbi>, X<Bbe>, 63, 21
    chi_step_ror Abe, X<Bbe>, X<Bbo>, X<Bbi>, 42, 41
    chi_step_ror Abi, X<Bbi>, X<Bbu>, X<Bbo>, 57, 35
    chi_step_ror Abo, X<Bbo>, X<Bba>, X<Bbu>, 50, 43
    chi_step_ror Abu, X<Bbu>, X<Bbe>, X<Bba>, 44, 30

    eor Aba, Aba, X<cur_const>

.endm

.macro keccak_f1600_round_noninitial

    eor X<C0>, Aba,   Aga, ror #61
    eor X<C0>, X<C0>, Ama, ror #54
    eor X<C0>, X<C0>, Aka, ror #39
    eor X<C0>, X<C0>, Asa, ror #25

    eor X<C1>, Ake,   Ame, ror #57
    eor X<C1>, X<C1>, Abe, ror #51
    eor X<C1>, X<C1>, Ase, ror #31
    eor X<C1>, X<C1>, Age, ror #27

    eor X<C2>, Asi,   Abi, ror #52
    eor X<C2>, X<C2>, Aki, ror #48
    eor X<C2>, X<C2>, Ami, ror #10
    eor X<C2>, X<C2>, Agi, ror #5

    eor X<C3>, Abo,   Ako, ror #63
    eor X<C3>, X<C3>, Amo, ror #37
    eor X<C3>, X<C3>, Ago, ror #36
    eor X<C3>, X<C3>, Aso, ror #2

    eor X<C4>, Aku,   Agu, ror #50
    eor X<C4>, X<C4>, Amu, ror #34
    eor X<C4>, X<C4>, Abu, ror #26
    eor X<C4>, X<C4>, Asu, ror #15

    eor X<E1>, X<C0>, X<C2>, ror #61
    ror X<C2>, X<C2>, #62
    eor X<E3>, X<C2>, X<C4>, ror #57
    ror X<C4>, X<C4>, #58
    eor X<E0>, X<C4>, X<C1>, ror #55
    ror X<C1>, X<C1>, #56
    eor X<E2>, X<C1>, X<C3>, ror #63
    eor X<E4>, X<C3>, X<C0>, ror #63

    eor X<Bba>, X<E0>, Aba
    eor X<Bsa>, X<E2>, Abi, ror #50
    eor X<Bbi>, X<E2>, Aki, ror #46
    eor X<Bki>, X<E3>, Ako, ror #63
    eor X<Bko>, X<E4>, Amu, ror #28
    eor X<Bmu>, X<E3>, Aso, ror #2
    eor X<Bso>, X<E0>, Ama, ror #54
    eor X<Bka>, X<E1>, Abe, ror #43
    eor X<Bse>, X<E3>, Ago, ror #36
    eor X<Bgo>, X<E1>, Ame, ror #49
    eor X<Bke>, X<E2>, Agi, ror #3
    eor X<Bgi>, X<E0>, Aka, ror #39
    eor X<Bga>, X<E3>, Abo
    eor X<Bbo>, X<E3>, Amo, ror #37
    eor X<Bmo>, X<E2>, Ami, ror #8
    eor X<Bmi>, X<E1>, Ake, ror #56
    eor X<Bge>, X<E4>, Agu, ror #44
    eor X<Bgu>, X<E2>, Asi, ror #62
    eor X<Bsi>, X<E4>, Aku, ror #58
    eor X<Bku>, X<E0>, Asa, ror #25
    eor X<Bma>, X<E4>, Abu, ror #20
    eor X<Bbu>, X<E4>, Asu, ror #9
    eor X<Bsu>, X<E1>, Ase, ror #23
    eor X<Bme>, X<E0>, Aga, ror #61
    eor X<Bbe>, X<E1>, Age, ror #19

    ldr X<caddr>, [sp, #STACK_LOC_CONST]
    ldr X<count>, [sp, #STACK_LOC_COUNT] // @slothy:reads=STACK_LOC_COUNT
    ldr X<cur_const>, [X<caddr>, X<count>, LSL #3]
    add X<count>, X<count>, #1
    cmp X<count>, #(KECCAK_F1600_ROUNDS-1) // @slothy:ignore_useless_output
    str X<count>, [sp, #STACK_LOC_COUNT] // @slothy:writes=STACK_LOC_COUNT

    chi_step_ror Aga, X<Bga>, X<Bgi>, X<Bge>, 47, 39
    chi_step_ror Age, X<Bge>, X<Bgo>, X<Bgi>, 42, 25
    chi_step_ror Agi, X<Bgi>, X<Bgu>, X<Bgo>, 16, 58
    chi_step_ror Ago, X<Bgo>, X<Bga>, X<Bgu>, 31, 47
    chi_step_ror Agu, X<Bgu>, X<Bge>, X<Bga>, 56, 23
    chi_step_ror Aka, X<Bka>, X<Bki>, X<Bke>, 19, 24
    chi_step_ror Ake, X<Bke>, X<Bko>, X<Bki>, 47, 2
    chi_step_ror Aki, X<Bki>, X<Bku>, X<Bko>, 10, 57
    chi_step_ror Ako, X<Bko>, X<Bka>, X<Bku>, 47, 57
    chi_step_ror Aku, X<Bku>, X<Bke>, X<Bka>, 5,  52
    chi_step_ror Ama, X<Bma>, X<Bmi>, X<Bme>, 38, 47
    chi_step_ror Ame, X<Bme>, X<Bmo>, X<Bmi>, 5,  43
    chi_step_ror Ami, X<Bmi>, X<Bmu>, X<Bmo>, 41, 46
    chi_step_ror Amo, X<Bmo>, X<Bma>, X<Bmu>, 35, 12
    chi_step_ror Amu, X<Bmu>, X<Bme>, X<Bma>, 9,  44
    chi_step_ror Asa, X<Bsa>, X<Bsi>, X<Bse>, 48, 41
    chi_step_ror Ase, X<Bse>, X<Bso>, X<Bsi>, 2,  50
    chi_step_ror Asi, X<Bsi>, X<Bsu>, X<Bso>, 25, 27
    chi_step_ror Aso, X<Bso>, X<Bsa>, X<Bsu>, 60, 21
    chi_step_ror Asu, X<Bsu>, X<Bse>, X<Bsa>, 57, 53
    chi_step_ror2 Aba, X<Bba>, X<Bbi>, X<Bbe>, 63, 21
    chi_step_ror Abe, X<Bbe>, X<Bbo>, X<Bbi>, 42, 41
    chi_step_ror Abi, X<Bbi>, X<Bbu>, X<Bbo>, 57, 35
    chi_step_ror Abo, X<Bbo>, X<Bba>, X<Bbu>, 50, 43
    chi_step_ror Abu, X<Bbu>, X<Bbe>, X<Bba>, 44, 30

    eor Aba, Aba, X<cur_const>
.endm

.macro load_state
    ldp Aba, Abe, [input_addr, #(1*8*0)]
    ldp Abi, Abo, [input_addr, #(1*8*2)]
    ldp Abu, Aga, [input_addr, #(1*8*4)]
    ldp Age, Agi, [input_addr, #(1*8*6)]
    ldp Ago, Agu, [input_addr, #(1*8*8)]
    ldp Aka, Ake, [input_addr, #(1*8*10)]
    ldp Aki, Ako, [input_addr, #(1*8*12)]
    ldp Aku, Ama, [input_addr, #(1*8*14)]
    ldp Ame, Ami, [input_addr, #(1*8*16)]
    ldp Amo, Amu, [input_addr, #(1*8*18)]
    ldp Asa, Ase, [input_addr, #(1*8*20)]
    ldp Asi, Aso, [input_addr, #(1*8*22)]
    ldr Asu,      [input_addr, #(1*8*24)]
.endm

.macro store_state
    stp Aba, Abe, [input_addr, #(1*8*0)]
    stp Abi, Abo, [input_addr, #(1*8*2)]
    stp Abu, Aga, [input_addr, #(1*8*4)]
    stp Age, Agi, [input_addr, #(1*8*6)]
    stp Ago, Agu, [input_addr, #(1*8*8)]
    stp Aka, Ake, [input_addr, #(1*8*10)]
    stp Aki, Ako, [input_addr, #(1*8*12)]
    stp Aku, Ama, [input_addr, #(1*8*14)]
    stp Ame, Ami, [input_addr, #(1*8*16)]
    stp Amo, Amu, [input_addr, #(1*8*18)]
    stp Asa, Ase, [input_addr, #(1*8*20)]
    stp Asi, Aso, [input_addr, #(1*8*22)]
    str Asu,      [input_addr, #(1*8*24)]
.endm

.macro final_rotate
    ror Abe, Abe,#(64-21)
    ror Abi, Abi,#(64-14)
    ror Abu, Abu,#(64-44)
    ror Aga, Aga,#(64-3)
    ror Age, Age,#(64-45)
    ror Agi, Agi,#(64-61)
    ror Ago, Ago,#(64-28)
    ror Agu, Agu,#(64-20)
    ror Aka, Aka,#(64-25)
    ror Ake, Ake,#(64-8)
    ror Aki, Aki,#(64-18)
    ror Ako, Ako,#(64-1)
    ror Aku, Aku,#(64-6)
    ror Ama, Ama,#(64-10)
    ror Ame, Ame,#(64-15)
    ror Ami, Ami,#(64-56)
    ror Amo, Amo,#(64-27)
    ror Amu, Amu,#(64-36)
    ror Asa, Asa,#(64-39)
    ror Ase, Ase,#(64-41)
    ror Asi, Asi,#(64-2)
    ror Aso, Aso,#(64-62)
    ror Asu, Asu,#(64-55)
.endm

#define KECCAK_F1600_ROUNDS 24

    .text
    .global MLK_ASM_NAMESPACE(keccak_f1600_x1_scalar_asm)
    .balign 4
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_scalar_asm)
    alloc_stack
    save_gprs

keccak_f1600_x1_scalar_initial:
    mov const_addr, input_rc
    str input_rc, [sp, #STACK_LOC_CONST]
    load_state
    str input_addr, [sp, #STACK_LOC_INPUT] // @slothy:writes=STACK_LOC_INPUT

keccak_f1600_x1_scalar_initial_start:
   keccak_f1600_round_initial

keccak_f1600_x1_scalar_loop:
    keccak_f1600_round_noninitial
keccak_f1600_x1_scalar_end_loop:
    ble keccak_f1600_x1_scalar_loop

keccak_f1600_x1_scalar_final:
    final_rotate
    ldr input_addr, [sp, #STACK_LOC_INPUT] // @slothy:reads=STACK_LOC_INPUT
    store_state
keccak_f1600_x1_scalar_end_final:

    restore_gprs
    free_stack
    ret

/****************** REGISTER DEALLOCATIONS *******************/
    .unreq input_addr
    .unreq input_rc
    .unreq const_addr
    .unreq Aba
    .unreq Abe
    .unreq Abi
    .unreq Abo
    .unreq Abu
    .unreq Aga
    .unreq Age
    .unreq Agi
    .unreq Ago
    .unreq Agu
    .unreq Aka
    .unreq Ake
    .unreq Aki
    .unreq Ako
    .unreq Aku
    .unreq Ama
    .unreq Ame
    .unreq Ami
    .unreq Amo
    .unreq Amu
    .unreq Asa
    .unreq Ase
    .unreq Asi
    .unreq Aso
    .unreq Asu

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef STACK_LOCS
#undef STACK_SIZE
#undef STACK_BASE_GPRS
#undef STACK_LOC_INPUT
#undef STACK_LOC_CONST
#undef STACK_LOC_COUNT
#undef STACK_LOC_MISC
#undef STACK_LOC_0
#undef STACK_LOC_1
#undef STACK_LOC_2
#undef STACK_LOC_3
#undef STACK_LOC_4
#undef STACK_LOC_5
#undef STACK_LOC_6
#undef STACK_LOC_7
#undef STACK_LOC_8
#undef STACK_LOC_9
#undef STACK_LOC_10
#undef STACK_LOC_11
#undef STACK_LOC_12
#undef STACK_LOC_13
#undef STACK_LOC_14
#undef STACK_LOC_15
#undef STACK_LOC_16
#undef STACK_LOC_17
#undef STACK_LOC_18
#undef STACK_LOC_19
#undef STACK_LOC_20
#undef STACK_LOC_21
#undef STACK_LOC_22
#undef STACK_LOC_23
#undef STACK_LOC_24
#undef STACK_LOC_25
#undef STACK_LOC_26
#undef STACK_LOC_27
#undef STACK_LOC_28
#undef STACK_LOC_29
#undef STACK_LOC_30
#undef STACK_LOC_31
#undef STACK_LOC_32
#undef STACK_LOC_33
#undef STACK_LOC_34
#undef STACK_LOC_35
#undef STACK_LOC_36
#undef STACK_LOC_37
#undef STACK_LOC_38
#undef STACK_LOC_39
#undef KECCAK_F1600_ROUNDS

/* simpasm: footer-start */
#endif /* MLK_FIPS202_AARCH64_NEED_X1_SCALAR && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
