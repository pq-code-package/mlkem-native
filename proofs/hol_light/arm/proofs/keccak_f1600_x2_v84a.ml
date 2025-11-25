(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 2-way batch Keccak-f1600 vector code.                                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/keccak_spec.ml";;

(**** print_literal_from_elf "arm/mlkem/keccak_f1600_x2_v84a.o";;
 ****)

let keccak_f1600_x2_v84a_mc = define_assert_from_elf
  "keccak_f1600_x2_v84a_mc" "arm/mlkem/keccak_f1600_x2_v84a.o"
(*** BYTECODE START ***)
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x91032002;       (* arm_ADD X2 X0 (rvalue (word 200)) *)
  0xad406819;       (* arm_LDP Q25 Q26 X0 (Immediate_Offset (iword (&0))) *)
  0xad40705b;       (* arm_LDP Q27 Q28 X2 (Immediate_Offset (iword (&0))) *)
  0x4edb2b20;       (* arm_TRN1 Q0 Q25 Q27 64 128 *)
  0x4edb6b21;       (* arm_TRN2 Q1 Q25 Q27 64 128 *)
  0x4edc2b42;       (* arm_TRN1 Q2 Q26 Q28 64 128 *)
  0x4edc6b43;       (* arm_TRN2 Q3 Q26 Q28 64 128 *)
  0xad416819;       (* arm_LDP Q25 Q26 X0 (Immediate_Offset (iword (&32))) *)
  0xad41705b;       (* arm_LDP Q27 Q28 X2 (Immediate_Offset (iword (&32))) *)
  0x4edb2b24;       (* arm_TRN1 Q4 Q25 Q27 64 128 *)
  0x4edb6b25;       (* arm_TRN2 Q5 Q25 Q27 64 128 *)
  0x4edc2b46;       (* arm_TRN1 Q6 Q26 Q28 64 128 *)
  0x4edc6b47;       (* arm_TRN2 Q7 Q26 Q28 64 128 *)
  0xad426819;       (* arm_LDP Q25 Q26 X0 (Immediate_Offset (iword (&64))) *)
  0xad42705b;       (* arm_LDP Q27 Q28 X2 (Immediate_Offset (iword (&64))) *)
  0x4edb2b28;       (* arm_TRN1 Q8 Q25 Q27 64 128 *)
  0x4edb6b29;       (* arm_TRN2 Q9 Q25 Q27 64 128 *)
  0x4edc2b4a;       (* arm_TRN1 Q10 Q26 Q28 64 128 *)
  0x4edc6b4b;       (* arm_TRN2 Q11 Q26 Q28 64 128 *)
  0xad436819;       (* arm_LDP Q25 Q26 X0 (Immediate_Offset (iword (&96))) *)
  0xad43705b;       (* arm_LDP Q27 Q28 X2 (Immediate_Offset (iword (&96))) *)
  0x4edb2b2c;       (* arm_TRN1 Q12 Q25 Q27 64 128 *)
  0x4edb6b2d;       (* arm_TRN2 Q13 Q25 Q27 64 128 *)
  0x4edc2b4e;       (* arm_TRN1 Q14 Q26 Q28 64 128 *)
  0x4edc6b4f;       (* arm_TRN2 Q15 Q26 Q28 64 128 *)
  0xad446819;       (* arm_LDP Q25 Q26 X0 (Immediate_Offset (iword (&128))) *)
  0xad44705b;       (* arm_LDP Q27 Q28 X2 (Immediate_Offset (iword (&128))) *)
  0x4edb2b30;       (* arm_TRN1 Q16 Q25 Q27 64 128 *)
  0x4edb6b31;       (* arm_TRN2 Q17 Q25 Q27 64 128 *)
  0x4edc2b52;       (* arm_TRN1 Q18 Q26 Q28 64 128 *)
  0x4edc6b53;       (* arm_TRN2 Q19 Q26 Q28 64 128 *)
  0xad456819;       (* arm_LDP Q25 Q26 X0 (Immediate_Offset (iword (&160))) *)
  0xad45705b;       (* arm_LDP Q27 Q28 X2 (Immediate_Offset (iword (&160))) *)
  0x4edb2b34;       (* arm_TRN1 Q20 Q25 Q27 64 128 *)
  0x4edb6b35;       (* arm_TRN2 Q21 Q25 Q27 64 128 *)
  0x4edc2b56;       (* arm_TRN1 Q22 Q26 Q28 64 128 *)
  0x4edc6b57;       (* arm_TRN2 Q23 Q26 Q28 64 128 *)
  0xfd406019;       (* arm_LDR D25 X0 (Immediate_Offset (word 192)) *)
  0xfd40605b;       (* arm_LDR D27 X2 (Immediate_Offset (word 192)) *)
  0x4edb2b38;       (* arm_TRN1 Q24 Q25 Q27 64 128 *)
  0xd2800302;       (* arm_MOV X2 (rvalue (word 24)) *)
  0xce05281e;       (* arm_EOR3 Q30 Q0 Q5 Q10 *)
  0xce062c3d;       (* arm_EOR3 Q29 Q1 Q6 Q11 *)
  0xce07305c;       (* arm_EOR3 Q28 Q2 Q7 Q12 *)
  0xce08347b;       (* arm_EOR3 Q27 Q3 Q8 Q13 *)
  0xce09389a;       (* arm_EOR3 Q26 Q4 Q9 Q14 *)
  0xce0f53de;       (* arm_EOR3 Q30 Q30 Q15 Q20 *)
  0xce1057bd;       (* arm_EOR3 Q29 Q29 Q16 Q21 *)
  0xce115b9c;       (* arm_EOR3 Q28 Q28 Q17 Q22 *)
  0xce125f7b;       (* arm_EOR3 Q27 Q27 Q18 Q23 *)
  0xce13635a;       (* arm_EOR3 Q26 Q26 Q19 Q24 *)
  0xce7c8fd9;       (* arm_RAX1 Q25 Q30 Q28 *)
  0xce7a8f9c;       (* arm_RAX1 Q28 Q28 Q26 *)
  0xce7d8f5a;       (* arm_RAX1 Q26 Q26 Q29 *)
  0xce7b8fbd;       (* arm_RAX1 Q29 Q29 Q27 *)
  0xce7e8f7b;       (* arm_RAX1 Q27 Q27 Q30 *)
  0x6e3a1c1e;       (* arm_EOR_VEC Q30 Q0 Q26 128 *)
  0xce9d0840;       (* arm_XAR Q0 Q2 Q29 (word 2) *)
  0xce9d5582;       (* arm_XAR Q2 Q12 Q29 (word 21) *)
  0xce9c9dac;       (* arm_XAR Q12 Q13 Q28 (word 39) *)
  0xce9be26d;       (* arm_XAR Q13 Q19 Q27 (word 56) *)
  0xce9c22f3;       (* arm_XAR Q19 Q23 Q28 (word 8) *)
  0xce9a5df7;       (* arm_XAR Q23 Q15 Q26 (word 23) *)
  0xce99fc2f;       (* arm_XAR Q15 Q1 Q25 (word 63) *)
  0xce9c2501;       (* arm_XAR Q1 Q8 Q28 (word 9) *)
  0xce994e08;       (* arm_XAR Q8 Q16 Q25 (word 19) *)
  0xce9de8f0;       (* arm_XAR Q16 Q7 Q29 (word 58) *)
  0xce9af547;       (* arm_XAR Q7 Q10 Q26 (word 61) *)
  0xce9c906a;       (* arm_XAR Q10 Q3 Q28 (word 36) *)
  0xce9cae43;       (* arm_XAR Q3 Q18 Q28 (word 43) *)
  0xce9dc632;       (* arm_XAR Q18 Q17 Q29 (word 49) *)
  0xce99d971;       (* arm_XAR Q17 Q11 Q25 (word 54) *)
  0xce9bb12b;       (* arm_XAR Q11 Q9 Q27 (word 44) *)
  0xce9d0ec9;       (* arm_XAR Q9 Q22 Q29 (word 3) *)
  0xce9b65d6;       (* arm_XAR Q22 Q14 Q27 (word 25) *)
  0xce9aba8e;       (* arm_XAR Q14 Q20 Q26 (word 46) *)
  0xce9b9494;       (* arm_XAR Q20 Q4 Q27 (word 37) *)
  0xce9bcb04;       (* arm_XAR Q4 Q24 Q27 (word 50) *)
  0xce99fab8;       (* arm_XAR Q24 Q21 Q25 (word 62) *)
  0xce9a70b5;       (* arm_XAR Q21 Q5 Q26 (word 28) *)
  0xce9950db;       (* arm_XAR Q27 Q6 Q25 (word 20) *)
  0x4ddfcc3f;       (* arm_LD1R Q31 X1 (Postimmediate_Offset (word 8)) 64 128 *)
  0xce272d45;       (* arm_BCAX Q5 Q10 Q7 Q11 *)
  0xce281d66;       (* arm_BCAX Q6 Q11 Q8 Q7 *)
  0xce2920e7;       (* arm_BCAX Q7 Q7 Q9 Q8 *)
  0xce2a2508;       (* arm_BCAX Q8 Q8 Q10 Q9 *)
  0xce2b2929;       (* arm_BCAX Q9 Q9 Q11 Q10 *)
  0xce2c41ea;       (* arm_BCAX Q10 Q15 Q12 Q16 *)
  0xce2d320b;       (* arm_BCAX Q11 Q16 Q13 Q12 *)
  0xce2e358c;       (* arm_BCAX Q12 Q12 Q14 Q13 *)
  0xce2f39ad;       (* arm_BCAX Q13 Q13 Q15 Q14 *)
  0xce303dce;       (* arm_BCAX Q14 Q14 Q16 Q15 *)
  0xce31568f;       (* arm_BCAX Q15 Q20 Q17 Q21 *)
  0xce3246b0;       (* arm_BCAX Q16 Q21 Q18 Q17 *)
  0xce334a31;       (* arm_BCAX Q17 Q17 Q19 Q18 *)
  0xce344e52;       (* arm_BCAX Q18 Q18 Q20 Q19 *)
  0xce355273;       (* arm_BCAX Q19 Q19 Q21 Q20 *)
  0xce360414;       (* arm_BCAX Q20 Q0 Q22 Q1 *)
  0xce375835;       (* arm_BCAX Q21 Q1 Q23 Q22 *)
  0xce385ed6;       (* arm_BCAX Q22 Q22 Q24 Q23 *)
  0xce2062f7;       (* arm_BCAX Q23 Q23 Q0 Q24 *)
  0xce210318;       (* arm_BCAX Q24 Q24 Q1 Q0 *)
  0xce226fc0;       (* arm_BCAX Q0 Q30 Q2 Q27 *)
  0xce230b61;       (* arm_BCAX Q1 Q27 Q3 Q2 *)
  0xce240c42;       (* arm_BCAX Q2 Q2 Q4 Q3 *)
  0xce3e1063;       (* arm_BCAX Q3 Q3 Q30 Q4 *)
  0xce3b7884;       (* arm_BCAX Q4 Q4 Q27 Q30 *)
  0x6e3f1c00;       (* arm_EOR_VEC Q0 Q0 Q31 128 *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fff782;       (* arm_CBNZ X2 (word 2096880) *)
  0x91032002;       (* arm_ADD X2 X0 (rvalue (word 200)) *)
  0x4ec12819;       (* arm_TRN1 Q25 Q0 Q1 64 128 *)
  0x4ec3285a;       (* arm_TRN1 Q26 Q2 Q3 64 128 *)
  0xad006819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&0))) *)
  0x4ec1681b;       (* arm_TRN2 Q27 Q0 Q1 64 128 *)
  0x4ec3685c;       (* arm_TRN2 Q28 Q2 Q3 64 128 *)
  0xad00705b;       (* arm_STP Q27 Q28 X2 (Immediate_Offset (iword (&0))) *)
  0x4ec52899;       (* arm_TRN1 Q25 Q4 Q5 64 128 *)
  0x4ec728da;       (* arm_TRN1 Q26 Q6 Q7 64 128 *)
  0xad016819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&32))) *)
  0x4ec5689b;       (* arm_TRN2 Q27 Q4 Q5 64 128 *)
  0x4ec768dc;       (* arm_TRN2 Q28 Q6 Q7 64 128 *)
  0xad01705b;       (* arm_STP Q27 Q28 X2 (Immediate_Offset (iword (&32))) *)
  0x4ec92919;       (* arm_TRN1 Q25 Q8 Q9 64 128 *)
  0x4ecb295a;       (* arm_TRN1 Q26 Q10 Q11 64 128 *)
  0xad026819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&64))) *)
  0x4ec9691b;       (* arm_TRN2 Q27 Q8 Q9 64 128 *)
  0x4ecb695c;       (* arm_TRN2 Q28 Q10 Q11 64 128 *)
  0xad02705b;       (* arm_STP Q27 Q28 X2 (Immediate_Offset (iword (&64))) *)
  0x4ecd2999;       (* arm_TRN1 Q25 Q12 Q13 64 128 *)
  0x4ecf29da;       (* arm_TRN1 Q26 Q14 Q15 64 128 *)
  0xad036819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&96))) *)
  0x4ecd699b;       (* arm_TRN2 Q27 Q12 Q13 64 128 *)
  0x4ecf69dc;       (* arm_TRN2 Q28 Q14 Q15 64 128 *)
  0xad03705b;       (* arm_STP Q27 Q28 X2 (Immediate_Offset (iword (&96))) *)
  0x4ed12a19;       (* arm_TRN1 Q25 Q16 Q17 64 128 *)
  0x4ed32a5a;       (* arm_TRN1 Q26 Q18 Q19 64 128 *)
  0xad046819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&128))) *)
  0x4ed16a1b;       (* arm_TRN2 Q27 Q16 Q17 64 128 *)
  0x4ed36a5c;       (* arm_TRN2 Q28 Q18 Q19 64 128 *)
  0xad04705b;       (* arm_STP Q27 Q28 X2 (Immediate_Offset (iword (&128))) *)
  0x4ed52a99;       (* arm_TRN1 Q25 Q20 Q21 64 128 *)
  0x4ed72ada;       (* arm_TRN1 Q26 Q22 Q23 64 128 *)
  0xad056819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&160))) *)
  0x4ed56a9b;       (* arm_TRN2 Q27 Q20 Q21 64 128 *)
  0x4ed76adc;       (* arm_TRN2 Q28 Q22 Q23 64 128 *)
  0xad05705b;       (* arm_STP Q27 Q28 X2 (Immediate_Offset (iword (&160))) *)
  0xfd006018;       (* arm_STR D24 X0 (Immediate_Offset (word 192)) *)
  0x4ed86b19;       (* arm_TRN2 Q25 Q24 Q24 64 128 *)
  0xfd006059;       (* arm_STR D25 X2 (Immediate_Offset (word 192)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let KECCAK_F1600_X2_V84A_EXEC = ARM_MK_EXEC_RULE keccak_f1600_x2_v84a_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_KECCAK_F1600_X2_V84A_MC =
  REWRITE_CONV[keccak_f1600_x2_v84a_mc] `LENGTH keccak_f1600_x2_v84a_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let KECCAK_F1600_X2_V84A_PREAMBLE_LENGTH = new_definition
  `KECCAK_F1600_X2_V84A_PREAMBLE_LENGTH = 20`;;

let KECCAK_F1600_X2_V84A_POSTAMBLE_LENGTH = new_definition
  `KECCAK_F1600_X2_V84A_POSTAMBLE_LENGTH = 24`;;

let KECCAK_F1600_X2_V84A_CORE_START = new_definition
  `KECCAK_F1600_X2_V84A_CORE_START = KECCAK_F1600_X2_V84A_PREAMBLE_LENGTH`;;

let KECCAK_F1600_X2_V84A_CORE_END = new_definition
  `KECCAK_F1600_X2_V84A_CORE_END = LENGTH keccak_f1600_x2_v84a_mc - KECCAK_F1600_X2_V84A_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_KECCAK_F1600_X2_V84A_MC;
              KECCAK_F1600_X2_V84A_CORE_START; KECCAK_F1600_X2_V84A_CORE_END;
              KECCAK_F1600_X2_V84A_PREAMBLE_LENGTH; KECCAK_F1600_X2_V84A_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

let KECCAK_F1600_X2_V84A_EXEC = ARM_MK_EXEC_RULE keccak_f1600_x2_v84a_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof                                                         *)
(* ------------------------------------------------------------------------- *)

let KECCAK_F1600_X2_V84A_CORRECT = prove
 (`!a rc A A' pc.
      ALL (nonoverlapping (a,400)) [(word pc,LENGTH keccak_f1600_x2_v84a_mc); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) keccak_f1600_x2_v84a_mc /\
                read PC s = word (pc + KECCAK_F1600_X2_V84A_CORE_START) /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(a,25) s = A /\
                wordlist_from_memory(word_add a (word 200),25) s = A' /\
                wordlist_from_memory(rc,24) s = round_constants)
           (\s. read PC s = word(pc + KECCAK_F1600_X2_V84A_CORE_END) /\
                wordlist_from_memory(a,25) s = keccak 24 A /\
                wordlist_from_memory(word_add a (word 200),25) s = keccak 24 A')
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,400)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A:int64 list`; `A':int64 list`; `pc:num`] THEN
  REWRITE_TAC[fst KECCAK_F1600_X2_V84A_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Establish once and for all that A and A' have length 25 ***)

  ASM_CASES_TAC
   `LENGTH(A:int64 list) = 25 /\ LENGTH(A':int64 list) = 25`
  THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  ENSURES_WHILE_UP_TAC `24` `pc + 0xb8` `pc + 0x1c8`
   `\i s.
      wordlist_from_memory(rc,24) s = round_constants /\
      read X0 s = a /\
      read X1 s = word_add rc (word(8 * i)) /\
      read X2 s = word_sub (word 24) (word i) /\
      [read Q0 s; read Q1 s; read Q2 s; read Q3 s; read Q4 s;
       read Q5 s; read Q6 s; read Q7 s; read Q8 s; read Q9 s;
       read Q10 s; read Q11 s; read Q12 s; read Q13 s; read Q14 s;
       read Q15 s; read Q16 s; read Q17 s; read Q18 s; read Q19 s;
       read Q20 s; read Q21 s; read Q22 s; read Q23 s; read Q24 s] =
      MAP2 word_join (keccak i A') (keccak i A)` THEN
  REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 50)) s0` THEN
    REPEAT(FIRST_X_ASSUM
     (MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MEMORY_128_FROM_64_TAC "a" 0 12 THEN
    MEMORY_128_FROM_64_TAC "a" 200 12 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN STRIP_TAC THEN
    ARM_STEPS_TAC KECCAK_F1600_X2_V84A_EXEC (1--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    MAP_EVERY EXPAND_TAC ["A"; "A'"] THEN
    REWRITE_TAC[MAP2; keccak; CONS_11] THEN CONV_TAC WORD_BLAST;

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A':int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ARM_STEPS_TAC KECCAK_F1600_X2_V84A_EXEC (1--68) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC[keccak; keccak_round] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[MAP2; CONS_11] THEN
    REPEAT CONJ_TAC THEN BITBLAST_TAC;

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
    WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ARM_SIM_TAC KECCAK_F1600_X2_V84A_EXEC [1] THEN
    VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_SIMP_TAC[LT_IMP_NE];

    (*** The tail of deferred rotations and writeback ***)

    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A':int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN

    ARM_SIM_TAC KECCAK_F1600_X2_V84A_EXEC (1--41) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN

    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST]);;

let KECCAK_F1600_X2_V84A_SUBROUTINE_CORRECT = prove
(`!a rc A A' pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (a,400) (word_sub stackpointer (word 64),64) /\
        ALLPAIRS nonoverlapping
          [(a,400); (word_sub stackpointer (word 64),64)]
          [(word pc,LENGTH keccak_f1600_x2_v84a_mc); (rc,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) keccak_f1600_x2_v84a_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; rc] s /\
                  wordlist_from_memory(a,25) s = A /\
                  wordlist_from_memory (word_add a (word 200),25) s = A' /\
                  wordlist_from_memory(rc,24) s = round_constants)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A /\
                  wordlist_from_memory (word_add a (word 200),25) s =
                  keccak 24 A')
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,400);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  let TWEAK_CONV =
   ONCE_DEPTH_CONV
    (WORDLIST_FROM_MEMORY_CONV THENC
     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) KECCAK_F1600_X2_V84A_EXEC
   (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV KECCAK_F1600_X2_V84A_CORRECT))
  `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
