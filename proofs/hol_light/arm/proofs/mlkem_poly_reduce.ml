(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "mlkem/mlkem_poly_reduce.o";;
 ****)

let mlkem_poly_reduce_mc = define_assert_from_elf
  "mlkem_poly_reduce_mc" "mlkem/mlkem_poly_reduce.o"
[
  0x5281a022;       (* arm_MOV W2 (rvalue (word 3329)) *)
  0x4e020c43;       (* arm_DUP_GEN Q3 X2 16 128 *)
  0x5289d7e2;       (* arm_MOV W2 (rvalue (word 20159)) *)
  0x4e020c44;       (* arm_DUP_GEN Q4 X2 16 128 *)
  0xd2800101;       (* arm_MOV X1 (rvalue (word 8)) *)
  0x3dc00815;       (* arm_LDR Q21 X0 (Immediate_Offset (word 32)) *)
  0x3dc00c17;       (* arm_LDR Q23 X0 (Immediate_Offset (word 48)) *)
  0x4f44c2a7;       (* arm_SQDMULH_VEC Q7 Q21 (Q4 :> LANE_H 0) 16 128 *)
  0x4f44c2fe;       (* arm_SQDMULH_VEC Q30 Q23 (Q4 :> LANE_H 0) 16 128 *)
  0x4f1524e7;       (* arm_SRSHR_VEC Q7 Q7 11 16 128 *)
  0x4f1527de;       (* arm_SRSHR_VEC Q30 Q30 11 16 128 *)
  0x6f4340f5;       (* arm_MLS_VEC Q21 Q7 (Q3 :> LANE_H 0) 16 128 *)
  0x6f4343d7;       (* arm_MLS_VEC Q23 Q30 (Q3 :> LANE_H 0) 16 128 *)
  0x3dc00405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 16)) *)
  0x4f1106a7;       (* arm_SSHR_VEC Q7 Q21 15 16 128 *)
  0x4f1106fe;       (* arm_SSHR_VEC Q30 Q23 15 16 128 *)
  0x4e271c67;       (* arm_AND_VEC Q7 Q3 Q7 128 *)
  0x4e6786b5;       (* arm_ADD_VEC Q21 Q21 Q7 16 128 *)
  0x4e3e1c67;       (* arm_AND_VEC Q7 Q3 Q30 128 *)
  0x4e6786f0;       (* arm_ADD_VEC Q16 Q23 Q7 16 128 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0x3cc40406;       (* arm_LDR Q6 X0 (Postimmediate_Offset (word 64)) *)
  0x3dc0081e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 32)) *)
  0x4f44c0df;       (* arm_SQDMULH_VEC Q31 Q6 (Q4 :> LANE_H 0) 16 128 *)
  0x4f44c0bd;       (* arm_SQDMULH_VEC Q29 Q5 (Q4 :> LANE_H 0) 16 128 *)
  0x4f44c3d6;       (* arm_SQDMULH_VEC Q22 Q30 (Q4 :> LANE_H 0) 16 128 *)
  0x3c9f0010;       (* arm_STR Q16 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4f1527f4;       (* arm_SRSHR_VEC Q20 Q31 11 16 128 *)
  0x4f1527bc;       (* arm_SRSHR_VEC Q28 Q29 11 16 128 *)
  0x3c9e0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x6f434286;       (* arm_MLS_VEC Q6 Q20 (Q3 :> LANE_H 0) 16 128 *)
  0x6f434385;       (* arm_MLS_VEC Q5 Q28 (Q3 :> LANE_H 0) 16 128 *)
  0x3dc00c02;       (* arm_LDR Q2 X0 (Immediate_Offset (word 48)) *)
  0x4f1104df;       (* arm_SSHR_VEC Q31 Q6 15 16 128 *)
  0x4f1526d3;       (* arm_SRSHR_VEC Q19 Q22 11 16 128 *)
  0x4e3f1c76;       (* arm_AND_VEC Q22 Q3 Q31 128 *)
  0x4e7684c0;       (* arm_ADD_VEC Q0 Q6 Q22 16 128 *)
  0x6f43427e;       (* arm_MLS_VEC Q30 Q19 (Q3 :> LANE_H 0) 16 128 *)
  0x4f1104ba;       (* arm_SSHR_VEC Q26 Q5 15 16 128 *)
  0x4f44c059;       (* arm_SQDMULH_VEC Q25 Q2 (Q4 :> LANE_H 0) 16 128 *)
  0x4e3a1c71;       (* arm_AND_VEC Q17 Q3 Q26 128 *)
  0x4e7184a1;       (* arm_ADD_VEC Q1 Q5 Q17 16 128 *)
  0x4f1107df;       (* arm_SSHR_VEC Q31 Q30 15 16 128 *)
  0x4f152739;       (* arm_SRSHR_VEC Q25 Q25 11 16 128 *)
  0x3c9d0001;       (* arm_STR Q1 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e3f1c72;       (* arm_AND_VEC Q18 Q3 Q31 128 *)
  0x6f434322;       (* arm_MLS_VEC Q2 Q25 (Q3 :> LANE_H 0) 16 128 *)
  0x4e7287d5;       (* arm_ADD_VEC Q21 Q30 Q18 16 128 *)
  0x3dc00405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 16)) *)
  0x4f110452;       (* arm_SSHR_VEC Q18 Q2 15 16 128 *)
  0x3c9c0000;       (* arm_STR Q0 X0 (Immediate_Offset (word 18446744073709551552)) *)
  0x4e321c7b;       (* arm_AND_VEC Q27 Q3 Q18 128 *)
  0x4e7b8450;       (* arm_ADD_VEC Q16 Q2 Q27 16 128 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5fffbe1;       (* arm_CBNZ X1 (word 2097020) *)
  0x4f44c0b4;       (* arm_SQDMULH_VEC Q20 Q5 (Q4 :> LANE_H 0) 16 128 *)
  0x3cc40418;       (* arm_LDR Q24 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9e0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x4f152694;       (* arm_SRSHR_VEC Q20 Q20 11 16 128 *)
  0x4f44c319;       (* arm_SQDMULH_VEC Q25 Q24 (Q4 :> LANE_H 0) 16 128 *)
  0x3c9f0010;       (* arm_STR Q16 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f434285;       (* arm_MLS_VEC Q5 Q20 (Q3 :> LANE_H 0) 16 128 *)
  0x4f152734;       (* arm_SRSHR_VEC Q20 Q25 11 16 128 *)
  0x4f1104a2;       (* arm_SSHR_VEC Q2 Q5 15 16 128 *)
  0x6f434298;       (* arm_MLS_VEC Q24 Q20 (Q3 :> LANE_H 0) 16 128 *)
  0x4e221c74;       (* arm_AND_VEC Q20 Q3 Q2 128 *)
  0x4e7484bf;       (* arm_ADD_VEC Q31 Q5 Q20 16 128 *)
  0x4f110714;       (* arm_SSHR_VEC Q20 Q24 15 16 128 *)
  0x3c9d001f;       (* arm_STR Q31 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e341c7f;       (* arm_AND_VEC Q31 Q3 Q20 128 *)
  0x4e7f8718;       (* arm_ADD_VEC Q24 Q24 Q31 16 128 *)
  0x3c9c0018;       (* arm_STR Q24 X0 (Immediate_Offset (word 18446744073709551552)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_POLY_REDUCE_EXEC = ARM_MK_EXEC_RULE mlkem_poly_reduce_mc;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas, tactics etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let lemma_rem = prove
 (`(y == x) (mod &3329) /\
   --(&1664) <= y /\ y <= &1664
   ==> x rem &3329 = if y < &0 then y + &3329 else y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
  SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE);;

let overall_lemma = prove
 (`!x:int16.
        ival(word_add (barred x)
                      (word_and (word_ishr (barred x) 15) (word 3329))) =
        ival x rem &3329`,
  REWRITE_TAC[MATCH_MP lemma_rem (CONGBOUND_RULE `barred x`)] THEN
  BITBLAST_TAC);;

let MLKEM_POLY_REDUCE_CORRECT = prove
 (`!a x pc.
        nonoverlapping (word pc,0x124) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_reduce_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + 0x120) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Manually restructure to match the 128-bit loads. It would be nicer
   *** if the simulation machinery did this automatically.
   ***)

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN

  (*** Do a full simulation with no breakpoints, unrolling the loop ***)

  MAP_EVERY (fun n ->
   ARM_STEPS_TAC MLKEM_POLY_REDUCE_EXEC [n] THEN SIMD_SIMPLIFY_TAC)
  (1--276) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE SIMD_SIMPLIFY_CONV o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Now the result is just a replicated instance of our lemma ***)

  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s276" THEN
  REWRITE_TAC[GSYM barred; overall_lemma]);;

let MLKEM_POLY_REDUCE_SUBROUTINE_CORRECT = prove
 (`!a x pc returnaddress.
        nonoverlapping (word pc,0x124) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_reduce_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
 let TWEAK_CONV =
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_REDUCE_EXEC
   (CONV_RULE TWEAK_CONV MLKEM_POLY_REDUCE_CORRECT));;
