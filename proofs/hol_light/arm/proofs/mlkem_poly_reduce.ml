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
(*** BYTECODE START ***)
[
  0x5281a022;       (* arm_MOV W2 (rvalue (word 3329)) *)
  0x4e020c43;       (* arm_DUP_GEN Q3 X2 16 128 *)
  0x5289d7e2;       (* arm_MOV W2 (rvalue (word 20159)) *)
  0x4e020c44;       (* arm_DUP_GEN Q4 X2 16 128 *)
  0xd2800101;       (* arm_MOV X1 (rvalue (word 8)) *)
  0x3cc40415;       (* arm_LDR Q21 X0 (Postimmediate_Offset (word 64)) *)
  0x3cde0012;       (* arm_LDR Q18 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdd0000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cdf0005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc4041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 64)) *)
  0x4f44c2b1;       (* arm_SQDMULH_VEC Q17 Q21 (Q4 :> LANE_H 0) 16 128 *)
  0x4f44c25b;       (* arm_SQDMULH_VEC Q27 Q18 (Q4 :> LANE_H 0) 16 128 *)
  0x4f44c016;       (* arm_SQDMULH_VEC Q22 Q0 (Q4 :> LANE_H 0) 16 128 *)
  0x4f152631;       (* arm_SRSHR_VEC Q17 Q17 11 16 128 *)
  0x4f44c0b7;       (* arm_SQDMULH_VEC Q23 Q5 (Q4 :> LANE_H 0) 16 128 *)
  0x4f15277d;       (* arm_SRSHR_VEC Q29 Q27 11 16 128 *)
  0x6f434235;       (* arm_MLS_VEC Q21 Q17 (Q3 :> LANE_H 0) 16 128 *)
  0x4f1526d1;       (* arm_SRSHR_VEC Q17 Q22 11 16 128 *)
  0x6f4343b2;       (* arm_MLS_VEC Q18 Q29 (Q3 :> LANE_H 0) 16 128 *)
  0x4f1526f6;       (* arm_SRSHR_VEC Q22 Q23 11 16 128 *)
  0x6f434220;       (* arm_MLS_VEC Q0 Q17 (Q3 :> LANE_H 0) 16 128 *)
  0x4f1106a2;       (* arm_SSHR_VEC Q2 Q21 15 16 128 *)
  0x6f4342c5;       (* arm_MLS_VEC Q5 Q22 (Q3 :> LANE_H 0) 16 128 *)
  0x4f11065d;       (* arm_SSHR_VEC Q29 Q18 15 16 128 *)
  0x4e221c73;       (* arm_AND_VEC Q19 Q3 Q2 128 *)
  0x4f44c342;       (* arm_SQDMULH_VEC Q2 Q26 (Q4 :> LANE_H 0) 16 128 *)
  0x4f11041f;       (* arm_SSHR_VEC Q31 Q0 15 16 128 *)
  0x4e7386b1;       (* arm_ADD_VEC Q17 Q21 Q19 16 128 *)
  0x4e3d1c75;       (* arm_AND_VEC Q21 Q3 Q29 128 *)
  0x4e3f1c7f;       (* arm_AND_VEC Q31 Q3 Q31 128 *)
  0xd1000821;       (* arm_SUB X1 X1 (rvalue (word 2)) *)
  0x4e758655;       (* arm_ADD_VEC Q21 Q18 Q21 16 128 *)
  0x3cde0012;       (* arm_LDR Q18 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e7f8419;       (* arm_ADD_VEC Q25 Q0 Q31 16 128 *)
  0x3cdd0000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9a0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551520)) *)
  0x4f1104bc;       (* arm_SSHR_VEC Q28 Q5 15 16 128 *)
  0x3c980011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551488)) *)
  0x4f152457;       (* arm_SRSHR_VEC Q23 Q2 11 16 128 *)
  0x4f44c25e;       (* arm_SQDMULH_VEC Q30 Q18 (Q4 :> LANE_H 0) 16 128 *)
  0x3c990019;       (* arm_STR Q25 X0 (Immediate_Offset (word 18446744073709551504)) *)
  0x4e3c1c76;       (* arm_AND_VEC Q22 Q3 Q28 128 *)
  0x4f44c007;       (* arm_SQDMULH_VEC Q7 Q0 (Q4 :> LANE_H 0) 16 128 *)
  0x4e7684b0;       (* arm_ADD_VEC Q16 Q5 Q22 16 128 *)
  0x3cdf0005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f4342fa;       (* arm_MLS_VEC Q26 Q23 (Q3 :> LANE_H 0) 16 128 *)
  0x3c9b0010;       (* arm_STR Q16 X0 (Immediate_Offset (word 18446744073709551536)) *)
  0x4f1527c6;       (* arm_SRSHR_VEC Q6 Q30 11 16 128 *)
  0x4f1524e1;       (* arm_SRSHR_VEC Q1 Q7 11 16 128 *)
  0x4f44c0b3;       (* arm_SQDMULH_VEC Q19 Q5 (Q4 :> LANE_H 0) 16 128 *)
  0x6f4340d2;       (* arm_MLS_VEC Q18 Q6 (Q3 :> LANE_H 0) 16 128 *)
  0x4f110758;       (* arm_SSHR_VEC Q24 Q26 15 16 128 *)
  0x6f434020;       (* arm_MLS_VEC Q0 Q1 (Q3 :> LANE_H 0) 16 128 *)
  0x4e381c7b;       (* arm_AND_VEC Q27 Q3 Q24 128 *)
  0x4f15267d;       (* arm_SRSHR_VEC Q29 Q19 11 16 128 *)
  0x4e7b8751;       (* arm_ADD_VEC Q17 Q26 Q27 16 128 *)
  0x3cc4041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 64)) *)
  0x4f110641;       (* arm_SSHR_VEC Q1 Q18 15 16 128 *)
  0x6f4343a5;       (* arm_MLS_VEC Q5 Q29 (Q3 :> LANE_H 0) 16 128 *)
  0x4f110414;       (* arm_SSHR_VEC Q20 Q0 15 16 128 *)
  0x4e211c75;       (* arm_AND_VEC Q21 Q3 Q1 128 *)
  0x4e341c7f;       (* arm_AND_VEC Q31 Q3 Q20 128 *)
  0x4f44c342;       (* arm_SQDMULH_VEC Q2 Q26 (Q4 :> LANE_H 0) 16 128 *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0xb5fffbe1;       (* arm_CBNZ X1 (word 2097020) *)
  0x4e7f841c;       (* arm_ADD_VEC Q28 Q0 Q31 16 128 *)
  0x3cdf001d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e758655;       (* arm_ADD_VEC Q21 Q18 Q21 16 128 *)
  0x4f152452;       (* arm_SRSHR_VEC Q18 Q2 11 16 128 *)
  0x4f1104a2;       (* arm_SSHR_VEC Q2 Q5 15 16 128 *)
  0x3cde0010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c980011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551488)) *)
  0x3cdd0000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e221c62;       (* arm_AND_VEC Q2 Q3 Q2 128 *)
  0x4f44c3b8;       (* arm_SQDMULH_VEC Q24 Q29 (Q4 :> LANE_H 0) 16 128 *)
  0x3c99001c;       (* arm_STR Q28 X0 (Immediate_Offset (word 18446744073709551504)) *)
  0x3c9a0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551520)) *)
  0x4e6284bf;       (* arm_ADD_VEC Q31 Q5 Q2 16 128 *)
  0x4f44c206;       (* arm_SQDMULH_VEC Q6 Q16 (Q4 :> LANE_H 0) 16 128 *)
  0x3c9b001f;       (* arm_STR Q31 X0 (Immediate_Offset (word 18446744073709551536)) *)
  0x4f44c011;       (* arm_SQDMULH_VEC Q17 Q0 (Q4 :> LANE_H 0) 16 128 *)
  0x4f152716;       (* arm_SRSHR_VEC Q22 Q24 11 16 128 *)
  0x6f43425a;       (* arm_MLS_VEC Q26 Q18 (Q3 :> LANE_H 0) 16 128 *)
  0x4f1524df;       (* arm_SRSHR_VEC Q31 Q6 11 16 128 *)
  0x6f4342dd;       (* arm_MLS_VEC Q29 Q22 (Q3 :> LANE_H 0) 16 128 *)
  0x4f152633;       (* arm_SRSHR_VEC Q19 Q17 11 16 128 *)
  0x6f4343f0;       (* arm_MLS_VEC Q16 Q31 (Q3 :> LANE_H 0) 16 128 *)
  0x4f110747;       (* arm_SSHR_VEC Q7 Q26 15 16 128 *)
  0x6f434260;       (* arm_MLS_VEC Q0 Q19 (Q3 :> LANE_H 0) 16 128 *)
  0x4e271c65;       (* arm_AND_VEC Q5 Q3 Q7 128 *)
  0x4f1107b6;       (* arm_SSHR_VEC Q22 Q29 15 16 128 *)
  0x4e65875b;       (* arm_ADD_VEC Q27 Q26 Q5 16 128 *)
  0x4e361c7a;       (* arm_AND_VEC Q26 Q3 Q22 128 *)
  0x4f110614;       (* arm_SSHR_VEC Q20 Q16 15 16 128 *)
  0x3c9c001b;       (* arm_STR Q27 X0 (Immediate_Offset (word 18446744073709551552)) *)
  0x4e341c62;       (* arm_AND_VEC Q2 Q3 Q20 128 *)
  0x4f110417;       (* arm_SSHR_VEC Q23 Q0 15 16 128 *)
  0x4e7a87b2;       (* arm_ADD_VEC Q18 Q29 Q26 16 128 *)
  0x4e62861f;       (* arm_ADD_VEC Q31 Q16 Q2 16 128 *)
  0x4e371c7d;       (* arm_AND_VEC Q29 Q3 Q23 128 *)
  0x3c9f0012;       (* arm_STR Q18 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7d8419;       (* arm_ADD_VEC Q25 Q0 Q29 16 128 *)
  0x3c9e001f;       (* arm_STR Q31 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9d0019;       (* arm_STR Q25 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_REDUCE_EXEC = ARM_MK_EXEC_RULE mlkem_poly_reduce_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_REDUCE_MC =
  REWRITE_CONV[mlkem_poly_reduce_mc] `LENGTH mlkem_poly_reduce_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_REDUCE_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_REDUCE_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_REDUCE_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_REDUCE_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_REDUCE_CORE_START = new_definition
  `MLKEM_POLY_REDUCE_CORE_START = MLKEM_POLY_REDUCE_PREAMBLE_LENGTH`;;

let MLKEM_POLY_REDUCE_CORE_END = new_definition
  `MLKEM_POLY_REDUCE_CORE_END = LENGTH mlkem_poly_reduce_mc - MLKEM_POLY_REDUCE_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_REDUCE_MC;
              MLKEM_POLY_REDUCE_CORE_START; MLKEM_POLY_REDUCE_CORE_END;
              MLKEM_POLY_REDUCE_PREAMBLE_LENGTH; MLKEM_POLY_REDUCE_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0] ;;

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
        nonoverlapping (word pc,LENGTH mlkem_poly_reduce_mc) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_reduce_mc /\
                  read PC s = word (pc + MLKEM_POLY_REDUCE_CORE_START) /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + MLKEM_POLY_REDUCE_CORE_END) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
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

  MAP_UNTIL_TARGET_PC (fun n ->
   ARM_STEPS_TAC MLKEM_POLY_REDUCE_EXEC [n] THEN (SIMD_SIMPLIFY_TAC [barred])) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE (SIMD_SIMPLIFY_CONV []) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Now the result is just a replicated instance of our lemma ***)

  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s276" THEN
  REWRITE_TAC[GSYM barred; overall_lemma]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_REDUCE_SUBROUTINE_CORRECT = prove
 (`!a x pc returnaddress.
        nonoverlapping (word pc,LENGTH mlkem_poly_reduce_mc) (a,512)
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
 CONV_TAC LENGTH_SIMPLIFY_CONV THEN
 let TWEAK_CONV =
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0]
     in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_REDUCE_EXEC
   (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_REDUCE_CORRECT)));;
