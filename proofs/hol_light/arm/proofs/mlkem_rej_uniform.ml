(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling for ML-KEM, filtering packed numbers < 3329.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;
needs "proofs/mlkem_rej_uniform_table.ml";;

(**** print_literal_from_elf "mlkem/mlkem_rej_uniform.o";;
 ****)

let mlkem_rej_uniform_mc = define_assert_from_elf
  "mlkem_rej_uniform_mc" "mlkem/mlkem_rej_uniform.o"
[
  0xd10903ff;       (* arm_SUB SP SP (rvalue (word 576)) *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0xf2a00047;       (* arm_MOVK X7 (word 2) 16 *)
  0xf2c00087;       (* arm_MOVK X7 (word 4) 32 *)
  0xf2e00107;       (* arm_MOVK X7 (word 8) 48 *)
  0x4e081cff;       (* arm_INS_GEN Q31 X7 0 64 *)
  0xd2800207;       (* arm_MOV X7 (rvalue (word 16)) *)
  0xf2a00407;       (* arm_MOVK X7 (word 32) 16 *)
  0xf2c00807;       (* arm_MOVK X7 (word 64) 32 *)
  0xf2e01007;       (* arm_MOVK X7 (word 128) 48 *)
  0x4e181cff;       (* arm_INS_GEN Q31 X7 64 64 *)
  0x5281a02b;       (* arm_MOV W11 (rvalue (word 3329)) *)
  0x4e020d7e;       (* arm_DUP_GEN Q30 X11 16 128 *)
  0x910003e8;       (* arm_ADD X8 SP (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0x6e301e10;       (* arm_EOR_VEC Q16 Q16 Q16 128 *)
  0x3c8404f0;       (* arm_STR Q16 X7 (Postimmediate_Offset (word 64)) *)
  0x3c9d00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100816b;       (* arm_ADD X11 X11 (rvalue (word 32)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54ffff4b;       (* arm_BLT (word 2097128) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd2800009;       (* arm_MOV X9 (rvalue (word 0)) *)
  0xd2802004;       (* arm_MOV X4 (rvalue (word 256)) *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 48)) *)
  0x54000863;       (* arm_BCC (word 268) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x54000ca2;       (* arm_BCS (word 404) *)
  0xd100c042;       (* arm_SUB X2 X2 (rvalue (word 48)) *)
  0x4cdf4020;       (* arm_LD3 [Q0; Q1; Q2] X1 (Postimmediate_Offset (word 48)) 128 8 *)
  0x4e013804;       (* arm_ZIP1 Q4 Q0 Q1 8 128 *)
  0x4e017805;       (* arm_ZIP2 Q5 Q0 Q1 8 128 *)
  0x4e023826;       (* arm_ZIP1 Q6 Q1 Q2 8 128 *)
  0x4e027827;       (* arm_ZIP2 Q7 Q1 Q2 8 128 *)
  0x6f07b604;       (* arm_BIC_VEC Q4 Q4 (rvalue (word 319019586840962221640188233472310046720)) 128 *)
  0x6f07b605;       (* arm_BIC_VEC Q5 Q5 (rvalue (word 319019586840962221640188233472310046720)) 128 *)
  0x6f1c04c6;       (* arm_USHR_VEC Q6 Q6 4 16 128 *)
  0x6f1c04e7;       (* arm_USHR_VEC Q7 Q7 4 16 128 *)
  0x4e463890;       (* arm_ZIP1 Q16 Q4 Q6 16 128 *)
  0x4e467891;       (* arm_ZIP2 Q17 Q4 Q6 16 128 *)
  0x4e4738b2;       (* arm_ZIP1 Q18 Q5 Q7 16 128 *)
  0x4e4778b3;       (* arm_ZIP2 Q19 Q5 Q7 16 128 *)
  0x6e7037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 16 128 *)
  0x6e7137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 16 128 *)
  0x6e7237c6;       (* arm_CMHI_VEC Q6 Q30 Q18 16 128 *)
  0x6e7337c7;       (* arm_CMHI_VEC Q7 Q30 Q19 16 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x4e3f1cc6;       (* arm_AND_VEC Q6 Q6 Q31 128 *)
  0x4e3f1ce7;       (* arm_AND_VEC Q7 Q7 Q31 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x6e7038d6;       (* arm_UADDLV Q22 Q6 8 16 *)
  0x6e7038f7;       (* arm_UADDLV Q23 Q7 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x1e2602ce;       (* arm_FMOV_FtoI W14 Q22 0 32 *)
  0x1e2602ef;       (* arm_FMOV_FtoI W15 Q23 0 32 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x3cee787a;       (* arm_LDR Q26 X3 (Shiftreg_Offset X14 4) *)
  0x3cef787b;       (* arm_LDR Q27 X3 (Shiftreg_Offset X15 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x4e2058c6;       (* arm_CNT Q6 Q6 128 *)
  0x4e2058e7;       (* arm_CNT Q7 Q7 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x6e7038d6;       (* arm_UADDLV Q22 Q6 8 16 *)
  0x6e7038f7;       (* arm_UADDLV Q23 Q7 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x1e2602ce;       (* arm_FMOV_FtoI W14 Q22 0 32 *)
  0x1e2602ef;       (* arm_FMOV_FtoI W15 Q23 0 32 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x4e1a0252;       (* arm_TBL Q18 [Q18] Q26 128 *)
  0x4e1b0273;       (* arm_TBL Q19 [Q19] Q27 128 *)
  0x3d8000f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 0)) *)
  0x8b0c04e7;       (* arm_ADD X7 X7 (Shiftedreg X12 LSL 1) *)
  0x3d8000f1;       (* arm_STR Q17 X7 (Immediate_Offset (word 0)) *)
  0x8b0d04e7;       (* arm_ADD X7 X7 (Shiftedreg X13 LSL 1) *)
  0x3d8000f2;       (* arm_STR Q18 X7 (Immediate_Offset (word 0)) *)
  0x8b0e04e7;       (* arm_ADD X7 X7 (Shiftedreg X14 LSL 1) *)
  0x3d8000f3;       (* arm_STR Q19 X7 (Immediate_Offset (word 0)) *)
  0x8b0f04e7;       (* arm_ADD X7 X7 (Shiftedreg X15 LSL 1) *)
  0x8b0d018c;       (* arm_ADD X12 X12 X13 *)
  0x8b0f01ce;       (* arm_ADD X14 X14 X15 *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0x8b0e0129;       (* arm_ADD X9 X9 X14 *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 48)) *)
  0x54fff7e2;       (* arm_BCS (word 2096892) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x54000462;       (* arm_BCS (word 140) *)
  0xf100605f;       (* arm_CMP X2 (rvalue (word 24)) *)
  0x54000423;       (* arm_BCC (word 132) *)
  0xd1006042;       (* arm_SUB X2 X2 (rvalue (word 24)) *)
  0x0cdf4020;       (* arm_LD3 [Q0; Q1; Q2] X1 (Postimmediate_Offset (word 24)) 64 8 *)
  0x4e013804;       (* arm_ZIP1 Q4 Q0 Q1 8 128 *)
  0x4e023825;       (* arm_ZIP1 Q5 Q1 Q2 8 128 *)
  0x6f07b604;       (* arm_BIC_VEC Q4 Q4 (rvalue (word 319019586840962221640188233472310046720)) 128 *)
  0x6f1c04a5;       (* arm_USHR_VEC Q5 Q5 4 16 128 *)
  0x4e453890;       (* arm_ZIP1 Q16 Q4 Q5 16 128 *)
  0x4e457891;       (* arm_ZIP2 Q17 Q4 Q5 16 128 *)
  0x6e7037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 16 128 *)
  0x6e7137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 16 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x3d8000f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 0)) *)
  0x8b0c04e7;       (* arm_ADD X7 X7 (Shiftedreg X12 LSL 1) *)
  0x3d8000f1;       (* arm_STR Q17 X7 (Immediate_Offset (word 0)) *)
  0x8b0d04e7;       (* arm_ADD X7 X7 (Shiftedreg X13 LSL 1) *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0x8b0d0129;       (* arm_ADD X9 X9 X13 *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x9a843129;       (* arm_CSEL X9 X9 X4 Condition_CC *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0x3cc404f0;       (* arm_LDR Q16 X7 (Postimmediate_Offset (word 64)) *)
  0x3cdd00f1;       (* arm_LDR Q17 X7 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cde00f2;       (* arm_LDR Q18 X7 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdf00f3;       (* arm_LDR Q19 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9d0011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e0012;       (* arm_STR Q18 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f0013;       (* arm_STR Q19 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100816b;       (* arm_ADD X11 X11 (rvalue (word 32)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54fffecb;       (* arm_BLT (word 2097112) *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x14000001;       (* arm_B (word 4) *)
  0x910903ff;       (* arm_ADD SP SP (rvalue (word 576)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_REJ_UNIFORM_EXEC = ARM_MK_EXEC_RULE mlkem_rej_uniform_mc;;

(* ------------------------------------------------------------------------- *)
(* This is a general concept that subsumes a lot of specific cases like      *)
(* num_of_bytelist and bignum_of_wordlist - should standardize a bit.        *)
(* ------------------------------------------------------------------------- *)

let num_of_wordlist = define
 `num_of_wordlist [] = 0 /\
  num_of_wordlist (CONS (h:N word) t) =
     val h + 2 EXP dimindex(:N) * num_of_wordlist t`;;

let NUM_OF_WORDLIST_SING = prove
 (`!h:N word. num_of_wordlist [h] = val h`,
  REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_APPEND = prove
 (`!lis1 lis2:(N word)list.
        num_of_wordlist(APPEND lis1 lis2) =
        num_of_wordlist lis1 +
        2 EXP (dimindex(:N) * LENGTH lis1) * num_of_wordlist lis2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_wordlist] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD; ARITH] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o lhand o snd) THEN
  MATCH_MP_TAC(ARITH_RULE
   `n * (x + 1) <= y ==> h < n ==> h + n * x < y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list n.
        LENGTH l <= n ==> num_of_wordlist l < 2 EXP (dimindex(:N) * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(l:(N word)list))` THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_GEN = prove
 (`!l:((N word)list) n.
        dimindex(:N) * LENGTH l <= n ==> num_of_wordlist l < 2 EXP n`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NUM_OF_WORDLIST_BOUND_LENGTH o
    lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_SUB_LIST_0 = prove
 (`!(l:(N word)list) n.
        num_of_wordlist(SUB_LIST(0,n) l) =
        num_of_wordlist l MOD 2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[EXP_ADD] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
    REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`; MOD_LT_EQ] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(NUMBER_RULE
     `(t == t') (mod d)
      ==> (h + e * t == h + e * t') (mod (e * d))`) THEN
    REWRITE_TAC[CONG_RMOD; CONG_REFL]]);;

let NUM_OF_WORDLIST_SUB_LIST = prove
 (`!(l:(N word)list) m n.
        num_of_wordlist (SUB_LIST(m,n) l) =
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; GSYM(CONJUNCT2 num_of_wordlist);
              EXP; DIV_1; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `n:num` THEN
  SIMP_TAC[EXP_ADD; GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

(*** More on SUB_LIST, which should be earlier ***)

let SUB_LIST_REFL = prove
 (`!(l:A list) n. LENGTH l <= n ==> SUB_LIST(0,n) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; LE_SUC; LENGTH] THEN
  ARITH_TAC);;

let SUB_LIST_1 = prove
 (`!(l:A list) n. SUB_LIST(n,1) l = if n < LENGTH l then [EL n l] else []`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; SUB_LIST_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:A list`] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LT_0; num_CONV `1`; EL; TL] THEN
  ASM_REWRITE_TAC[GSYM(num_CONV `1`); LT_SUC; HD]);;

let SUB_LIST_APPEND_LEFT = prove
 (`!(l:A list) m n.
        n <= LENGTH l ==> SUB_LIST(0,n) (APPEND l m) = SUB_LIST(0,n) l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; CONJUNCT1 LE; SUB_LIST_CLAUSES] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; APPEND; LE_SUC]);;

let NUM_OF_WORDLIST_EL = prove
 (`!(l:(N word)list) m.
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N)) =
        if m < LENGTH l then val(EL m l) else 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`l:(N word)list`; `m:num`; `1`]
   NUM_OF_WORDLIST_SUB_LIST) THEN
  REWRITE_TAC[SUB_LIST_1; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SING; num_of_wordlist]);;

let pair_wordlist = define
 `(!hi (lo:N word) rest.
     pair_wordlist (CONS lo (CONS hi rest)) =
     CONS (word_join hi lo:((N)tybit0)word) (pair_wordlist rest)) /\
  (!w. pair_wordlist [w] = [word_join (word 0:N word) w]) /\
  pair_wordlist [] = []`;;

let NUM_OF_PAIR_WORDLIST = prove
 (`!l:(N word)list. num_of_wordlist (pair_wordlist l) = num_of_wordlist l`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  MAP_EVERY X_GEN_TAC [`lo:N word`; `med:(N word)list`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`med:(N word)list`,`med:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN_SIMPLE; DIMINDEX_TYBIT0;
           VAL_WORD_0; GSYM MULT_2; LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  REWRITE_TAC[MULT_2; EXP_ADD] THEN ARITH_TAC);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND = prove
 (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word) t.
    dimindex(:N) <= len
    ==> (read (m :> bytes(a,len)) s = num_of_wordlist (CONS h t) <=>
         read (m :> wbytes a) s = h /\
         read (m :> bytes(word_add a (word(dimindex(:N))),len-dimindex(:N))) s =
         num_of_wordlist t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `d:num <= l ==> l = d + (l - d)`)) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; ADD_SUB2] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`]);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV =
  let pth = prove
   (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word).
        dimindex(:N) = len
        ==> (read (m :> bytes(a,len)) s = num_of_wordlist [h] <=>
             read (m :> wbytes a) s = h)`,
    SIMP_TAC[BYTES_EQ_NUM_OF_WORDLIST_EXPAND; LE_REFL] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; SUB_REFL; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[num_of_wordlist]) in
  let frule = PART_MATCH (lhand o rand) pth
  and brule = PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_EXPAND in
  let baseconv tm =
    let ith = frule tm in
    let sth = (LAND_CONV DIMINDEX_CONV THENC NUM_EQ_CONV)
              (lhand(concl ith)) in
    MP ith (EQT_ELIM sth) in
  let rec conv tm =
    try baseconv tm with Failure _ ->
    let ith = brule tm in
    let dth = DIMINDEX_CONV(lhand(lhand(concl ith))) in
    let ith' = SUBS[dth] ith in
    let ath = MP ith' (EQT_ELIM(NUM_LE_CONV(lhand(concl ith')))) in
    let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV
               (RAND_CONV
                 (BINOP2_CONV (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                              NUM_SUB_CONV))))))) ath in
    CONV_RULE(RAND_CONV(RAND_CONV conv)) bth in
  conv;;

let BYTES_EQ_NUM_OF_WORDLIST_APPEND = prove
 (`!m (a:int64) (s:S) lis1 (lis2:(N word)list) len1 len2.
        dimindex(:N) * LENGTH lis1 = 8 * len1
        ==>  (read (m :> bytes(a,len1+len2)) s =
              num_of_wordlist(APPEND lis1 lis2) <=>
              read (m :> bytes(a,len1)) s = num_of_wordlist lis1 /\
              read (m :> bytes(word_add a (word len1),len2)) s =
              num_of_wordlist lis2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Some general stuff for fiddling with the chunksize for memory             *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let MEMORY_128_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 16*i) in
      READ_MEMORY_MERGE_CONV 1 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* New lemmas and definitions.                                               *)
(* ------------------------------------------------------------------------- *)

(*** This one clearly belongs in the core! ***)

let LENGTH_FILTER = prove
 (`!P l:A list. LENGTH(FILTER P l) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

(*** More local ones ***)

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x. val x < 3329) (MAP (word_zx:12 word->int16) l)`;;

let REJ_SAMPLE_EMPTY = prove
 (`REJ_SAMPLE [] = []`,
  REWRITE_TAC[REJ_SAMPLE; FILTER; MAP]);;

let REJ_SAMPLE_APPEND = prove
 (`!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`,
  REWRITE_TAC[REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;
let DIMINDEX_192 = DIMINDEX_CONV `dimindex(:192)`;;
let DIMINDEX_384 = DIMINDEX_CONV `dimindex(:384)`;;

(* ------------------------------------------------------------------------- *)
(* Now the actual proof.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_REJ_UNIFORM_CORRECT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer.
        24 divides val buflen /\
        8 * val buflen = 12 * LENGTH inlist /\
        ALL (nonoverlapping (stackpointer,576))
            [(word pc,0x258); (buf,val buflen); (table,4096)] /\
        ALL (nonoverlapping (res,512))
            [(word pc,0x258); (stackpointer,576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                  read PC s = word(pc + 0x4) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,4096)) s =
                  num_of_wordlist mlkem_rej_uniform_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = word(pc + 0x250) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,2 * outlen)) s =
                  num_of_wordlist outlist)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,512);
                         memory :> bytes(stackpointer,576)])`,
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; C_RETURN; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** First split off and handle the writeback tail once and for all ***)

  ENSURES_SEQUENCE_TAC `pc + 0x20c`
   `\s. read X0 s = res /\
        read X4 s = word 256 /\
        read X8 s = stackpointer /\
        ?n. let outlist = REJ_SAMPLE (SUB_LIST (0,16 * n) inlist) in
            let outlen = LENGTH outlist in
            outlen < 288 /\
            read X9 s = word outlen /\
            (buflen < 24 * (n + 1) \/ 256 <= outlen) /\
            read (memory :> bytes (stackpointer,2 * outlen)) s =
            num_of_wordlist outlist` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    (*** Just be lazy and unroll the writeback loop for now ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `outlist = REJ_SAMPLE (SUB_LIST (0,16 * n) inlist)` THEN
    ABBREV_TAC `outlen = LENGTH(outlist:int16 list)` THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    VAL_INT64_TAC `outlen:num` THEN
    BIGNUM_LDIGITIZE_TAC "b_"
      `read (memory :> bytes(stackpointer,8 * 64)) s0` THEN
    MEMORY_128_FROM_64_TAC "stackpointer" 0 32 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--94) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `read (memory :> bytes (res,2 * MIN 256 outlen)) s94 =
      num_of_wordlist (SUB_LIST (0,256) outlist:int16 list)`
    ASSUME_TAC THENL
     [REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; DIMINDEX_16] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[ARITH_RULE `2 * MIN 256 l = MIN (2 * l) 512`] THEN
      REWRITE_TAC[ARITH_RULE `16 * 256 = 8 * 512`] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `MIN a b = MIN b a`] THEN
      REWRITE_TAC[GSYM READ_BYTES_MOD] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC[ARITH_RULE `512 = 8 * 64`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [SUBGOAL_THEN `SUB_LIST (0,16 * n) (inlist:(12 word)list) = inlist`
      SUBST_ALL_TAC THENL
       [MATCH_MP_TAC SUB_LIST_REFL THEN FIRST_X_ASSUM(MATCH_MP_TAC o
        MATCH_MP
         (ARITH_RULE `8 * b = 12 * l ==> b <= 24 * n ==> l <= 16 * n`)) THEN
        UNDISCH_TAC `buflen < 24 * (n + 1)` THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
        SIMP_TAC[LEFT_IMP_EXISTS_THM; LE_MULT_LCANCEL; LT_MULT_LCANCEL] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0]] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN
      REWRITE_TAC[ARITH_RULE `(if l < p then l else p) = MIN p l`];
      ASM_REWRITE_TAC[GSYM NOT_LE; LENGTH_SUB_LIST; SUB_0] THEN
      MATCH_MP_TAC(MESON[]
       `y = x /\ (y = x ==> P) ==> word x = word y /\ P`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
        TRANS_TAC LE_TRANS `outlen:num` THEN ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME `LENGTH(outlist:int16 list) = outlen`)) THEN
        EXPAND_TAC "outlist" THEN
        MP_TAC(ISPECL [`inlist:(12 word)list`; `16 * n`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th ->
          GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
        REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN
       `SUB_LIST (0,256) (REJ_SAMPLE inlist) = SUB_LIST (0,256) outlist`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`inlist:(12 word)list`; `16 * n`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
        ASM_SIMP_TAC[REJ_SAMPLE_APPEND; SUB_LIST_APPEND_LEFT];
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `256 <= l ==> 2 * 256 = 2 * MIN 256 l`)) THEN
      FIRST_ASSUM ACCEPT_TAC]] THEN

  (*** Characterize the number of times round the main loop. ***)

  SUBGOAL_THEN
   `?i. buflen < 48 * (i + 1) \/
        256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN

  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN STRIP_TAC THEN

  (*** Slightly elaborated sequencing to handle N = 0 case as well ***)

  MATCH_MP_TAC(MESON[]
   `!P'. (ensures arm P' Q R ==> ensures arm P Q R) /\ ensures arm P' Q R
        ==> ensures arm P Q R`) THEN
  EXISTS_TAC
   `\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
        read PC s = word (pc + 0x17c) /\
        read (memory :> bytes (table,4096)) s =
        num_of_wordlist mlkem_rej_uniform_table /\
        read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
        read Q30 s = word 17285419996640026625003037585112632577 /\
        read Q31 s = word 664619068533544770747334646890102785 /\
        let outlist = REJ_SAMPLE (SUB_LIST (0,32 * N) inlist) in
        let outlen = LENGTH outlist in
        read X0 s = res /\
        read X1 s = word_add buf (word (48 * N)) /\
        read X2 s = word_sub (word buflen) (word (48 * N)) /\
        read X3 s = table /\
        read X4 s = word 256 /\
        read X7 s = word_add stackpointer (word (2 * outlen)) /\
        read X8 s = stackpointer /\
        read X9 s = word outlen /\
        read (memory :> bytes (stackpointer,2 * outlen)) s =
        num_of_wordlist outlist` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
       (REWRITE_RULE[CONJ_ASSOC] ENSURES_TRANS_SIMPLE)) THEN
      CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
       [ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN DISCH_TAC;
        ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES] THEN
        REWRITE_TAC[REJ_SAMPLE_EMPTY; LENGTH] THEN
        CONV_TAC NUM_REDUCE_CONV] THEN
      GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--77) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `~(N = 0) ==> 0 < N`)) THEN
      DISCH_TAC] THEN

    (*** Set up the loop invariant, not at the nominal loop label ***)

    ENSURES_WHILE_UP_TAC `N:num` `pc + 0x7c` `pc + 0x174`
     `\i s. read (memory :> bytes (table,4096)) s =
            num_of_wordlist mlkem_rej_uniform_table /\
            read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
            read Q30 s = word 0x0d010d010d010d010d010d010d010d01 /\
            read Q31 s = word 0x00800040002000100008000400020001 /\
            let outlist = REJ_SAMPLE(SUB_LIST(0,32 * i) inlist) in
            let outlen = LENGTH outlist in
            read X0 s = res /\
            read X1 s = word_add buf (word(48 * i)) /\
            read X2 s = word_sub (word buflen) (word(48 * i)) /\
            read X3 s = table /\
            read X4 s = word 256 /\
            read X7 s = word_add stackpointer (word(2 * outlen)) /\
            read X8 s = stackpointer /\
            read X9 s = word outlen /\
            read (memory :> bytes (stackpointer,2*outlen)) s =
            num_of_wordlist outlist` THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;

      FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--79) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

      (*** Main invariant preservation proof for loop48 ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ABBREV_TAC `cur:int64 = word_add buf (word (48 * i))` THEN
      ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,32 * i) inlist)` THEN
      ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
      CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
      ASM_REWRITE_TAC[] THEN
      ENSURES_INIT_TAC "s0" THEN
      MAP_EVERY ABBREV_TAC
       [`q0 = read (memory :> bytes128 cur) s0`;
        `q1 = read (memory :> bytes128 (word_add cur (word 16))) s0`;
        `q2 = read (memory :> bytes128 (word_add cur (word 32))) s0`] THEN

      (*** Abbreviate the next 32 digits as 16-bit words ***)

      ABBREV_TAC
       `(x:num->int16) j =
        word_zx(word_subword (read (memory :> wbytes cur) s0:384 word)
                                   (12 * j,12):12 word)` THEN

      (*** The loading with LD3 and full de-interleaving / zero-extension ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--14) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

      SUBGOAL_THEN
       `read Q16 s14 =
            word_join (word_join (word_join (x 7) (x 6):int32)
                                 (word_join (x 5) (x 4):int32):int64)
                      (word_join (word_join (x 3) (x 2):int32)
                                 (word_join (x 1) (x 0:int16):int32):int64) /\
        read Q17 s14 =
            word_join (word_join (word_join (x 15) (x 14):int32)
                                 (word_join (x 13) (x 12):int32):int64)
                      (word_join (word_join (x 11) (x 10):int32)
                                 (word_join (x 9) (x 8:int16):int32):int64) /\
        read Q18 s14 =
            word_join (word_join (word_join (x 23) (x 22):int32)
                                 (word_join (x 21) (x 20):int32):int64)
                      (word_join (word_join (x 19) (x 18):int32)
                                 (word_join (x 17) (x 16:int16):int32):int64) /\
        read Q19 s14 =
            word_join (word_join (word_join (x 31) (x 30):int32)
                                 (word_join (x 29) (x 28):int32):int64)
                      (word_join (word_join (x 27) (x 26):int32)
                                 (word_join (x 25) (x 24:int16):int32):int64)`
      MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        ASM_REWRITE_TAC[READ_MEMORY_TRIPLES_SPLIT] THEN REPEAT CONJ_TAC THEN
        GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
        REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
        CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
        REWRITE_TAC[word_subdeinterleave; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC[] THEN NO_TAC;
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q16 s = x`; `read Q17 s = x`;
          `read Q18 s = x`; `read Q19 s = x`] THEN
        STRIP_TAC] THEN

      (**** Later in the proof, we actually want this equivalent ***)

      SUBGOAL_THEN
       `!j. j < 32
            ==> (word_zx:12 word->int16)
                (EL j (SUB_LIST(32 * i,32) inlist)) = x j`
      ASSUME_TAC THENL
       [UNDISCH_THEN
         `read (memory :> bytes (buf,buflen)) s14 =
          num_of_wordlist(inlist:(12 word)list)`
         (MP_TAC o AP_TERM
           `\x. x DIV 2 EXP (8 * 48 * i) MOD 2 EXP (8 * 48)`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
        REWRITE_TAC[READ_BYTES_MOD] THEN
        REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
        REWRITE_TAC[ARITH_RULE `8 * 48 = 12 * 32 * 1`] THEN
        REWRITE_TAC[ARITH_RULE `8 * 48 * x = 12 * 32 * x`] THEN
        REWRITE_TAC[GSYM DIMINDEX_12; GSYM NUM_OF_WORDLIST_SUB_LIST] THEN
        SUBGOAL_THEN
         `MIN (buflen - 48 * i) 48 = dimindex(:384) DIV 8`
        SUBST1_TAC THENL
         [REWRITE_TAC[DIMINDEX_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
          MATCH_MP_TAC(ARITH_RULE
           `~(b < 48 * (i + 1)) ==> MIN (b - 48 * i) 48 = 48`) THEN
          ASM_SIMP_TAC[];
          REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM VAL_READ_WBYTES] THEN
          ASM_REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE]] THEN
        DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `j:num`) THEN
        ASM_REWRITE_TAC[word_zx; VAL_WORD_SUBWORD] THEN
        REWRITE_TAC[MULT_CLAUSES; DIMINDEX_12; ARITH_RULE `MIN n n = n`] THEN
        REWRITE_TAC[GSYM DIMINDEX_12; NUM_OF_WORDLIST_EL] THEN
        REWRITE_TAC[LENGTH_SUB_LIST] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN

      (*** The comparisons and table index computation ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (15--30) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

      RULE_ASSUM_TAC(REWRITE_RULE [word_ugt; relational2; GT; WORD_AND_MASK;
       WORD_BLAST `word_and x ((word_subword:int16->num#num->int128) y (0,16)) =
                   word_zx (word_and (word_zx x) y)`]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

      (*** Abbreviate the table entries and perform the table loads ***)

      MAP_EVERY REABBREV_TAC
       [`idx0 = read X12 s30`;
        `idx1 = read X13 s30`;
        `idx2 = read X14 s30`;
        `idx3 = read X15 s30`] THEN

      MAP_EVERY ABBREV_TAC
       [`tab0 =
         read(memory :> bytes128(word_add table (word(16 * val(idx0:int64))))) s30`;
        `tab1 =
         read(memory :> bytes128(word_add table (word(16 * val(idx1:int64))))) s30`;
        `tab2 =
         read(memory :> bytes128(word_add table (word(16 * val(idx2:int64))))) s30`;
        `tab3 =
         read(memory :> bytes128(word_add table
             (word(16 * val(idx3:int64))))) s30`] THEN

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (31--46) THEN

      (*** Repeating all the simplifications above actually. Just here? ***)

      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

      RULE_ASSUM_TAC(REWRITE_RULE [word_ugt; relational2; GT; WORD_AND_MASK;
       WORD_BLAST `word_and x ((word_subword:int16->num#num->int128) y (0,16)) =
                   word_zx (word_and (word_zx x) y)`]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

      (*** The actual tbl instructions ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (47--50) THEN

      (*** The table-based selection, brute forced by case analysis ***)

      SUBGOAL_THEN
       `read Q16 s50 = word(num_of_wordlist (FILTER (\x. val x < 3329)
                         [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
        read Q17 s50 = word(num_of_wordlist (FILTER (\x. val x < 3329)
                         [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15])) /\
        read Q18 s50 = word(num_of_wordlist (FILTER (\x. val x < 3329)
                         [x 16; x 17; x 18; x 19; x 20; x 21; x 22; x 23])) /\
        read Q19 s50 = word(num_of_wordlist (FILTER (\x. val x < 3329)
                         [x 24; x 25; x 26; x 27; x 28; x 29; x 30; x 31]))`
      MP_TAC THENL
       [UNDISCH_TAC
         `read(memory :> bytes(table,4096)) s50 =
          num_of_wordlist mlkem_rej_uniform_table` THEN
        REPLICATE_TAC 4
         (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
               [GSYM NUM_OF_PAIR_WORDLIST]) THEN
        REWRITE_TAC[mlkem_rej_uniform_table; pair_wordlist] THEN
        CONV_TAC WORD_REDUCE_CONV THEN
        CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
        REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q24 s = x`; `read Q25 s = x`;
          `read Q26 s = x`; `read Q27 s = x`] THEN
        MAP_EVERY EXPAND_TAC
         ["tab0"; "idx0"; "tab1"; "idx1"; "tab2"; "idx2"; "tab3"; "idx3"] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        ASM_REWRITE_TAC[FILTER] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REPLICATE_TAC 3 (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
        REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
        REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;

        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q16 s = x`; `read Q17 s = x`;
          `read Q18 s = x`; `read Q19 s = x`] THEN
        STRIP_TAC] THEN

      (*** The counting part, similarly brute-forced, though it's easier ***)

      SUBGOAL_THEN
       `read X12 s50 = word(LENGTH (FILTER (\x. val x < 3329)
                         [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
        read X13 s50 = word(LENGTH (FILTER (\x. val x < 3329)
                         [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15])) /\
        read X14 s50 = word(LENGTH (FILTER (\x. val x < 3329)
                         [x 16; x 17; x 18; x 19; x 20; x 21; x 22; x 23])) /\
        read X15 s50 = word(LENGTH (FILTER (\x. val x < 3329)
                         [x 24; x 25; x 26; x 27; x 28; x 29; x 30; x 31]))`
      MP_TAC THENL
       [ASM_REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; BITBLAST_RULE
         `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
          word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
          word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
          word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
          word_popcount(word_and (word 16) x:byte) = bitval(bit 4 x) /\
          word_popcount(word_and (word 32) x:byte) = bitval(bit 5 x) /\
          word_popcount(word_and (word 64) x:byte) = bitval(bit 6 x) /\
          word_popcount(word_and (word 128) x:byte) = bitval(bit 7 x)`] THEN
        DISCARD_STATE_TAC "s50" THEN REPEAT CONJ_TAC THEN
        REWRITE_TAC[WORD_MASK_ALT] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        ASM_REWRITE_TAC[FILTER] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        DISCARD_MATCHING_ASSUMPTIONS
         [`read X12 s = x`; `read X13 s = x`;
          `read X14 s = x`; `read X15 s = x`] THEN
        STRIP_TAC] THEN

      (*** Handle the overlapping writebacks, first some initialization ***)

      MAP_EVERY ABBREV_TAC
       [`lis0 = FILTER (\x. val x < 3329)
                       [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7]`;
        `lis1 = FILTER (\x. val x < 3329)
                       [x 8:int16; x 9; x 10; x 11; x 12; x 13; x 14; x 15]`;
        `lis2 = FILTER (\x. val x < 3329)
                       [x 16:int16; x 17; x 18; x 19; x 20; x 21; x 22; x 23]`;
        `lis3 = FILTER (\x. val x < 3329)
                         [x 24:int16; x 25; x 26; x 27; x 28; x 29; x 30; x 31]`;
        `len0 = LENGTH(lis0:int16 list)`;
        `len1 = LENGTH(lis1:int16 list)`;
        `len2 = LENGTH(lis2:int16 list)`;
        `len3 = LENGTH(lis3:int16 list)`] THEN

      SUBGOAL_THEN `len0 <= 8 /\ len1 <= 8 /\ len2 <= 8 /\ len3 <= 8`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["len0"; "len1"; "len2"; "len3"] THEN
        MAP_EVERY EXPAND_TAC ["lis0"; "lis1"; "lis2"; "lis3"] THEN
        REPEAT CONJ_TAC THEN
        W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN

      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

      (*** Now stupidly do 4 similar cut-and-paste blocks, first one ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (51--52) THEN
      ABBREV_TAC `curlist1:int16 list = APPEND curlist lis0` THEN
      ABBREV_TAC `curlen1:num = curlen + len0` THEN

      SUBGOAL_THEN
       `curlen1 < 264 /\
        read (memory :> bytes (stackpointer,2*curlen1)) s52 =
        num_of_wordlist(curlist1:int16 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen1"; "curlist1"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen < 256`; `len0 <= 8`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
          snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN

        UNDISCH_THEN
         `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen))))
               s52 =
          word (num_of_wordlist(lis0:int16 list))`
         (MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `2 * len0 = MIN 16 (2 * len0)` SUBST1_TAC THENL
         [UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_16] THEN
        UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (2 * l0)))
                               (word_shl (word l1) 1) =
                      word_add a (word(2 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist1:int16 list) = curlen1` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist1"; "curlen1"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** Second writeback ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (53--54) THEN
      ABBREV_TAC `curlist2:int16 list = APPEND curlist1 lis1` THEN
      ABBREV_TAC `curlen2:num = curlen1 + len1` THEN

      SUBGOAL_THEN
       `curlen2 < 272 /\
        read (memory :> bytes (stackpointer,2*curlen2)) s54 =
        num_of_wordlist(curlist2:int16 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen2"; "curlist2"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen1 < 264`; `len1 <= 8`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
          snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN

        UNDISCH_THEN
         `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen1))))
               s54 =
          word (num_of_wordlist(lis1:int16 list))`
         (MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `2 * len1 = MIN 16 (2 * len1)` SUBST1_TAC THENL
         [UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_16] THEN
        UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (2 * l0)))
                               (word_shl (word l1) 1) =
                      word_add a (word(2 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist2:int16 list) = curlen2` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist2"; "curlen2"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** Third writeback ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (55--56) THEN
      ABBREV_TAC `curlist3:int16 list = APPEND curlist2 lis2` THEN
      ABBREV_TAC `curlen3:num = curlen2 + len2` THEN

      SUBGOAL_THEN
       `curlen3 < 280 /\
        read (memory :> bytes (stackpointer,2*curlen3)) s56 =
        num_of_wordlist(curlist3:int16 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen3"; "curlist3"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen2 < 272`; `len2 <= 8`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
          snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN

        UNDISCH_THEN
         `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen2))))
               s56 =
          word (num_of_wordlist(lis2:int16 list))`
         (MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `2 * len2 = MIN 16 (2 * len2)` SUBST1_TAC THENL
         [UNDISCH_TAC `len2 <= 8` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_16] THEN
        UNDISCH_TAC `len2 <= 8` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (2 * l0)))
                               (word_shl (word l1) 1) =
                      word_add a (word(2 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist3:int16 list) = curlen3` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist3"; "curlen3"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** Fourth and final writeback ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (57--58) THEN
      ABBREV_TAC `curlist4:int16 list = APPEND curlist3 lis3` THEN
      ABBREV_TAC `curlen4:num = curlen3 + len3` THEN

      SUBGOAL_THEN
       `curlen4 < 288 /\
        read (memory :> bytes (stackpointer,2*curlen4)) s58 =
        num_of_wordlist(curlist4:int16 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen4"; "curlist4"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen3 < 280`; `len3 <= 8`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
          snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN

        UNDISCH_THEN
         `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen3))))
               s58 =
          word (num_of_wordlist(lis3:int16 list))`
         (MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `2 * len3 = MIN 16 (2 * len3)` SUBST1_TAC THENL
         [UNDISCH_TAC `len3 <= 8` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_16] THEN
        UNDISCH_TAC `len3 <= 8` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (2 * l0)))
                               (word_shl (word l1) 1) =
                      word_add a (word(2 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist4:int16 list) = curlen4` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist4"; "curlen4"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** The end of the loop ***)

      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (59--62) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

      REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; ADD_CLAUSES] THEN
      SUBGOAL_THEN
       `REJ_SAMPLE (SUB_LIST (32 * i,32) inlist) =
        APPEND (APPEND (APPEND lis0 lis1) lis2) lis3`
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["lis0"; "lis1"; "lis2"; "lis3"] THEN
        REWRITE_TAC[GSYM APPEND_ASSOC; GSYM FILTER_APPEND] THEN
        REWRITE_TAC[APPEND; REJ_SAMPLE] THEN AP_TERM_TAC THEN
        REWRITE_TAC[LIST_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
        REWRITE_TAC[LENGTH_MAP] THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
         [REWRITE_TAC[LENGTH_SUB_LIST] THEN MATCH_MP_TAC(ARITH_RULE
           `32 * (i + 1) <= l ==> MIN 32 (l - 32 * i) = 32`) THEN
          MAP_EVERY UNDISCH_TAC
           [`~(buflen < 48 * (i + 1))`;
            `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`] THEN
          ARITH_TAC;
          ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
          CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
        ASM_REWRITE_TAC[APPEND_ASSOC] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "cur" THEN
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      SUBST1_TAC(SYM(ASSUME `curlen3 + len3:num = curlen4`)) THEN
      SUBST1_TAC(SYM(ASSUME `curlen2 + len2:num = curlen3`)) THEN
      SUBST1_TAC(SYM(ASSUME `curlen1 + len1:num = curlen2`)) THEN
      SUBST1_TAC(SYM(ASSUME `curlen + len0:num = curlen1`)) THEN
      CONV_TAC WORD_RULE;

      (*** The (relatively) trivial loop-back goal ****)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `48 <= val(word_sub (word buflen:int64) (word (48 * i)))`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
        VAL_INT64_TAC `48 * i` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(buflen < 48 * (i + 1))` THEN ARITH_TAC;
        ALL_TAC] THEN
      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[] `~p ==> (if p then x else y) = y`) THEN
      ASM_SIMP_TAC[NOT_LE; VAL_WORD_LT];

      (*** Handling the cases possibly leading to the tail computation ***)

      SUBGOAL_THEN
       `LENGTH (REJ_SAMPLE (SUB_LIST (0,32 * N) inlist)) < 288`
      ASSUME_TAC THENL
       [ASM_CASES_TAC `N = 0` THENL
         [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
          REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
          FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`)] THEN
        ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
        MATCH_MP_TAC(ARITH_RULE
         `l' <= l + 32 ==> ~(b < x) /\ l < 256 ==> l' < 288`) THEN
        MP_TAC(ISPECL [`inlist:(12 word)list`; `32 * (N - 1)`; `32`; `0`]
            SUB_LIST_SPLIT) THEN
        ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 32 * (N - 1) + 32 = 32 * N`] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
        REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
        REWRITE_TAC[REJ_SAMPLE] THEN
        W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
        REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
        ALL_TAC] THEN
      VAL_INT64_TAC `LENGTH (REJ_SAMPLE (SUB_LIST (0,32 * N) inlist))` THEN
      SUBGOAL_THEN
       `48 <= val(word_sub (word buflen:int64) (word (48 * N))) <=>
        48 * (N + 1) <= buflen`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `48 * N < 2 EXP 64` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
          MAP_EVERY VAL_INT64_TAC [`48 * N`; `buflen:num`]] THEN
        ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN

      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_CASES_TAC `48 * (N + 1) <= buflen` THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--2) THEN
        FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
        ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
        ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `2 * N` THEN
        ASM_REWRITE_TAC[ARITH_RULE `16 * 2 * n = 32 * n`];
        ALL_TAC] THEN
       RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
           (REWRITE_RULE[CONJ_ASSOC] ENSURES_TRANS_SIMPLE))) THEN
       CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

     ALL_TAC] THEN

  (*** The initial case splits before settling into tail computation ***)

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `LENGTH (REJ_SAMPLE (SUB_LIST (0,32 * N) inlist)) < 288`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
      REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`)] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l' <= l + 32 ==> ~(b < x) /\ l < 256 ==> l' < 288`) THEN
    MP_TAC(ISPECL [`inlist:(12 word)list`; `32 * (N - 1)`; `32`; `0`]
        SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 32 * (N - 1) + 32 = 32 * N`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
    REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
    REWRITE_TAC[REJ_SAMPLE] THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
    ALL_TAC] THEN
  VAL_INT64_TAC `LENGTH (REJ_SAMPLE (SUB_LIST (0,32 * N) inlist))` THEN
  SUBGOAL_THEN
   `24 <= val(word_sub (word buflen:int64) (word (48 * N))) <=>
    48 * N + 24 <= buflen`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `48 * N < 2 EXP 64` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
      MAP_EVERY VAL_INT64_TAC [`48 * N`; `buflen:num`]] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,32 * N) inlist))` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--2) THENL
   [ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `2 * N` THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * 2 * n = 32 * n`];
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ASM_CASES_TAC `48 * N + 24 <= buflen` THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (3--4) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]);
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `2 * N` THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * 2 * n = 32 * n`] THEN
    UNDISCH_TAC `~(48 * N + 24 <= buflen)` THEN ARITH_TAC] THEN

  (*** Because of divisibility, exactly 24 buffer elements left ***)

  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  SUBGOAL_THEN `48 * N + 24 = buflen` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`48 * N + 24 <= buflen`; `buflen < 48 * (N + 1)`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM; ARITH_RULE `48 = 24 * 2`] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; ARITH_RULE `24 * n + 24 = 24 * (n + 1)`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL; LT_MULT_LCANCEL] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The tail computation, a half-sized version of the main loop ***)

  ABBREV_TAC `cur:int64 = word_add buf (word (48 * N))` THEN
  ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,32 * N) inlist)` THEN
  ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
  ASM_REWRITE_TAC[] THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = read (memory :> bytes64 cur) s4`;
    `q1 = read (memory :> bytes64 (word_add cur (word 8))) s4`;
    `q2 = read (memory :> bytes64 (word_add cur (word 16))) s4`] THEN

  (*** Abbreviate the next 16 digits as 16-bit words ***)

  ABBREV_TAC
   `(x:num->int16) j =
    word_zx(word_subword (read (memory :> wbytes cur) s4:192 word)
                               (12 * j,12):12 word)` THEN

  (*** The loading with LD3 and full de-interleaving / zero-extension ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (5--12) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

  SUBGOAL_THEN
   `read Q16 s12 =
        word_join (word_join (word_join (x 7) (x 6):int32)
                             (word_join (x 5) (x 4):int32):int64)
                  (word_join (word_join (x 3) (x 2):int32)
                             (word_join (x 1) (x 0:int16):int32):int64) /\
    read Q17 s12 =
        word_join (word_join (word_join (x 15) (x 14):int32)
                             (word_join (x 13) (x 12):int32):int64)
                  (word_join (word_join (x 11) (x 10):int32)
                             (word_join (x 9) (x 8:int16):int32):int64)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[READ_MEMORY_TRIPLES_SPLIT] THEN REPEAT CONJ_TAC THEN
    GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[word_subdeinterleave; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC[] THEN NO_TAC;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`] THEN
    STRIP_TAC] THEN

  (**** Later in the proof, we actually want this equivalent ***)

  SUBGOAL_THEN
   `!j. j < 16
        ==> (word_zx:12 word->int16)
            (EL j (SUB_LIST(32 * N,16) inlist)) = x j`
  ASSUME_TAC THENL
   [UNDISCH_THEN
     `read (memory :> bytes (buf,buflen)) s12 =
      num_of_wordlist(inlist:(12 word)list)`
     (MP_TAC o AP_TERM
       `\x. x DIV 2 EXP (8 * 48 * N) MOD 2 EXP (8 * 24)`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
    REWRITE_TAC[READ_BYTES_MOD] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[ARITH_RULE `8 * 24 = 12 * 16 * 1`] THEN
    REWRITE_TAC[ARITH_RULE `8 * 48 * x = 12 * 32 * x`] THEN
    REWRITE_TAC[GSYM DIMINDEX_12; GSYM NUM_OF_WORDLIST_SUB_LIST] THEN
    SUBGOAL_THEN
     `MIN (buflen - 48 * N) 24 = dimindex(:192) DIV 8`
    SUBST1_TAC THENL
     [REWRITE_TAC[DIMINDEX_192] THEN
      UNDISCH_TAC `48 * N + 24 = buflen` THEN ARITH_TAC;
      REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM VAL_READ_WBYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; GSYM READ_COMPONENT_COMPOSE]] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[word_zx; VAL_WORD_SUBWORD] THEN
    REWRITE_TAC[MULT_CLAUSES; DIMINDEX_12; ARITH_RULE `MIN n n = n`] THEN
    REWRITE_TAC[GSYM DIMINDEX_12; NUM_OF_WORDLIST_EL] THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN

  (*** The comparisons and table index computation ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (13--20) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  RULE_ASSUM_TAC(REWRITE_RULE [word_ugt; relational2; GT; WORD_AND_MASK;
   WORD_BLAST `word_and x ((word_subword:int16->num#num->int128) y (0,16)) =
               word_zx (word_and (word_zx x) y)`]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  (*** Abbreviate the table entries and perform the table loads ***)

  MAP_EVERY REABBREV_TAC
   [`idx0 = read X12 s20`; `idx1 = read X13 s20`] THEN

  MAP_EVERY ABBREV_TAC
   [`tab0 =
     read(memory :> bytes128(word_add table (word(16 * val(idx0:int64))))) s20`;
    `tab1 =
     read(memory :> bytes128(word_add table (word(16 * val(idx1:int64))))) s20`] THEN

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (21--28) THEN

  (*** Repeating all the simplifications above actually. Just here? ***)

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  RULE_ASSUM_TAC(REWRITE_RULE [word_ugt; relational2; GT; WORD_AND_MASK;
   WORD_BLAST `word_and x ((word_subword:int16->num#num->int128) y (0,16)) =
               word_zx (word_and (word_zx x) y)`]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  (*** The actual tbl instructions ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (29--30) THEN

  (*** The table-based selection, brute forced by case analysis ***)

  SUBGOAL_THEN
   `read Q16 s30 = word(num_of_wordlist (FILTER (\x. val x < 3329)
                     [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
    read Q17 s30 = word(num_of_wordlist (FILTER (\x. val x < 3329)
                     [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15]))`
  MP_TAC THENL
   [UNDISCH_TAC
     `read(memory :> bytes(table,4096)) s30 =
      num_of_wordlist mlkem_rej_uniform_table` THEN
    REPLICATE_TAC 4
     (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
           [GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[mlkem_rej_uniform_table; pair_wordlist] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q24 s = x`; `read Q25 s = x`] THEN
    MAP_EVERY EXPAND_TAC ["tab0"; "idx0"; "tab1"; "idx1"] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[FILTER] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REPLICATE_TAC 3 (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
    REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;
    DISCARD_MATCHING_ASSUMPTIONS [`read Q16 s = x`; `read Q17 s = x`] THEN
    STRIP_TAC] THEN

  (*** The counting part, similarly brute-forced, though it's easier ***)

  SUBGOAL_THEN
   `read X12 s30 = word(LENGTH (FILTER (\x. val x < 3329)
                     [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
    read X13 s30 = word(LENGTH (FILTER (\x. val x < 3329)
                     [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15]))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; BITBLAST_RULE
     `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
      word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
      word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
      word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
      word_popcount(word_and (word 16) x:byte) = bitval(bit 4 x) /\
      word_popcount(word_and (word 32) x:byte) = bitval(bit 5 x) /\
      word_popcount(word_and (word 64) x:byte) = bitval(bit 6 x) /\
      word_popcount(word_and (word 128) x:byte) = bitval(bit 7 x)`] THEN
    DISCARD_STATE_TAC "s30" THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[WORD_MASK_ALT] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[FILTER] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    DISCARD_MATCHING_ASSUMPTIONS [`read X12 s = x`; `read X13 s = x`] THEN
    STRIP_TAC] THEN

  (*** Handle the overlapping writebacks, first some initialization ***)

  MAP_EVERY ABBREV_TAC
   [`lis0 = FILTER (\x. val x < 3329)
                   [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7]`;
    `lis1 = FILTER (\x. val x < 3329)
                   [x 8:int16; x 9; x 10; x 11; x 12; x 13; x 14; x 15]`;
    `len0 = LENGTH(lis0:int16 list)`;
    `len1 = LENGTH(lis1:int16 list)`] THEN

  SUBGOAL_THEN `len0 <= 8 /\ len1 <= 8`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["len0"; "len1"] THEN
    MAP_EVERY EXPAND_TAC ["lis0"; "lis1"] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Now stupidly do 2 similar cut-and-paste blocks, first one ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (31--32) THEN
  ABBREV_TAC `curlist1:int16 list = APPEND curlist lis0` THEN
  ABBREV_TAC `curlen1:num = curlen + len0` THEN

  SUBGOAL_THEN
   `curlen1 < 264 /\
    read (memory :> bytes (stackpointer,2*curlen1)) s32 =
    num_of_wordlist(curlist1:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen1"; "curlist1"] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen < 256`; `len0 <= 8`] THEN ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
      snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN

    UNDISCH_THEN
     `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen))))
           s32 =
      word (num_of_wordlist(lis0:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len0 = MIN 16 (2 * len0)` SUBST1_TAC THENL
     [UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist1:int16 list) = curlen1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist1"; "curlen1"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Second writeback ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (33--34) THEN
  ABBREV_TAC `curlist2:int16 list = APPEND curlist1 lis1` THEN
  ABBREV_TAC `curlen2:num = curlen1 + len1` THEN

  SUBGOAL_THEN
   `curlen2 < 272 /\
    read (memory :> bytes (stackpointer,2*curlen2)) s34 =
    num_of_wordlist(curlist2:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen2"; "curlist2"] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen1 < 264`; `len1 <= 8`] THEN ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
      snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN

    UNDISCH_THEN
     `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen1))))
           s34 =
      word (num_of_wordlist(lis1:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len1 = MIN 16 (2 * len1)` SUBST1_TAC THENL
     [UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist2:int16 list) = curlen2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist2"; "curlen2"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The end of the loop ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (35--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `2 * N + 1` THEN
  REWRITE_TAC[ARITH_RULE `16 * (2 * N + 1) = 32 * N + 16`] THEN
  ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `REJ_SAMPLE (SUB_LIST (32 * N,16) inlist) =
    APPEND lis0 lis1`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lis0"; "lis1"] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; GSYM FILTER_APPEND] THEN
    REWRITE_TAC[APPEND; REJ_SAMPLE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[LENGTH_MAP] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN MAP_EVERY UNDISCH_TAC
       [`48 * N + 24 = buflen`;
        `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`] THEN
      ARITH_TAC;
      ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
    ASM_REWRITE_TAC[APPEND_ASSOC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
  ASM_SIMP_TAC[ARITH_RULE `l < 272 ==> l < 288`] THEN
  ASM_REWRITE_TAC[ARITH_RULE
   `24 * ((2 * N + 1) + 1) = (48 * N + 24) + 24`] THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `curlen1 + len1:num = curlen2`)) THEN
  SUBST1_TAC(SYM(ASSUME `curlen + len0:num = curlen1`)) THEN
  CONV_TAC WORD_RULE);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_REJ_UNIFORM_SUBROUTINE_CORRECT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer returnaddress.
        24 divides val buflen /\
        8 * val buflen = 12 * LENGTH inlist /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
            [(word pc,0x258); (buf,val buflen); (table,4096)] /\
        ALL (nonoverlapping (res,512))
            [(word pc,0x258); (word_sub stackpointer (word 576),576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,4096)) s =
                  num_of_wordlist mlkem_rej_uniform_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = returnaddress /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,2 * outlen)) s =
                  num_of_wordlist outlist)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,512);
                         memory :> bytes(word_sub stackpointer (word 576),576)])`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC MLKEM_REJ_UNIFORM_EXEC
   (CONV_RULE (TOP_DEPTH_CONV let_CONV) MLKEM_REJ_UNIFORM_CORRECT)
    `[]:int64 list` 576);;
