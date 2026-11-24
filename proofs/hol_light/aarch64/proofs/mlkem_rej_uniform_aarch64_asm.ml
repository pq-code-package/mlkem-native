(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling for ML-KEM, filtering packed numbers < 3329.   *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_rej_uniform_table.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_rej_uniform_aarch64_asm.o";;
 ****)

let mlkem_rej_uniform_mc = define_assert_from_elf
  "mlkem_rej_uniform_mc" "aarch64/mlkem/mlkem_rej_uniform_aarch64_asm.o"
(*** BYTECODE START ***)
[
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
  0x4f00e424;       (* arm_MOVI Q4 (word 72340172838076673) *)
  0x4f3057fc;       (* arm_SHL_VEC Q28 Q31 16 32 128 *)
  0x6f30079c;       (* arm_USHR_VEC Q28 Q28 16 32 128 *)
  0x6f3007fd;       (* arm_USHR_VEC Q29 Q31 16 32 128 *)
  0x4ea49f9c;       (* arm_MUL_VEC Q28 Q28 Q4 32 128 *)
  0x4ea49fbd;       (* arm_MUL_VEC Q29 Q29 Q4 32 128 *)
  0x5281a024;       (* arm_MOV W4 (rvalue (word 3329)) *)
  0x4e020c9e;       (* arm_DUP_GEN Q30 X4 16 128 *)
  0xd2802007;       (* arm_MOV X7 (rvalue (word 256)) *)
  0xf2a08067;       (* arm_MOVK X7 (word 1027) 16 *)
  0xf2c0e0c7;       (* arm_MOVK X7 (word 1798) 32 *)
  0xf2e14127;       (* arm_MOVK X7 (word 2569) 48 *)
  0xd281a18b;       (* arm_MOV X11 (rvalue (word 3340)) *)
  0xf2a201eb;       (* arm_MOVK X11 (word 4111) 16 *)
  0xf2c2624b;       (* arm_MOVK X11 (word 4882) 32 *)
  0xf2e2c2ab;       (* arm_MOVK X11 (word 5653) 48 *)
  0x9e6700f4;       (* arm_FMOV_ItoF Q20 X7 0 *)
  0x4e181d74;       (* arm_INS_GEN Q20 X11 64 64 *)
  0x4f00e424;       (* arm_MOVI Q4 (word 72340172838076673) *)
  0x4f00e505;       (* arm_MOVI Q5 (word 578721382704613384) *)
  0x4e248695;       (* arm_ADD_VEC Q21 Q20 Q4 8 128 *)
  0x4e258696;       (* arm_ADD_VEC Q22 Q20 Q5 8 128 *)
  0x4e2486d7;       (* arm_ADD_VEC Q23 Q22 Q4 8 128 *)
  0xd2800009;       (* arm_MOV X9 (rvalue (word 0)) *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 48)) *)
  0x54000803;       (* arm_BCC (word 256) *)
  0xf103813f;       (* arm_CMP X9 (rvalue (word 224)) *)
  0x540007c8;       (* arm_BHI (word 248) *)
  0xd100c042;       (* arm_SUB X2 X2 (rvalue (word 48)) *)
  0x4cdfa020;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (word 32)) *)
  0x4cdf7022;       (* arm_LDR Q2 X1 (Postimmediate_Offset (word 16)) *)
  0x4e142004;       (* arm_TBL2 Q4 Q0 Q1 Q20 128 *)
  0x4e162025;       (* arm_TBL2 Q5 Q1 Q2 Q22 128 *)
  0x4e152006;       (* arm_TBL2 Q6 Q0 Q1 Q21 128 *)
  0x4e172027;       (* arm_TBL2 Q7 Q1 Q2 Q23 128 *)
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
  0x4e052884;       (* arm_TRN1 Q4 Q4 Q5 8 128 *)
  0x4e0728c5;       (* arm_TRN1 Q5 Q6 Q7 8 128 *)
  0x4e456886;       (* arm_TRN2 Q6 Q4 Q5 16 128 *)
  0x4e452884;       (* arm_TRN1 Q4 Q4 Q5 16 128 *)
  0x4e3c1c84;       (* arm_AND_VEC Q4 Q4 Q28 128 *)
  0x4e3d1cc6;       (* arm_AND_VEC Q6 Q6 Q29 128 *)
  0x4ea68484;       (* arm_ADD_VEC Q4 Q4 Q6 32 128 *)
  0x6eb03880;       (* arm_UADDLV Q0 Q4 4 32 *)
  0x9e66000f;       (* arm_FMOV_FtoI X15 Q0 0 64 *)
  0xd3401dec;       (* arm_UBFM X12 X15 0 7 *)
  0xd3483ded;       (* arm_UBFM X13 X15 8 15 *)
  0xd3505dee;       (* arm_UBFM X14 X15 16 23 *)
  0xd3587def;       (* arm_UBFM X15 X15 24 31 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x3cee787a;       (* arm_LDR Q26 X3 (Shiftreg_Offset X14 4) *)
  0x3cef787b;       (* arm_LDR Q27 X3 (Shiftreg_Offset X15 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x6eb03880;       (* arm_UADDLV Q0 Q4 4 32 *)
  0x9e66000f;       (* arm_FMOV_FtoI X15 Q0 0 64 *)
  0xd3400dec;       (* arm_UBFM X12 X15 0 3 *)
  0xd3482ded;       (* arm_UBFM X13 X15 8 11 *)
  0xd3504dee;       (* arm_UBFM X14 X15 16 19 *)
  0xd3586def;       (* arm_UBFM X15 X15 24 27 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x4e1a0252;       (* arm_TBL Q18 [Q18] Q26 128 *)
  0x4e1b0273;       (* arm_TBL Q19 [Q19] Q27 128 *)
  0x4c007410;       (* arm_STR Q16 X0 No_Offset *)
  0x8b0c0400;       (* arm_ADD X0 X0 (Shiftedreg X12 LSL 1) *)
  0x4c007411;       (* arm_STR Q17 X0 No_Offset *)
  0x8b0d0400;       (* arm_ADD X0 X0 (Shiftedreg X13 LSL 1) *)
  0x4c007412;       (* arm_STR Q18 X0 No_Offset *)
  0x8b0e0400;       (* arm_ADD X0 X0 (Shiftedreg X14 LSL 1) *)
  0x4c007413;       (* arm_STR Q19 X0 No_Offset *)
  0x8b0f0400;       (* arm_ADD X0 X0 (Shiftedreg X15 LSL 1) *)
  0x8b0d018c;       (* arm_ADD X12 X12 X13 *)
  0x8b0f01ce;       (* arm_ADD X14 X14 X15 *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0x8b0e0129;       (* arm_ADD X9 X9 X14 *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 48)) *)
  0x54fff842;       (* arm_BCS (word 2096904) *)
  0xf100605f;       (* arm_CMP X2 (rvalue (word 24)) *)
  0x54000743;       (* arm_BCC (word 232) *)
  0xf103c13f;       (* arm_CMP X9 (rvalue (word 240)) *)
  0x54000448;       (* arm_BHI (word 136) *)
  0xd1006042;       (* arm_SUB X2 X2 (rvalue (word 24)) *)
  0x4cdf7020;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 16)) *)
  0x0cdf7021;       (* arm_LDR D1 X1 (Postimmediate_Offset (word 8)) *)
  0x4e142004;       (* arm_TBL2 Q4 Q0 Q1 Q20 128 *)
  0x4e152005;       (* arm_TBL2 Q5 Q0 Q1 Q21 128 *)
  0x6f07b604;       (* arm_BIC_VEC Q4 Q4 (rvalue (word 319019586840962221640188233472310046720)) 128 *)
  0x6f1c04a5;       (* arm_USHR_VEC Q5 Q5 4 16 128 *)
  0x4e453890;       (* arm_ZIP1 Q16 Q4 Q5 16 128 *)
  0x4e457891;       (* arm_ZIP2 Q17 Q4 Q5 16 128 *)
  0x6e7037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 16 128 *)
  0x6e7137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 16 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x6e703880;       (* arm_UADDLV Q0 Q4 8 16 *)
  0x6e7038a1;       (* arm_UADDLV Q1 Q5 8 16 *)
  0x1e26000c;       (* arm_FMOV_FtoI W12 Q0 0 32 *)
  0x1e26002d;       (* arm_FMOV_FtoI W13 Q1 0 32 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x6e703880;       (* arm_UADDLV Q0 Q4 8 16 *)
  0x6e7038a1;       (* arm_UADDLV Q1 Q5 8 16 *)
  0x1e26000c;       (* arm_FMOV_FtoI W12 Q0 0 32 *)
  0x1e26002d;       (* arm_FMOV_FtoI W13 Q1 0 32 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x4c007410;       (* arm_STR Q16 X0 No_Offset *)
  0x8b0c0400;       (* arm_ADD X0 X0 (Shiftedreg X12 LSL 1) *)
  0x4c007411;       (* arm_STR Q17 X0 No_Offset *)
  0x8b0d0400;       (* arm_ADD X0 X0 (Shiftedreg X13 LSL 1) *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0x8b0d0129;       (* arm_ADD X9 X9 X13 *)
  0xf104013f;       (* arm_CMP X9 (rvalue (word 256)) *)
  0x540002a2;       (* arm_BCS (word 84) *)
  0xb4000282;       (* arm_CBZ X2 (word 80) *)
  0x39400025;       (* arm_LDRB W5 X1 (Immediate_Offset (word 0)) *)
  0x39400427;       (* arm_LDRB W7 X1 (Immediate_Offset (word 1)) *)
  0x39400826;       (* arm_LDRB W6 X1 (Immediate_Offset (word 2)) *)
  0x91000c21;       (* arm_ADD X1 X1 (rvalue (word 3)) *)
  0xd1000c42;       (* arm_SUB X2 X2 (rvalue (word 3)) *)
  0x33180ce5;       (* arm_BFM W5 W7 24 3 *)
  0x53047ce7;       (* arm_LSR W7 W7 4 *)
  0x2a0610e6;       (* arm_ORR W6 W7 (Shiftedreg W6 LSL 4) *)
  0x6b0400bf;       (* arm_CMP W5 W4 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0x78002405;       (* arm_STRH W5 X0 (Postimmediate_Offset (word 2)) *)
  0x91000529;       (* arm_ADD X9 X9 (rvalue (word 1)) *)
  0xf104013f;       (* arm_CMP X9 (rvalue (word 256)) *)
  0x54fffe02;       (* arm_BCS (word 2097088) *)
  0x6b0400df;       (* arm_CMP W6 W4 *)
  0x54fffdc2;       (* arm_BCS (word 2097080) *)
  0x78002406;       (* arm_STRH W6 X0 (Postimmediate_Offset (word 2)) *)
  0x91000529;       (* arm_ADD X9 X9 (rvalue (word 1)) *)
  0x17ffffeb;       (* arm_B (word 268435372) *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_REJ_UNIFORM_EXEC = ARM_MK_EXEC_RULE mlkem_rej_uniform_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_REJ_UNIFORM_MC =
  REWRITE_CONV[mlkem_rej_uniform_mc] `LENGTH mlkem_rej_uniform_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

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

(* Count accepted coefficients in a group of eight. *)
let LENGTH_FILTER_EIGHT = prove
 (`!P (a:A) b c d e f g h.
     LENGTH (FILTER P [a;b;c;d;e;f;g;h]) =
     bitval(P a) + bitval(P b) + bitval(P c) + bitval(P d) +
     bitval(P e) + bitval(P f) + bitval(P g) + bitval(P h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FILTER] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[LENGTH; bitval] THEN ARITH_TAC);;

let WORD_SUBWORD_8_64 = prove
 (`!(x:N word) pos.
     (word_subword x (pos,8):int64) =
     word_zx (word_subword x (pos,8):byte)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_ZX;
              DIMINDEX_8; DIMINDEX_64] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < 8` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let VAL_WORD_ZX_8_64 = prove
 (`!x:byte. val(word_zx x:int64) < 256`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(x:byte) < 18446744073709551616`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;


(* Helper: discharge the memsafe postcondition
     exists e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 R W
   after symbolic simulation, using accumulated events from the invariant.
   This is DISCHARGE_SAFETY_PROPERTY_TAC minus the f_events unification. *)
let DISCHARGE_MEMSAFE_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* Like SIMPLE_ARITH_TAC but allows `val` in assumptions since
   contained_modulo bounds may involve val terms. Filters out
   read/write/word simulation cruft that makes ASM_ARITH_TAC slow. *)
let (MEMSAFE_ARITH_TAC:tactic) =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "word"] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n avoiders | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  let tweak = GEN_REWRITE_RULE TRY_CONV [ARITH_RULE `~(n = 0) <=> 1 <= n`] in
  W(fun (asl,w) ->
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o tweak o snd) asl' THEN CONV_TAC ARITH_RULE);;

(* ASM-aware version of CONTAINED_TAC for loop-body proofs where
   memory addresses involve symbolic loop variables. Uses MEMSAFE_ARITH_TAC
   which filters assumptions to avoid the performance issues of ASM_ARITH_TAC
   with hundreds of symbolic simulation assumptions. *)
let CONTAINED_ASM_TAC =
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  GEN_REWRITE_TAC I [CONTAINED_MODULO_MOD2] THEN
  ((GEN_REWRITE_TAC I [CONTAINED_MODULO_REFL] THEN
    MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN MEMSAFE_ARITH_TAC));;

(* ASM-aware version of DISCHARGE_MEMSAFE_TAC for loop bodies.
   Uses MEMSAFE_ARITH_TAC for contained_modulo proofs with symbolic bounds. *)
let DISCHARGE_MEMSAFE_ASM_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
    REPEAT CONJ_TAC THEN
    TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
                CONTAINED_ASM_TAC) THEN NO_TAC);
    REWRITE_TAC[APPEND; APPEND_NIL] THEN
    FIRST_ASSUM ACCEPT_TAC];;

(* Strip an existential assumption of the form
   `?e_acc. read events s = APPEND e_acc e /\ memaccess_inbounds ...`
   into separate assumptions. Used at ENSURES_INIT_TAC boundaries. *)
let STRIP_EXISTS_ASSUM_TAC =
  FIRST_X_ASSUM(CHOOSE_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC)));;

(* After n candidates, the output cursor follows the accepted prefix. *)
let rej_uniform_state = new_definition
 `rej_uniform_state res buf buflen table (inlist:(12 word)list) e n
    (outlist:int16 list) s <=>
    let outlen = LENGTH outlist in
    read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
    read (memory :> bytes (table,4096)) s =
      num_of_wordlist mlkem_rej_uniform_table /\
    read X0 s = word_add res (word (2 * outlen)) /\
    read X1 s = word_add buf (word (3 * n)) /\
    read X2 s = word_sub (word buflen) (word (3 * n)) /\
    read X3 s = table /\ read X4 s = word 3329 /\
    read X9 s = word outlen /\
    read (memory :> bytes (res,2 * outlen)) s = num_of_wordlist outlist /\
    (?e2. read events s = APPEND e2 e /\
          memaccess_inbounds e2 [buf,buflen; table,4096] [res,512])`;;

let rej_uniform_prefix = new_definition
 `rej_uniform_prefix res buf buflen table inlist e n s <=>
    rej_uniform_state res buf buflen table inlist e n
      (REJ_SAMPLE (SUB_LIST (0,2 * n) inlist)) s`;;

let rej_uniform_scalar_prefix = new_definition
 `rej_uniform_scalar_prefix res buf buflen table inlist e n s <=>
    rej_uniform_state res buf buflen table inlist e n
      (SUB_LIST(0,256) (REJ_SAMPLE (SUB_LIST (0,2 * n) inlist))) s`;;

let rej_uniform_vectors = new_definition
 `rej_uniform_vectors s <=>
    read Q20 s = word 0x16151312100f0d0c0a09070604030100 /\
    read Q21 s = word 0x1716141311100e0d0b0a080705040201 /\
    read Q22 s = word 0x1e1d1b1a1817151412110f0e0c0b0908 /\
    read Q23 s = word 0x1f1e1c1b191816151312100f0d0c0a09 /\
    read Q28 s = word 0x40404040101010100404040401010101 /\
    read Q29 s = word 0x80808080202020200808080802020202 /\
    read Q30 s = word 0x0d010d010d010d010d010d010d010d01 /\
    read Q31 s = word 0x00800040002000100008000400020001`;;

let REJ_UNIFORM_LENGTH_STEP = prove
 (`!inlist:(12 word)list. !n k.
     LENGTH(REJ_SAMPLE(SUB_LIST(0,n+k) inlist)) <=
     LENGTH(REJ_SAMPLE(SUB_LIST(0,n) inlist)) + k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND;
    ADD_CLAUSES; LENGTH_APPEND; LE_ADD_LCANCEL] THEN
  REWRITE_TAC[REJ_SAMPLE] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `LENGTH(MAP (word_zx:12 word->int16) (SUB_LIST(n,k) inlist))` THEN
  REWRITE_TAC[LENGTH_FILTER; LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC);;

let MLKEM_REJ_UNIFORM_INIT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e.
     nonoverlapping (res,512) (word pc,LENGTH mlkem_rej_uniform_mc)
     ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word pc /\ C_ARGUMENTS [res;buf;word buflen;table] s /\
            read (memory :> bytes (table,4096)) s =
              num_of_wordlist mlkem_rej_uniform_table /\
            read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
            read events s = e)
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word (pc + 0x88) /\ rej_uniform_vectors s /\
            rej_uniform_prefix res buf buflen table inlist e 0 s)
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes (res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rej_uniform_vectors; rej_uniform_prefix; rej_uniform_state;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
    LENGTH_MLKEM_REJ_UNIFORM_MC] THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `q20_init:int128` `read Q20` THEN
  GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--34) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
  REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0;
    READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist] THEN
  EXISTS_TAC `[]:uarch_event list` THEN REWRITE_TAC[APPEND;
    memaccess_inbounds; ALL]);;

(* Both loop tests branch on the remaining input and output capacity. *)
let MLKEM_REJ_UNIFORM_TEST32 = prove
 (`!res buf buflen table (inlist:(12 word)list) e i pc first take.
     let len = LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist)) in
     buflen < 2 EXP 64 /\ 48 * i <= buflen /\ len <= 256 /\
     (take <=> 48 * i + 48 <= buflen /\ len <= 224) /\
     nonoverlapping (res,512) (word pc,LENGTH mlkem_rej_uniform_mc)
     ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word (pc + (if first then 0x88 else 0x184)) /\
            rej_uniform_vectors s /\
            rej_uniform_prefix res buf buflen table inlist e (16 * i) s)
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word (pc + (if take then 0x98 else 0x18c)) /\
            rej_uniform_vectors s /\
            rej_uniform_prefix res buf buflen table inlist e (16 * i) s)
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes (res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rej_uniform_vectors; rej_uniform_prefix; rej_uniform_state;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_MLKEM_REJ_UNIFORM_MC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 * 16 * i = 32 * i`] THEN STRIP_TAC THEN
  ABBREV_TAC `len = LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist))` THEN
  SUBGOAL_THEN `val (word_sub (word buflen) (word (3 * 16 * i)):int64) =
                buflen - 48 * i` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 * 16 * i = 48 * i`] THEN
    SUBGOAL_THEN `48 * i < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY VAL_INT64_TAC [`48 * i`; `buflen:num`] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES]; ALL_TAC] THEN
  VAL_INT64_TAC `len:num` THEN VAL_INT64_TAC `224` THEN
  SUBGOAL_THEN `(224 <= len /\ ~(val(word_sub (word len) (word 224):int64) = 0))
                <=> ~(len <= 224)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(48 <= buflen - 48 * i <=> 48 * i + 48 <= buflen)`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `first:bool` THEN (ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ASM_CASES_TAC `48 * i + 48 <= buflen` THENL
   [ASM_CASES_TAC `len <= 224` THEN ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--4);
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--2)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  DISCHARGE_MEMSAFE_ASM_TAC));;

let MLKEM_REJ_UNIFORM_TEST16 = prove
 (`!res buf buflen table (inlist:(12 word)list) e i pc.
     let len = LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist)) in
     buflen < 2 EXP 64 /\ 48 * i <= buflen /\ len <= 256 /\
     nonoverlapping (res,512) (word pc,LENGTH mlkem_rej_uniform_mc)
     ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word(pc + 0x18c) /\ rej_uniform_vectors s /\
            rej_uniform_prefix res buf buflen table inlist e (16 * i) s)
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word(pc + (if 48 * i + 24 <= buflen then
              if len <= 240 then 0x19c else 0x220 else 0x278)) /\
            rej_uniform_vectors s /\
            rej_uniform_prefix res buf buflen table inlist e (16 * i) s)
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes (res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rej_uniform_vectors; rej_uniform_prefix; rej_uniform_state;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_MLKEM_REJ_UNIFORM_MC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 * 16 * i = 32 * i`] THEN STRIP_TAC THEN
  ABBREV_TAC `len = LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist))` THEN
  SUBGOAL_THEN `val (word_sub (word buflen) (word (3 * 16 * i)):int64) =
                buflen - 48 * i` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 * 16 * i = 48 * i`] THEN
    SUBGOAL_THEN `48 * i < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY VAL_INT64_TAC [`48 * i`; `buflen:num`] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES]; ALL_TAC] THEN
  VAL_INT64_TAC `len:num` THEN VAL_INT64_TAC `240` THEN
  SUBGOAL_THEN `(240 <= len /\ ~(val(word_sub (word len) (word 240):int64) = 0))
                <=> ~(len <= 240)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(24 <= buflen - 48 * i <=> 48 * i + 24 <= buflen)`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ASM_CASES_TAC `48 * i + 24 <= buflen` THENL
   [ASM_CASES_TAC `len <= 240` THEN ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--4);
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--2)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  DISCHARGE_MEMSAFE_ASM_TAC);;

let REJ_UNIFORM_BLOCK_COUNT = prove
 (`!buflen (inlist:(12 word)list).
     ?N. 48 * N <= buflen /\
         LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * N) inlist)) <= 256 /\
         ~(48 * N + 48 <= buflen /\
           LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * N) inlist)) <= 224) /\
         (!i. i < N ==> 48 * i + 48 <= buflen /\
             LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist)) <= 224)`,
  REPEAT GEN_TAC THEN SUBGOAL_THEN
   `?i. ~(48 * i + 48 <= buflen /\
          LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist)) <= 224)` MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN REWRITE_TAC[NOT_CLAUSES]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `N = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY;
                    LENGTH; LE_0] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> N - 1 < N`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`inlist:(12 word)list`; `32 * (N - 1)`; `32`]
      REJ_UNIFORM_LENGTH_STEP) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 32 * (N - 1) + 32 = 32 * N`] THEN
    ASM_ARITH_TAC]);;

let MLKEM_REJ_UNIFORM_BLOCK32 = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e i.
     buflen < 2 EXP 64 /\ 8 * buflen = 12 * LENGTH inlist /\
     48 * i + 48 <= buflen /\
     LENGTH (REJ_SAMPLE (SUB_LIST (0,32 * i) inlist)) <= 224 /\
     ALL (nonoverlapping (res,512))
       [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,buflen); (table,4096)]
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x98) /\ rej_uniform_vectors s /\
                rej_uniform_prefix res buf buflen table inlist e (16 * i) s)
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x184) /\ rej_uniform_vectors s /\
                rej_uniform_prefix res buf buflen table inlist e (16 * (i + 1)) s)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes (res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_MLKEM_REJ_UNIFORM_MC;
    rej_uniform_vectors; rej_uniform_prefix; rej_uniform_state] THEN STRIP_TAC THEN
  ABBREV_TAC `cur:int64 = word_add buf (word (48 * i))` THEN
  ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,32 * i) inlist)` THEN
  ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * 16 * n = 32 * n /\ 3 * 16 * n = 48 * n`] THEN
  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`q0 = read (memory :> bytes128 cur) s0`;
    `q1 = read (memory :> bytes128 (word_add cur (word 16))) s0`;
    `q2 = read (memory :> bytes128 (word_add cur (word 32))) s0`] THEN

  (*** Abbreviate the next 32 digits as 16-bit words ***)

  ABBREV_TAC
   `(x:num->int16) j =
    word_zx(word_subword (read (memory :> wbytes cur) s0:384 word)
                               (12 * j,12):12 word)` THEN

  (*** The byte-lane loads and TBL de-interleaving ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--15) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

  SUBGOAL_THEN
   `read Q16 s15 =
        word_join (word_join (word_join (x 7) (x 6):int32)
                             (word_join (x 5) (x 4):int32):int64)
                  (word_join (word_join (x 3) (x 2):int32)
                             (word_join (x 1) (x 0:int16):int32):int64) /\
    read Q17 s15 =
        word_join (word_join (word_join (x 15) (x 14):int32)
                             (word_join (x 13) (x 12):int32):int64)
                  (word_join (word_join (x 11) (x 10):int32)
                             (word_join (x 9) (x 8:int16):int32):int64) /\
    read Q18 s15 =
        word_join (word_join (word_join (x 23) (x 22):int32)
                             (word_join (x 21) (x 20):int32):int64)
                  (word_join (word_join (x 19) (x 18):int32)
                             (word_join (x 17) (x 16:int16):int32):int64) /\
    read Q19 s15 =
        word_join (word_join (word_join (x 31) (x 30):int32)
                             (word_join (x 29) (x 28):int32):int64)
                  (word_join (word_join (x 27) (x 26):int32)
                             (word_join (x 25) (x 24:int16):int32):int64)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[READ_MEMORY_TRIPLES_SPLIT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_BLAST;
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
     `read (memory :> bytes (buf,buflen)) s15 =
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
       `48 * i + 48 <= b ==> MIN (b - 48 * i) 48 = 48`) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM VAL_READ_WBYTES] THEN
      ASM_REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE]] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[word_zx; VAL_WORD_SUBWORD] THEN
    REWRITE_TAC[MULT_CLAUSES; DIMINDEX_12;
                ARITH_RULE `MIN n n = n`] THEN
    REWRITE_TAC[GSYM DIMINDEX_12; NUM_OF_WORDLIST_EL] THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** The comparisons and packed table index computation ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (16--26) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  RULE_ASSUM_TAC(REWRITE_RULE [word_ugt; relational2; GT; WORD_AND_MASK;
   WORD_BLAST `word_and x ((word_subword:int16->num#num->int128) y (0,16)) =
               word_zx (word_and (word_zx x) y)`]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  ABBREV_TAC
   `valid j = (val ((x:num->int16) j) < 3329)` THEN
  POP_ASSUM(fun valid_def ->
   ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (27--32) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  SUBGOAL_THEN
   `read X12 s32 =
      (word_zx(word(bitval(valid 0) + 2 * bitval(valid 1) +
                    4 * bitval(valid 2) + 8 * bitval(valid 3) +
                    16 * bitval(valid 4) + 32 * bitval(valid 5) +
                    64 * bitval(valid 6) + 128 * bitval(valid 7)):byte)
       :int64) /\
    read X13 s32 =
      (word_zx(word(bitval(valid 8) + 2 * bitval(valid 9) +
                    4 * bitval(valid 10) + 8 * bitval(valid 11) +
                    16 * bitval(valid 12) + 32 * bitval(valid 13) +
                    64 * bitval(valid 14) + 128 * bitval(valid 15)):byte)
       :int64) /\
    read X14 s32 =
      (word_zx(word(bitval(valid 16) + 2 * bitval(valid 17) +
                    4 * bitval(valid 18) + 8 * bitval(valid 19) +
                    16 * bitval(valid 20) + 32 * bitval(valid 21) +
                    64 * bitval(valid 22) + 128 * bitval(valid 23)):byte)
       :int64) /\
    read X15 s32 =
      (word_zx(word(bitval(valid 24) + 2 * bitval(valid 25) +
                    4 * bitval(valid 26) + 8 * bitval(valid 27) +
                    16 * bitval(valid 28) + 32 * bitval(valid 29) +
                    64 * bitval(valid 30) + 128 * bitval(valid 31)):byte)
       :int64)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUBWORD_8_64] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN CONV_TAC BITBLAST_RULE;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read X12 s32 = x`; `read X13 s32 = x`;
      `read X14 s32 = x`; `read X15 s32 = x`] THEN
    STRIP_TAC] THEN

  (*** Abbreviate the table entries and perform the table loads ***)

  MAP_EVERY REABBREV_TAC
   [`idx0 = read X12 s32`;
    `idx1 = read X13 s32`;
    `idx2 = read X14 s32`;
    `idx3 = read X15 s32`] THEN

  MAP_EVERY ABBREV_TAC
   [`tab0 =
     read(memory :> bytes128(word_add table
         (word(16 * val(idx0:int64))))) s32`;
    `tab1 =
     read(memory :> bytes128(word_add table
         (word(16 * val(idx1:int64))))) s32`;
    `tab2 =
     read(memory :> bytes128(word_add table
         (word(16 * val(idx2:int64))))) s32`;
    `tab3 =
     read(memory :> bytes128(word_add table
         (word(16 * val(idx3:int64))))) s32`] THEN

  (*** Table loads, packed counts, and table selection ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (33--47) THEN

  (* Normalize shifted-register table addresses for event containment *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_shl (x:int64) 4 = word(16 * val x)`]) THEN

  (*** Repeating all the simplifications above ***)

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
  RULE_ASSUM_TAC(CONV_RULE
    (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  RULE_ASSUM_TAC(REWRITE_RULE
   [word_ugt; relational2; GT; WORD_AND_MASK;
   WORD_BLAST
    `word_and x
      ((word_subword:int16->num#num->int128) y (0,16)) =
     word_zx (word_and (word_zx x) y)`]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM valid_def])) THEN

  (*** The table-based selection, brute forced by case analysis ***)

  SUBGOAL_THEN
   `read Q16 s47 = word(num_of_wordlist (FILTER (\x. val x < 3329)
       [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
    read Q17 s47 = word(num_of_wordlist (FILTER (\x. val x < 3329)
       [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15])) /\
    read Q18 s47 = word(num_of_wordlist (FILTER (\x. val x < 3329)
       [x 16; x 17; x 18; x 19; x 20; x 21; x 22; x 23])) /\
    read Q19 s47 = word(num_of_wordlist (FILTER (\x. val x < 3329)
       [x 24; x 25; x 26; x 27; x 28; x 29; x 30; x 31]))`
  MP_TAC THENL
   [UNDISCH_TAC
     `read(memory :> bytes(table,4096)) s47 =
      num_of_wordlist mlkem_rej_uniform_table` THEN
    REPLICATE_TAC 4
     (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
           [GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[mlkem_rej_uniform_table; pair_wordlist] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q24 s = x`; `read Q25 s = x`;
      `read Q26 s = x`; `read Q27 s = x`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
      (fun th -> is_var(rhs(concl th)) &&
                 let n = fst(dest_var(rhs(concl th))) in
                 n = "tab0" || n = "tab1" ||
                 n = "tab2" || n = "tab3"))) THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read X12 s = x`; `read X13 s = x`;
      `read X14 s = x`; `read X15 s = x`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
      (fun th -> is_var(rhs(concl th)) &&
                 let n = fst(dest_var(rhs(concl th))) in
                 n = "idx0" || n = "idx1" ||
                 n = "idx2" || n = "idx3"))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`;
      `read Q18 s = x`; `read Q19 s = x`] THEN
    REPEAT CONJ_TAC THEN
    ASM_REWRITE_TAC[FILTER] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[bitval] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REPLICATE_TAC 3
      (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
    REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;

    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`;
      `read Q18 s = x`; `read Q19 s = x`] THEN
    STRIP_TAC] THEN

  (*** The counting part, similarly brute-forced ***)

  SUBGOAL_THEN
   `read X12 s47 =
      word(LENGTH (FILTER (\x. val x < 3329)
       [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
    read X13 s47 =
      word(LENGTH (FILTER (\x. val x < 3329)
       [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15])) /\
    read X14 s47 =
      word(LENGTH (FILTER (\x. val x < 3329)
       [x 16; x 17; x 18; x 19; x 20; x 21; x 22; x 23])) /\
    read X15 s47 =
      word(LENGTH (FILTER (\x. val x < 3329)
       [x 24; x 25; x 26; x 27; x 28; x 29; x 30; x 31]))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; BITBLAST_RULE
     `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
      word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
      word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
      word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
      word_popcount(word_and (word 16) x:byte) =
        bitval(bit 4 x) /\
      word_popcount(word_and (word 32) x:byte) =
        bitval(bit 5 x) /\
      word_popcount(word_and (word 64) x:byte) =
        bitval(bit 6 x) /\
      word_popcount(word_and (word 128) x:byte) =
        bitval(bit 7 x)`] THEN
    DISCARD_STATE_TAC "s47" THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[BIT_WORD_MASK; DIMINDEX_8; LENGTH_FILTER_EIGHT;
                GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC BITBLAST_RULE;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read X12 s = x`; `read X13 s = x`;
      `read X14 s = x`; `read X15 s = x`] THEN
    STRIP_TAC] THEN

  (*** Handle the overlapping writebacks ***)

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

  SUBGOAL_THEN
    `len0 <= 8 /\ len1 <= 8 /\ len2 <= 8 /\ len3 <= 8`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC
     ["len0"; "len1"; "len2"; "len3"] THEN
    MAP_EVERY EXPAND_TAC
     ["lis0"; "lis1"; "lis2"; "lis3"] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `curlen <= 224` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen"; "curlist"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** First writeback ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (48--49) THEN
  ABBREV_TAC `curlist1:int16 list = APPEND curlist lis0` THEN
  ABBREV_TAC `curlen1:num = curlen + len0` THEN

  SUBGOAL_THEN
   `curlen1 <= 232 /\
    read (memory :> bytes (res,2*curlen1)) s49 =
    num_of_wordlist(curlist1:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen1"; "curlist1"] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen <= 224`; `len0 <= 8`] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16;
                    ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_THEN
     `read (memory :> bytes128
        (word_add res (word (2 * curlen)))) s49 =
      word (num_of_wordlist(lis0:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len0 = MIN 16 (2 * len0)` SUBST1_TAC THENL
     [UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist1:int16 list) = curlen1`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist1"; "curlen1"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Second writeback ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (50--51) THEN
  ABBREV_TAC `curlist2:int16 list = APPEND curlist1 lis1` THEN
  ABBREV_TAC `curlen2:num = curlen1 + len1` THEN

  SUBGOAL_THEN
   `curlen2 <= 240 /\
    read (memory :> bytes (res,2*curlen2)) s51 =
    num_of_wordlist(curlist2:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen2"; "curlist2"] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen1 <= 232`; `len1 <= 8`] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16;
                    ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_THEN
     `read (memory :> bytes128
        (word_add res (word (2 * curlen1)))) s51 =
      word (num_of_wordlist(lis1:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len1 = MIN 16 (2 * len1)` SUBST1_TAC THENL
     [UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist2:int16 list) = curlen2`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist2"; "curlen2"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Third writeback ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (52--53) THEN
  ABBREV_TAC `curlist3:int16 list = APPEND curlist2 lis2` THEN
  ABBREV_TAC `curlen3:num = curlen2 + len2` THEN

  SUBGOAL_THEN
   `curlen3 <= 248 /\
    read (memory :> bytes (res,2*curlen3)) s53 =
    num_of_wordlist(curlist3:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen3"; "curlist3"] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen2 <= 240`; `len2 <= 8`] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16;
                    ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_THEN
     `read (memory :> bytes128
        (word_add res (word (2 * curlen2)))) s53 =
      word (num_of_wordlist(lis2:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len2 = MIN 16 (2 * len2)` SUBST1_TAC THENL
     [UNDISCH_TAC `len2 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len2 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist3:int16 list) = curlen3`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist3"; "curlen3"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Fourth and final writeback ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (54--55) THEN
  ABBREV_TAC `curlist4:int16 list = APPEND curlist3 lis3` THEN
  ABBREV_TAC `curlen4:num = curlen3 + len3` THEN

  SUBGOAL_THEN
   `curlen4 <= 256 /\
    read (memory :> bytes (res,2*curlen4)) s55 =
    num_of_wordlist(curlist4:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen4"; "curlist4"] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen3 <= 248`; `len3 <= 8`] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16;
                    ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_THEN
     `read (memory :> bytes128
        (word_add res (word (2 * curlen3)))) s55 =
      word (num_of_wordlist(lis3:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len3 = MIN 16 (2 * len3)` SUBST1_TAC THENL
     [UNDISCH_TAC `len3 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len3 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist4:int16 list) = curlen4`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist4"; "curlen4"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The end of the loop body ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (56--59) THEN

  (* Normalize store event addresses: word_shl from ADD Xn, Xn, Xm LSL #1 *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add a (word(2 * n))) (word_shl (word m) 1):int64 =
     word_add a (word(2 * (n + m)))`]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  REWRITE_TAC[ARITH_RULE `2 * 16 * (i+1) = 32*i+32 /\
                         32 * (i+1) = 32*i+32 /\
                         3 * 16 * (i+1) = 48*i+48`] THEN
  ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND;
                  ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `REJ_SAMPLE (SUB_LIST (32 * i,32) inlist) =
    APPEND (APPEND (APPEND lis0 lis1) lis2) lis3`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC
     ["lis0"; "lis1"; "lis2"; "lis3"] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; GSYM FILTER_APPEND] THEN
    REWRITE_TAC[APPEND; REJ_SAMPLE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[LENGTH_MAP] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN MATCH_MP_TAC(ARITH_RULE
       `32 * (i + 1) <= l ==> MIN 32 (l - 32 * i) = 32`) THEN
      MAP_EVERY UNDISCH_TAC
       [`48 * i + 48 <= buflen`;
        `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`] THEN
      ARITH_TAC;
      ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
    ASM_REWRITE_TAC[APPEND_ASSOC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "cur" THEN
  CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      CONJ_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `curlen3 + len3:num = curlen4`)) THEN
        SUBST1_TAC(SYM(ASSUME `curlen2 + len2:num = curlen3`)) THEN
        SUBST1_TAC(SYM(ASSUME `curlen1 + len1:num = curlen2`)) THEN
        SUBST1_TAC(SYM(ASSUME `curlen + len0:num = curlen1`)) THEN
        CONV_TAC WORD_RULE;
        (* Establish table index bounds for memory safety *)
        SUBGOAL_THEN `val(idx0:int64) < 256` ASSUME_TAC THENL
         [EXPAND_TAC "idx0" THEN
          ASM_REWRITE_TAC[VAL_WORD_ZX_8_64] THEN NO_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `val(idx1:int64) < 256` ASSUME_TAC THENL
         [EXPAND_TAC "idx1" THEN
          ASM_REWRITE_TAC[VAL_WORD_ZX_8_64] THEN NO_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `val(idx2:int64) < 256` ASSUME_TAC THENL
         [EXPAND_TAC "idx2" THEN
          ASM_REWRITE_TAC[VAL_WORD_ZX_8_64] THEN NO_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `val(idx3:int64) < 256` ASSUME_TAC THENL
         [EXPAND_TAC "idx3" THEN
          ASM_REWRITE_TAC[VAL_WORD_ZX_8_64] THEN NO_TAC;
          ALL_TAC] THEN
        DISCHARGE_MEMSAFE_ASM_TAC]]]);;

let MLKEM_REJ_UNIFORM_BLOCK16 = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e i.
     buflen < 2 EXP 64 /\ 8 * buflen = 12 * LENGTH inlist /\
     48 * i + 24 <= buflen /\
     LENGTH (REJ_SAMPLE (SUB_LIST (0,32 * i) inlist)) <= 240 /\
     ALL (nonoverlapping (res,512))
       [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,buflen); (table,4096)]
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x19c) /\ rej_uniform_vectors s /\
                rej_uniform_prefix res buf buflen table inlist e (16 * i) s)
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x220) /\ rej_uniform_vectors s /\
                rej_uniform_prefix res buf buflen table inlist e (16 * i + 8) s)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes (res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_MLKEM_REJ_UNIFORM_MC;
    rej_uniform_vectors; rej_uniform_prefix; rej_uniform_state] THEN STRIP_TAC THEN
  ABBREV_TAC `cur:int64 = word_add buf (word (48 * i))` THEN
  ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,32 * i) inlist)` THEN
  ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * 16 * n = 32 * n /\ 3 * 16 * n = 48 * n`] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `curlen <= 240` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen"; "curlist"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = read (memory :> bytes64 cur) s0`;
    `q1 = read (memory :> bytes64 (word_add cur (word 8))) s0`;
    `q2 = read (memory :> bytes64 (word_add cur (word 16))) s0`] THEN

  (*** Abbreviate the next 16 digits as 16-bit words ***)

  ABBREV_TAC
   `(x:num->int16) j =
    word_zx(word_subword (read (memory :> wbytes cur) s0:192 word)
                               (12 * j,12):12 word)` THEN

  (*** The byte-lane loads and TBL de-interleaving ***)

  SUBGOAL_THEN
   `read (memory :> bytes128 cur) s0 = word_join (q1:int64) (q0:int64)`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV(READ_MEMORY_MERGE_CONV 1)) THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--9) THEN
  RULE_ASSUM_TAC(CONV_RULE
    (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

  SUBGOAL_THEN
   `read Q16 s9 =
        word_join (word_join (word_join (x 7) (x 6):int32)
                             (word_join (x 5) (x 4):int32):int64)
                  (word_join (word_join (x 3) (x 2):int32)
                             (word_join (x 1) (x 0:int16):int32):int64) /\
    read Q17 s9 =
        word_join (word_join (word_join (x 15) (x 14):int32)
                             (word_join (x 13) (x 12):int32):int64)
                  (word_join (word_join (x 11) (x 10):int32)
                             (word_join (x 9) (x 8:int16):int32):int64)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[READ_MEMORY_TRIPLES_SPLIT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_BLAST;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`] THEN
    STRIP_TAC] THEN

  (**** Later in the proof, we actually want this equivalent ***)

  SUBGOAL_THEN
   `!j. j < 16
        ==> (word_zx:12 word->int16)
            (EL j (SUB_LIST(32 * i,16) inlist)) = x j`
  ASSUME_TAC THENL
   [UNDISCH_THEN
     `read (memory :> bytes (buf,buflen)) s9 =
      num_of_wordlist(inlist:(12 word)list)`
     (MP_TAC o AP_TERM
       `\x. x DIV 2 EXP (8 * 48 * i) MOD 2 EXP (8 * 24)`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
    REWRITE_TAC[READ_BYTES_MOD] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[ARITH_RULE `8 * 24 = 12 * 16 * 1`] THEN
    REWRITE_TAC[ARITH_RULE `8 * 48 * x = 12 * 32 * x`] THEN
    REWRITE_TAC[GSYM DIMINDEX_12;
                GSYM NUM_OF_WORDLIST_SUB_LIST] THEN
    SUBGOAL_THEN
     `MIN (buflen - 48 * i) 24 = dimindex(:192) DIV 8`
    SUBST1_TAC THENL
     [REWRITE_TAC[DIMINDEX_192] THEN
      UNDISCH_TAC `48 * i + 24 <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM VAL_READ_WBYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES;
                      GSYM READ_COMPONENT_COMPOSE]] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[word_zx; VAL_WORD_SUBWORD] THEN
    REWRITE_TAC[MULT_CLAUSES; DIMINDEX_12;
                ARITH_RULE `MIN n n = n`] THEN
    REWRITE_TAC[GSYM DIMINDEX_12; NUM_OF_WORDLIST_EL] THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN

  (*** The comparisons and table index computation ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (10--17) THEN
  RULE_ASSUM_TAC(CONV_RULE
    (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
  RULE_ASSUM_TAC(CONV_RULE
    (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  RULE_ASSUM_TAC(REWRITE_RULE
   [word_ugt; relational2; GT; WORD_AND_MASK;
   WORD_BLAST
    `word_and x
      ((word_subword:int16->num#num->int128) y (0,16)) =
     word_zx (word_and (word_zx x) y)`]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  (*** Abbreviate the table entries and perform the table loads ***)

  MAP_EVERY REABBREV_TAC
   [`idx0 = read X12 s17`; `idx1 = read X13 s17`] THEN

  MAP_EVERY ABBREV_TAC
   [`tab0 =
     read(memory :> bytes128(word_add table
         (word(16 * val(idx0:int64))))) s17`;
    `tab1 =
     read(memory :> bytes128(word_add table
         (word(16 * val(idx1:int64))))) s17`] THEN

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (18--25) THEN

  (* Normalize shifted-register table addresses for event containment *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_shl (x:int64) 4 = word(16 * val x)`]) THEN

  (*** Repeating all the simplifications above ***)

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
  RULE_ASSUM_TAC(CONV_RULE
    (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  RULE_ASSUM_TAC(REWRITE_RULE
   [word_ugt; relational2; GT; WORD_AND_MASK;
   WORD_BLAST
    `word_and x
      ((word_subword:int16->num#num->int128) y (0,16)) =
     word_zx (word_and (word_zx x) y)`]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  (*** The actual tbl instructions ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (26--27) THEN

  (*** The table-based selection, brute forced by case analysis ***)

  SUBGOAL_THEN
   `read Q16 s27 = word(num_of_wordlist (FILTER (\x. val x < 3329)
       [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
    read Q17 s27 = word(num_of_wordlist (FILTER (\x. val x < 3329)
       [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15]))`
  MP_TAC THENL
   [UNDISCH_TAC
     `read(memory :> bytes(table,4096)) s27 =
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
    MAP_EVERY EXPAND_TAC
     ["tab0"; "idx0"; "tab1"; "idx1"] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[FILTER] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REPLICATE_TAC 3
      (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
    REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`] THEN
    STRIP_TAC] THEN

  (*** The counting part, similarly brute-forced ***)

  SUBGOAL_THEN
   `read X12 s27 =
      word(LENGTH (FILTER (\x. val x < 3329)
       [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])) /\
    read X13 s27 =
      word(LENGTH (FILTER (\x. val x < 3329)
       [x 8; x 9; x 10; x 11; x 12; x 13; x 14; x 15]))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; BITBLAST_RULE
     `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
      word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
      word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
      word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
      word_popcount(word_and (word 16) x:byte) =
        bitval(bit 4 x) /\
      word_popcount(word_and (word 32) x:byte) =
        bitval(bit 5 x) /\
      word_popcount(word_and (word 64) x:byte) =
        bitval(bit 6 x) /\
      word_popcount(word_and (word 128) x:byte) =
        bitval(bit 7 x)`] THEN
    DISCARD_STATE_TAC "s27" THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[WORD_MASK_ALT] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[FILTER] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[LENGTH] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    DISCARD_MATCHING_ASSUMPTIONS
     [`read X12 s = x`; `read X13 s = x`] THEN
    STRIP_TAC] THEN

  (*** Handle the overlapping writebacks ***)

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

  (*** First writeback (tail) ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (28--29) THEN
  ABBREV_TAC `curlist1:int16 list = APPEND curlist lis0` THEN
  ABBREV_TAC `curlen1:num = curlen + len0` THEN

  SUBGOAL_THEN
   `curlen1 <= 248 /\
    read (memory :> bytes (res,2*curlen1)) s29 =
    num_of_wordlist(curlist1:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen1"; "curlist1"] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen <= 240`; `len0 <= 8`] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16;
                    ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_THEN
     `read (memory :> bytes128
        (word_add res (word (2 * curlen)))) s29 =
      word (num_of_wordlist(lis0:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len0 = MIN 16 (2 * len0)` SUBST1_TAC THENL
     [UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len0 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist1:int16 list) = curlen1`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist1"; "curlen1"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Second writeback (tail) ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (30--31) THEN
  ABBREV_TAC `curlist2:int16 list = APPEND curlist1 lis1` THEN
  ABBREV_TAC `curlen2:num = curlen1 + len1` THEN

  SUBGOAL_THEN
   `curlen2 <= 256 /\
    read (memory :> bytes (res,2*curlen2)) s31 =
    num_of_wordlist(curlist2:int16 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen2"; "curlist2"] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen1 <= 248`; `len1 <= 8`] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16;
                    ARITH_RULE `8 * 2 * l = 16 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_THEN
     `read (memory :> bytes128
        (word_add res (word (2 * curlen1)))) s31 =
      word (num_of_wordlist(lis1:int16 list))`
     (MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `2 * len1 = MIN 16 (2 * len1)` SUBST1_TAC THENL
     [UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_16] THEN
    UNDISCH_TAC `len1 <= 8` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (2 * l0)))
                           (word_shl (word l1) 1) =
                  word_add a (word(2 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist2:int16 list) = curlen2`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist2"; "curlen2"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The end of the tail computation ***)

  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (32--33) THEN

  (* Normalize store event addresses: word_shl from ADD Xn, Xn, Xm LSL #1 *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add a (word(2 * n))) (word_shl (word m) 1):int64 =
     word_add a (word(2 * (n + m)))`]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * (16*i+8) = 32*i+16 /\ 3 * (16*i+8) = 48*i+24`] THEN
  ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND;
                  ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `REJ_SAMPLE (SUB_LIST (32 * i,16) inlist) =
    APPEND lis0 lis1`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lis0"; "lis1"] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; GSYM FILTER_APPEND] THEN
    REWRITE_TAC[APPEND; REJ_SAMPLE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[LENGTH_MAP] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN MAP_EVERY UNDISCH_TAC
       [`48 * i + 24 <= buflen`;
        `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`] THEN
      ARITH_TAC;
      ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
    ASM_REWRITE_TAC[APPEND_ASSOC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "cur" THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `curlen1 + len1:num = curlen2`)) THEN
    SUBST1_TAC(SYM(ASSUME `curlen + len0:num = curlen1`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* Establish table index bounds for memory safety *)
  SUBGOAL_THEN `val(idx0:int64) < 256` ASSUME_TAC THENL
   [EXPAND_TAC "idx0" THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_CONDENSE_CONV)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(idx1:int64) < 256` ASSUME_TAC THENL
   [EXPAND_TAC "idx1" THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_CONDENSE_CONV)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCHARGE_MEMSAFE_ASM_TAC THEN
  TRY(DISJ1_TAC THEN EXPAND_TAC "cur" THEN CONTAINED_TAC));;

(* The main loop exits at the first block with insufficient input or output. *)
let MLKEM_REJ_UNIFORM_LOOP = prove
 (`!res buf buflen table (inlist:(12 word)list) e pc N.
    buflen < 2 EXP 64 /\ 8 * buflen = 12 * LENGTH inlist /\
    ALL (nonoverlapping (res,512))
      [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,buflen); (table,4096)] /\
    48 * N <= buflen /\ LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * N) inlist)) <= 256 /\
    ~(48 * N + 48 <= buflen /\
       LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * N) inlist)) <= 224) /\
    (!i. i < N ==> 48 * i + 48 <= buflen /\
       LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * i) inlist)) <= 224)
    ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word(pc + 0x88) /\ rej_uniform_vectors s /\
            rej_uniform_prefix res buf buflen table inlist e 0 s)
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word(pc + 0x18c) /\ rej_uniform_vectors s /\
            rej_uniform_prefix res buf buflen table inlist e (16 * N) s)
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,512)])`,
  let normalize = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL] in
  let test i first take =
    SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
           `inlist:(12 word)list`; `e:uarch_event list`; i; `pc:num`; first; take]
      MLKEM_REJ_UNIFORM_TEST32 |>
    CONV_RULE(TOP_DEPTH_CONV let_CONV) |>
    REWRITE_RULE[COND_CLAUSES; MULT_CLAUSES] |> normalize in
  REPEAT GEN_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    ALL] THEN STRIP_TAC THEN ASM_CASES_TAC `N = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN MATCH_MP_TAC(test `0` `T` `F`) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0];
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N:num` `pc + 0x98` `pc + 0x184`
   `\i s. rej_uniform_vectors s /\
          rej_uniform_prefix res buf buflen table inlist e (16 * i) s` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_SIMP_TAC[LT_NZ; MULT_CLAUSES] THEN
    STRIP_TAC THEN MATCH_MP_TAC(test `0` `T` `T`) THEN
    ASM_REWRITE_TAC[LE_0] THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(normalize MLKEM_REJ_UNIFORM_BLOCK32) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(test `i:num` `F` `T`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(test `N:num` `F` `F`) THEN ASM_REWRITE_TAC[]]);;

let REJ_UNIFORM_READ_HALFWORD = prove
 (`!buf len d s. d+2 <= len
    ==> val(read (memory :> bytes16 (word_add buf (word d))) s) =
        (read (memory :> bytes(buf,len)) s DIV 2 EXP (8*d)) MOD 2 EXP (8*2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
    DIMINDEX_16; ARITH_RULE `16 DIV 8 = 2`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `d+2 <= len ==> MIN (len-d) 2 = 2`]);;

(* Combine the three byte loads into the two 12-bit candidates. *)
let REJ_UNIFORM_READ_PAIR = prove
 (`!(l:(12 word)list) (buf:int64) s n len.
      3 * n + 3 <= len /\ 8 * len = 12 * LENGTH l /\
      read (memory :> bytes(buf,len)) s = num_of_wordlist l
      ==> let p = word_add buf (word (3*n)) in
          let b0 = read (memory :> bytes8 p) s in
          let b1 = read (memory :> bytes8 (word_add p (word 1))) s in
          let b2 = read (memory :> bytes8 (word_add p (word 2))) s in
          word_insert (word_zx b0:int32) (8,4) (word_zx b1:int32):int32 =
            word_zx (EL (2*n) l) /\
          word_or (word_ushr (word_zx b1) 4)
                  (word_shl (word_zx b2) 4):int32 = word_zx (EL (2*n+1) l)`,
  let subword_value =
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_12;
      ARITH_RULE `MIN 12 12 = 12`; EXP; DIV_1] in
  let wordlist_el = REWRITE_RULE[DIMINDEX_12]
    (INST_TYPE [`:12`,`:N`] NUM_OF_WORDLIST_EL) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `3*n+2 <= len /\ (3*n+1)+2 <= len /\
                2*n < LENGTH(l:(12 word)list) /\
                2*n+1 < LENGTH(l:(12 word)list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `p:int64 = word_add buf (word (3*n))` THEN
  SUBGOAL_THEN
   `read (memory :> bytes16 p) s =
      word_join (read (memory :> bytes8 (word_add p (word 1))) s)
                (read (memory :> bytes8 p) s) /\
    read (memory :> bytes16 (word_add p (word 1))) s =
      word_join (read (memory :> bytes8 (word_add p (word 2))) s)
                (read (memory :> bytes8 (word_add p (word 1))) s)`
  (fun th -> REWRITE_TAC[WORD_BLAST
    `word_insert (word_zx (a:8 word):int32) (8,4)
                 (word_zx (b:8 word):int32):int32 =
     word_and (word_zx (word_join b a:int16)) (word 4095)`;
    WORD_BLAST
    `word_or (word_ushr (word_zx (b:8 word)) 4)
             (word_shl (word_zx (c:8 word)) 4):int32 =
     word_ushr (word_zx (word_join c b:int16)) 4`;
    GSYM (CONJUNCT1 th); GSYM (CONJUNCT2 th)]) THENL
   [REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV;
    EXPAND_TAC "p" THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_BLAST
      `word_and (word_zx (w:int16)) (word 4095):int32 =
       word_zx (word_subword w (0,12):12 word)`] THEN
    subword_value THEN
    ASM_SIMP_TAC[REJ_UNIFORM_READ_HALFWORD; ARITH_RULE `8 * 2 = 16`] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `MIN 16 12 = 12`;
                ARITH_RULE `8*(3*n) = 12*(2*n)`] THEN
    ASM_SIMP_TAC[wordlist_el];
    REWRITE_TAC[WORD_BLAST
      `word_ushr (word_zx (w:int16)) 4:int32 =
       word_zx (word_subword w (4,12):12 word)`] THEN
    subword_value THEN
    ASM_SIMP_TAC[REJ_UNIFORM_READ_HALFWORD; ARITH_RULE `8 * 2 = 16`] THEN
    GEN_REWRITE_TAC LAND_CONV [DIV_MOD] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 4 * 2 EXP 12 = 2 EXP 16`;
      MOD_MOD_REFL] THEN
    REWRITE_TAC[GSYM (REWRITE_RULE[ARITH_RULE `2 EXP 4 * 2 EXP 12 = 2 EXP 16`]
      (SPECL [`m:num`; `2 EXP 4`; `2 EXP 12`] DIV_MOD)); DIV_DIV; GSYM EXP_ADD;
      ARITH_RULE `8*(3*n+1)+4 = 12*(2*n+1)`] THEN
    ASM_SIMP_TAC[wordlist_el]]);;

let REJ_UNIFORM_NEXT_PAIR = prove
 (`!(l:(12 word)list) n. 2*n+2 <= LENGTH l
    ==> REJ_SAMPLE (SUB_LIST (0,2*(n+1)) l) =
        APPEND (REJ_SAMPLE (SUB_LIST (0,2*n) l))
          (FILTER (\x:int16. val x < 3329)
            [word_zx (EL (2*n) l); word_zx (EL (2*n+1) l)])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `2*(n+1) = 2*n+2`] THEN
  ONCE_REWRITE_TAC[SUB_LIST_SPLIT] THEN REWRITE_TAC[ADD_CLAUSES;
    REJ_SAMPLE_APPEND] THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONV_RULE NUM_REDUCE_CONV
    (ISPECL [`l:(12 word)list`; `1`; `1`; `2*n`] SUB_LIST_SPLIT)] THEN
  SUBGOAL_THEN `2*n < LENGTH(l:(12 word)list) /\
                2*n+1 < LENGTH(l:(12 word)list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[SUB_LIST_1; APPEND; REJ_SAMPLE; MAP]]);;

let REJ_UNIFORM_SCALAR_FINISHED = prove
 (`!(l:(12 word)list) n.
    2*n <= LENGTH l /\
    (2*n = LENGTH l \/
     LENGTH (SUB_LIST(0,256) (REJ_SAMPLE(SUB_LIST(0,2*n) l))) = 256)
    ==> SUB_LIST(0,256) (REJ_SAMPLE l) =
        SUB_LIST(0,256) (REJ_SAMPLE(SUB_LIST(0,2*n) l))`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[SUB_LIST_REFL; LE_REFL];
    MP_TAC(ISPECL [`l:(12 word)list`; `2*n`] SUB_LIST_TOPSPLIT) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
      [SYM th]) THEN REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
    MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN
    MP_TAC(ASSUME
      `LENGTH(SUB_LIST(0,256) (REJ_SAMPLE(SUB_LIST(0,2*n) l))) = 256`) THEN
    REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ARITH_TAC]);;

let REJ_UNIFORM_SCALAR_BOUND = prove
 (`!(l:(12 word)list) n.
    LENGTH(SUB_LIST(0,256) (REJ_SAMPLE(SUB_LIST(0,2*n) l))) <= 256`,
  REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

let REJ_UNIFORM_TO_SCALAR_PREFIX = prove
 (`!res buf buflen table (inlist:(12 word)list) e n s.
    LENGTH(REJ_SAMPLE(SUB_LIST(0,2*n) inlist)) <= 256 /\
    rej_uniform_prefix res buf buflen table inlist e n s
    ==> rej_uniform_scalar_prefix res buf buflen table inlist e n s`,
  SIMP_TAC[rej_uniform_prefix; rej_uniform_scalar_prefix; SUB_LIST_REFL]);;

(* At the scalar loop head, a full polynomial or an empty input stops sampling. *)
let MLKEM_REJ_UNIFORM_SCALAR_DONE = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e n.
     buflen < 2 EXP 64 /\ 8 * buflen = 12 * LENGTH inlist /\
     2*n <= LENGTH inlist /\
     (2*n = LENGTH inlist \/
      LENGTH(SUB_LIST(0,256) (REJ_SAMPLE(SUB_LIST(0,2*n) inlist))) = 256) /\
     nonoverlapping (res,512) (word pc,LENGTH mlkem_rej_uniform_mc)
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x220) /\
                rej_uniform_scalar_prefix res buf buflen table inlist e n s)
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x278) /\
                rej_uniform_scalar_prefix res buf buflen table inlist e n s)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes (res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rej_uniform_scalar_prefix; rej_uniform_state;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_MLKEM_REJ_UNIFORM_MC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`inlist:(12 word)list`; `n:num`] REJ_UNIFORM_SCALAR_BOUND) THEN
  ABBREV_TAC `k = LENGTH(SUB_LIST(0,256)
    (REJ_SAMPLE(SUB_LIST(0,2*n) (inlist:(12 word)list))))` THEN DISCH_TAC THEN
  VAL_INT64_TAC `k:num` THEN
  ASM_CASES_TAC `k = 256` THENL
   [ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--2);
    SUBGOAL_THEN `~(256 <= k)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_sub (word buflen) (word(3*n)):int64 = word 0`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `buflen = 3 * n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[WORD_SUB_REFL]]; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--3)] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCHARGE_MEMSAFE_ASM_TAC);;
(* A full prefix suppresses the second store if the first sample filled it. *)
let REJ_UNIFORM_PAIR_CAP = prove
 (`!l (a:int16) b. LENGTH l < 256
    ==> SUB_LIST(0,256) (APPEND l (FILTER (\x. val x < 3329) [a;b])) =
        let m = if val a < 3329 then APPEND l [a] else l in
        if LENGTH m < 256 /\ val b < 3329 then APPEND m [b] else m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(l:int16 list) <= 256 /\ SUC (LENGTH l) <= 256`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FILTER; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `val(a:int16) < 3329` THEN
  ASM_CASES_TAC `val(b:int16) < 3329` THEN ASM_REWRITE_TAC[APPEND; APPEND_NIL;
    LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[SUB_LIST_REFL; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
  SUBGOAL_THEN `APPEND l [a:int16;b] = APPEND (APPEND l [a]) [b]`
    SUBST1_TAC THENL [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  ASM_CASES_TAC `SUC (LENGTH(l:int16 list)) < 256` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUB_LIST_REFL THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `256 <= LENGTH(APPEND l [a:int16])` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT] THEN MATCH_MP_TAC SUB_LIST_REFL THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC]]);;

let REJ_UNIFORM_APPEND_SAMPLE = prove
 (`!res s out a.
     read (memory :> bytes(res,2 * LENGTH out)) s = num_of_wordlist out /\
     read (memory :> bytes16 (word_add res (word(2 * LENGTH out)))) s = a
     ==> read (memory :> bytes(res,2 * LENGTH(APPEND out [a:int16]))) s =
         num_of_wordlist(APPEND out [a])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; LEFT_ADD_DISTRIB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
  ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * k = 16*k`; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[NUM_OF_WORDLIST_SING] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int16->num`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES16_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_16; ARITH_RULE `16 DIV 8 = 2`]);;

let MLKEM_REJ_UNIFORM_SCALAR_STEP = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e n.
     buflen < 2 EXP 64 /\ 8 * buflen = 12 * LENGTH inlist /\
     3*n+3 <= buflen /\
     LENGTH (SUB_LIST(0,256) (REJ_SAMPLE (SUB_LIST (0,2*n) inlist))) < 256 /\
     ALL (nonoverlapping (res,512))
       [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,buflen); (table,4096)]
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x220) /\
                rej_uniform_scalar_prefix res buf buflen table inlist e n s)
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x220) /\
                rej_uniform_scalar_prefix res buf buflen table inlist e (n+1) s)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes (res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_MLKEM_REJ_UNIFORM_MC;
    rej_uniform_scalar_prefix; rej_uniform_state] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ABBREV_TAC `out = REJ_SAMPLE(SUB_LIST(0,2*n) (inlist:(12 word)list))` THEN
  ABBREV_TAC `k = LENGTH (out:int16 list)` THEN
  SUBGOAL_THEN `k < 256` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(SUB_LIST(0,256) (out:int16 list)) < 256` THEN
    ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `SUB_LIST(0,256) (out:int16 list) = out` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a:int16 = word_zx (EL (2*n) (inlist:(12 word)list))` THEN
  ABBREV_TAC `b:int16 = word_zx (EL (2*n+1) (inlist:(12 word)list))` THEN
  SUBGOAL_THEN `2*n+2 <= LENGTH(inlist:(12 word)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`inlist:(12 word)list`; `n:num`] REJ_UNIFORM_NEXT_PAIR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`out:int16 list`; `a:int16`; `b:int16`] REJ_UNIFORM_PAIR_CAP) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  VAL_INT64_TAC `k:num` THEN VAL_INT64_TAC `k + 1` THEN
  VAL_INT64_TAC `buflen:num` THEN VAL_INT64_TAC `3*n` THEN
  SUBGOAL_THEN `~(256 <= k) /\ 2*k+2 <= 512 /\
                ~(val(word_sub (word buflen) (word(3*n)):int64) = 0)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ABBREV_TAC `p:int64 = word_add buf (word (3*n))` THEN
  ABBREV_TAC `b0:8 word = read (memory :> bytes8 p) s0` THEN
  ABBREV_TAC `b1:8 word = read (memory :> bytes8 (word_add p (word 1))) s0` THEN
  ABBREV_TAC `b2:8 word = read (memory :> bytes8 (word_add p (word 2))) s0` THEN
  SUBGOAL_THEN
   `word_insert (word_zx (b0:8 word):int32) (8,4)
                (word_zx (b1:8 word):int32):int32 =
      word_zx (a:int16) /\
    word_or (word_ushr (word_zx (b1:8 word)) 4)
            (word_shl (word_zx (b2:8 word)) 4):int32 = word_zx (b:int16)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["b0"; "b1"; "b2"; "p"; "a"; "b"] THEN
    MP_TAC(SPECL [`inlist:(12 word)list`; `buf:int64`; `s0:armstate`; `n:num`;
      `buflen:num`] REJ_UNIFORM_READ_PAIR) THEN
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; WORD_BLAST
      `word_zx (word_zx (w:12 word):int16):int32 = word_zx w`];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--11) THEN
  SUBGOAL_THEN `read X5 s11 = word_zx (a:int16) /\
                read X6 s11 = word_zx (b:int16)` MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_BLAST
      `word_zx (word_zx (w:int32):int64):int32 = w`;
      WORD_BLAST `word_zx(word_zx (w:int16):int32):int64 = word_zx w`];
    DISCARD_MATCHING_ASSUMPTIONS [`read X5 s = x`; `read X6 s = x`] THEN
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `(val(a:int16) MOD 2 EXP 64) MOD 4294967296 = val a /\
    (val(b:int16) MOD 2 EXP 64) MOD 4294967296 = val b`
  STRIP_ASSUME_TAC THENL
   [(let th = prove
     (`!w:int16. (val w MOD 2 EXP 64) MOD 4294967296 = val w`,
      GEN_TAC THEN MP_TAC(ISPEC `w:int16` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_16] THEN SIMP_TAC[ARITH_RULE
        `v < 2 EXP 16 ==> v < 2 EXP 64 /\ v < 4294967296`; MOD_LT]) in
    REWRITE_TAC[th]);
    ALL_TAC] THEN
  let cmp_tac = RULE_ASSUM_TAC(SIMP_RULE[WORD_BLAST
      `word_zx(word_zx (x:int16):int64):int32 = word_zx x`;
      CONV_RULE WORD_REDUCE_CONV
      (ISPECL [`x:int32`; `word 3329:int32`] NOCARRY_WORD_SUB);
      VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_16; DIMINDEX_64; MOD_LT;
      ASSUME `(val(a:int16) MOD 2 EXP 64) MOD 4294967296 = val a`;
      ASSUME `(val(b:int16) MOD 2 EXP 64) MOD 4294967296 = val b`]) in
  let branch_tac step test =
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [step] THEN cmp_tac THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME test]) in
  let append_length_test = prove
   (`!l (x:int16). LENGTH(APPEND l [x]) < 256 <=> LENGTH l + 1 < 256`,
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH]) in
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [12] THEN cmp_tac THEN
  ASM_CASES_TAC `val(a:int16) < 3329` THENL
   [SUBGOAL_THEN `~(3329 <= val(a:int16))` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
    branch_tac 13 `~(3329 <= val(a:int16))` THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (14--16) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
    ASM_CASES_TAC `k+1 < 256` THENL
     [SUBGOAL_THEN `~(256 <= k+1) /\ 2*(k+1)+2 <= 512` STRIP_ASSUME_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (17--18) THEN cmp_tac THEN
      ASM_CASES_TAC `val(b:int16) < 3329` THENL
       [SUBGOAL_THEN `~(3329 <= val(b:int16))` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
        branch_tac 19 `~(3329 <= val(b:int16))` THEN
        ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (20--22);
        SUBGOAL_THEN `3329 <= val(b:int16)` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN branch_tac 19 `3329 <= val(b:int16)`];
      SUBGOAL_THEN `256 <= k+1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [17]];
    SUBGOAL_THEN `3329 <= val(a:int16)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    branch_tac 13 `3329 <= val(a:int16)` THEN
    ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [14] THEN cmp_tac THEN
    ASM_CASES_TAC `val(b:int16) < 3329` THENL
     [SUBGOAL_THEN `~(3329 <= val(b:int16))` ASSUME_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN branch_tac 15 `~(3329 <= val(b:int16))` THEN
      ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (16--18);
      SUBGOAL_THEN `3329 <= val(b:int16)` ASSUME_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN branch_tac 15 `3329 <= val(b:int16)`]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add a (word(2 * k))) (word 2):int64 =
     word_add a (word(2 * (k + 1)))`;
    SYM(ASSUME `word_add buf (word (3*n)):int64 = p`);
    GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[append_length_test] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
    ARITH_RULE `3 * (n+1) = 3*n+3 /\ 2*(n+1) = 2*n+2`;
    WORD_RULE `word_sub (word_sub x (word n)) (word k) = word_sub x (word(n+k))`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN CONV_TAC WORD_RULE; ALL_TAC]) THEN
  TRY(CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REJ_UNIFORM_APPEND_SAMPLE THEN CONJ_TAC THENL
      [ALL_TAC; ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH;
        ARITH_RULE `SUC 0 = 1`; ARITH_RULE `2*(k+1) = 2*k+2`] THEN
        CONV_TAC WORD_BLAST]) THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    ALL_TAC]) THEN
  DISCHARGE_MEMSAFE_ASM_TAC);;
let MLKEM_REJ_UNIFORM_SCALAR = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e n.
     buflen < 2 EXP 64 /\ 3 divides buflen /\
     8 * buflen = 12 * LENGTH inlist /\
     ALL (nonoverlapping (res,512))
       [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,buflen); (table,4096)] /\
     2*n <= LENGTH inlist
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x220) /\
                rej_uniform_scalar_prefix res buf buflen table inlist e n s)
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read PC s = word (pc + 0x278) /\
                ?k. 2*k <= LENGTH inlist /\
                    (2*k = LENGTH inlist \/
                     LENGTH(SUB_LIST(0,256)
                       (REJ_SAMPLE(SUB_LIST(0,2*k) inlist))) = 256) /\
                    rej_uniform_scalar_prefix res buf buflen table inlist e k s)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes (res,512)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `LENGTH(inlist:(12 word)list) - 2*n` THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `2*n = LENGTH(inlist:(12 word)list) \/
    LENGTH(SUB_LIST(0,256) (REJ_SAMPLE(SUB_LIST(0,2*n) inlist))) = 256` THENL
   [ENSURES_POSTCONDITION_TAC
      `\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
           read PC s = word (pc+0x278) /\
           rej_uniform_scalar_prefix res buf buflen table inlist e n s` THEN
    CONJ_TAC THENL
     [BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
        MLKEM_REJ_UNIFORM_SCALAR_DONE) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ALL]];
    ALL_TAC] THEN
  MP_TAC(ASSUME `3 divides buflen`) THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `pairs:num`) THEN
  SUBGOAL_THEN `LENGTH(inlist:(12 word)list) = 2*pairs` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n < pairs` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `3*n+3 <= buflen /\ 2*(n+1) <= LENGTH(inlist:(12 word)list)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc+0x220`
    `\s. rej_uniform_scalar_prefix res buf buflen table inlist e (n+1) s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
      MLKEM_REJ_UNIFORM_SCALAR_STEP) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`inlist:(12 word)list`; `n:num`] REJ_UNIFORM_SCALAR_BOUND) THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC(REWRITE_RULE[IMP_IMP]
      (SPECL [`inlist:(12 word)list`; `n+1`] th))) THEN REPEAT CONJ_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let MLKEM_REJ_UNIFORM_FINAL = prove
 (`!res buf buflen table (inlist:(12 word)list) e pc.
    nonoverlapping (res,512) (word pc,LENGTH mlkem_rej_uniform_mc)
    ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word(pc + 0x278) /\
            ?k. 2*k <= LENGTH inlist /\
                (2*k = LENGTH inlist \/
                 LENGTH(SUB_LIST(0,256)
                   (REJ_SAMPLE(SUB_LIST(0,2*k) inlist))) = 256) /\
                rej_uniform_scalar_prefix res buf buflen table inlist e k s)
       (\s. read PC s = word(pc + 0x27c) /\
            let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
            C_RETURN s = word(LENGTH outlist) /\
            read (memory :> bytes(res,2 * LENGTH outlist)) s =
              num_of_wordlist outlist /\
            ?e2. read events s = APPEND e2 e /\
                 memaccess_inbounds e2 [buf,buflen;table,4096] [res,512])
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    LENGTH_MLKEM_REJ_UNIFORM_MC; C_RETURN; rej_uniform_scalar_prefix; rej_uniform_state] THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(SPECL [`inlist:(12 word)list`; `k:num`] REJ_UNIFORM_SCALAR_FINISHED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ARM_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let MLKEM_REJ_UNIFORM_CORRECT_MEMSAFE = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e.
    24 divides val buflen /\ 8 * val buflen = 12 * LENGTH inlist /\
    ALL (nonoverlapping (res,512))
      [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,val buflen); (table,4096)]
    ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word pc /\ C_ARGUMENTS [res;buf;buflen;table] s /\
            read (memory :> bytes(table,4096)) s = num_of_wordlist mlkem_rej_uniform_table /\
            read (memory :> bytes(buf,val buflen)) s = num_of_wordlist inlist /\
            read events s = e)
       (\s. read PC s = word(pc + 0x27c) /\
            let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
            C_RETURN s = word(LENGTH outlist) /\
            read (memory :> bytes(res,2 * LENGTH outlist)) s =
              num_of_wordlist outlist /\
            ?e2. read events s = APPEND e2 e /\
                 memaccess_inbounds e2 [buf,val buflen;table,4096] [res,512])
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,512)])`,
  let normalize = REWRITE_RULE[ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] in
  let state pc n =
    let p = vsubst[n,`n:num`]
     `\s. rej_uniform_vectors s /\ rej_uniform_prefix res buf buflen table inlist e n s` in
    ENSURES_SEQUENCE_TAC pc p in
  let scalar n =
    let p = vsubst[n,`n:num`]
      `\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
           read PC s = word(pc + 0x220) /\
           rej_uniform_scalar_prefix res buf buflen table inlist e n s` in
    let th = SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                     `inlist:(12 word)list`; `pc:num`; `e:uarch_event list`; n]
                    (normalize MLKEM_REJ_UNIFORM_SCALAR) in
    ENSURES_PRECONDITION_TAC p THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REJ_UNIFORM_TO_SCALAR_PREFIX; ARITH_RULE
          `2 * (16*n+8) = 32*n+16 /\ 2 * 16*n = 32*n`] THEN
      ASM_MESON_TAC[REJ_UNIFORM_TO_SCALAR_PREFIX];
      MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] in
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC [`table:int64`; `inlist:(12 word)list`; `pc:num`;
                       `e:uarch_event list`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `3 divides buflen` ASSUME_TAC THENL
   [MP_TAC(ASSUME `24 divides buflen`) THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN EXISTS_TAC `8*d` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  state `pc + 0x88` `0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(normalize MLKEM_REJ_UNIFORM_INIT) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`buflen:num`; `inlist:(12 word)list`] REJ_UNIFORM_BLOCK_COUNT) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  state `pc + 0x18c` `16 * N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(normalize MLKEM_REJ_UNIFORM_LOOP) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x278`
   `\s. ?k. 2*k <= LENGTH inlist /\
            (2*k = LENGTH inlist \/
             LENGTH(SUB_LIST(0,256)
               (REJ_SAMPLE(SUB_LIST(0,2*k) inlist))) = 256) /\
            rej_uniform_scalar_prefix res buf buflen table inlist e k s` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC(normalize MLKEM_REJ_UNIFORM_FINAL) THEN
                             ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
    `inlist:(12 word)list`; `e:uarch_event list`; `N:num`; `pc:num`]
     (normalize MLKEM_REJ_UNIFORM_TEST16)) THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `48 * N + 24 <= buflen` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `LENGTH(REJ_SAMPLE(SUB_LIST(0,32 * N) inlist)) <= 240` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [state `pc + 0x19c` `16 * N` THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      state `pc + 0x220` `16 * N + 8` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(normalize MLKEM_REJ_UNIFORM_BLOCK16) THEN ASM_REWRITE_TAC[];
        MP_TAC(SPECL [`inlist:(12 word)list`; `32 * N`; `16`] REJ_UNIFORM_LENGTH_STEP) THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `LENGTH(REJ_SAMPLE(SUB_LIST(0,32*N+16) inlist)) <= 256`
          ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN scalar `16 * N + 8`];
      state `pc + 0x220` `16 * N` THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; scalar `16 * N`]];
    DISCH_TAC THEN SUBGOAL_THEN `2 * (16 * N) = LENGTH(inlist:(12 word)list)` ASSUME_TAC THENL
     [MP_TAC(ASSUME `24 divides buflen`) THEN REWRITE_TAC[divides] THEN
      DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN
      SUBGOAL_THEN `d = 2 * N` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC(BETA_RULE(MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM) th))) THEN
    X_GEN_TAC `s:armstate` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `16 * N` THEN ASM_REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC REJ_UNIFORM_TO_SCALAR_PREFIX THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 16 * n = 32 * n`] THEN
    SUBGOAL_THEN `32*N = LENGTH(inlist:(12 word)list)`
      (SUBST1_TAC o SYM) THENL [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]]);;

(* Project the functional result and the bounds on memory accesses. *)
let REJ_UNIFORM_PROJECT_TAC starting_events =
  REWRITE_TAC[ensures] THEN X_GEN_TAC `s0:armstate` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:int64`; `table:int64`;
    `inlist:(12 word)list`; `pc:num`; starting_events]
    MLKEM_REJ_UNIFORM_CORRECT_MEMSAFE) THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s0:armstate`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  SIMP_TAC[];;

let MLKEM_REJ_UNIFORM_CORRECT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc.
    24 divides val buflen /\ 8 * val buflen = 12 * LENGTH inlist /\
    ALL (nonoverlapping (res,512))
      [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,val buflen); (table,4096)]
    ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word pc /\ C_ARGUMENTS [res;buf;buflen;table] s /\
            read (memory :> bytes(table,4096)) s = num_of_wordlist mlkem_rej_uniform_table /\
            read (memory :> bytes(buf,val buflen)) s = num_of_wordlist inlist)
       (\s. read PC s = word(pc + 0x27c) /\
            let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
            let outlen = LENGTH outlist in
            C_RETURN s = word outlen /\
            read (memory :> bytes(res,2 * outlen)) s = num_of_wordlist outlist)
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,512)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REJ_UNIFORM_PROJECT_TAC `read events s0`);;

(* This must be kept in sync with the CBMC specification in
   mlkem/src/native/aarch64/src/arith_native_aarch64.h. *)
let MLKEM_REJ_UNIFORM_SUBROUTINE_CORRECT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc returnaddress.
    24 divides val buflen /\ 8 * val buflen = 12 * LENGTH inlist /\
    ALL (nonoverlapping (res,512))
      [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,val buflen); (table,4096)]
    ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word pc /\ read X30 s = returnaddress /\
            C_ARGUMENTS [res;buf;buflen;table] s /\
            read (memory :> bytes(table,4096)) s = num_of_wordlist mlkem_rej_uniform_table /\
            read (memory :> bytes(buf,val buflen)) s = num_of_wordlist inlist)
       (\s. read PC s = returnaddress /\
            let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
            let outlen = LENGTH outlist in
            C_RETURN s = word outlen /\
            read (memory :> bytes(res,2 * outlen)) s = num_of_wordlist outlist)
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,512)])`,
  let conv = TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory; LENGTH_MLKEM_REJ_UNIFORM_MC] in
  CONV_TAC conv THEN ARM_ADD_RETURN_NOSTACK_TAC MLKEM_REJ_UNIFORM_EXEC
    (CONV_RULE conv MLKEM_REJ_UNIFORM_CORRECT));;

let MLKEM_REJ_UNIFORM_MEMSAFE = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e.
    24 divides val buflen /\ 8 * val buflen = 12 * LENGTH inlist /\
    ALL (nonoverlapping (res,512))
      [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,val buflen); (table,4096)]
    ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word pc /\ C_ARGUMENTS [res;buf;buflen;table] s /\
            wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
            wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
            read events s = e)
       (\s. read PC s = word(pc + 0x27c) /\
            ?e2. read events s = APPEND e2 e /\
                 memaccess_inbounds e2 [buf,val buflen;table,4096] [res,512])
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,512)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
    (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
    `val(buflen:int64)`; `inlist:(12 word)list`]
    (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_12] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REJ_UNIFORM_PROJECT_TAC `e:uarch_event list`);;

let MLKEM_REJ_UNIFORM_SUBROUTINE_MEMSAFE = prove
 (`!res buf buflen table (inlist:(12 word)list) pc e returnaddress.
    24 divides val buflen /\ 8 * val buflen = 12 * LENGTH inlist /\
    ALL (nonoverlapping (res,512))
      [(word pc,LENGTH mlkem_rej_uniform_mc); (buf,val buflen); (table,4096)]
    ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
            read PC s = word pc /\ read X30 s = returnaddress /\
            C_ARGUMENTS [res;buf;buflen;table] s /\
            wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
            wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
            read events s = e)
       (\s. read PC s = returnaddress /\
            ?e2. read events s = APPEND e2 e /\
                 memaccess_inbounds e2 [buf,val buflen;table,4096] [res,512])
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(res,512)])`,
  let conv = TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory; LENGTH_MLKEM_REJ_UNIFORM_MC] in
  CONV_TAC conv THEN ARM_ADD_RETURN_NOSTACK_TAC MLKEM_REJ_UNIFORM_EXEC
    (CONV_RULE conv MLKEM_REJ_UNIFORM_MEMSAFE) THEN DISCHARGE_MEMSAFE_TAC);;
