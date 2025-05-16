(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks into a byte array.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "mlkem/mlkem_poly_tobytes.o";;
 ****)

let mlkem_poly_tobytes_mc = define_assert_from_elf
  "mlkem_poly_tobytes_mc" "mlkem/mlkem_poly_tobytes.o"
[
  0xd2800202;       (* arm_MOV X2 (rvalue (word 16)) *)
  0x3cc20426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0038;       (* arm_LDR Q24 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc2043e;       (* arm_LDR Q30 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0036;       (* arm_LDR Q22 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20425;       (* arm_LDR Q5 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0031;       (* arm_LDR Q17 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20433;       (* arm_LDR Q19 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0xd342fc42;       (* arm_LSR X2 X2 2 *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0x4e5818d9;       (* arm_UZP1 Q25 Q6 Q24 16 *)
  0x4e5858c6;       (* arm_UZP2 Q6 Q6 Q24 16 *)
  0x0e212b38;       (* arm_XTN Q24 Q25 8 *)
  0x0f088739;       (* arm_SHRN Q25 Q25 8 8 *)
  0x0e2128d2;       (* arm_XTN Q18 Q6 8 *)
  0x0f0c84da;       (* arm_SHRN Q26 Q6 4 8 *)
  0x2f0c5659;       (* arm_SLI_VEC Q25 Q18 4 64 8 *)
  0x0c9f4018;       (* arm_ST3 [Q24; Q25; Q26] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x4e561bd9;       (* arm_UZP1 Q25 Q30 Q22 16 *)
  0x4e565bc6;       (* arm_UZP2 Q6 Q30 Q22 16 *)
  0x0e212b38;       (* arm_XTN Q24 Q25 8 *)
  0x0e2128d2;       (* arm_XTN Q18 Q6 8 *)
  0x4e5118be;       (* arm_UZP1 Q30 Q5 Q17 16 *)
  0x4e5158b6;       (* arm_UZP2 Q22 Q5 Q17 16 *)
  0x0e212bc5;       (* arm_XTN Q5 Q30 8 *)
  0x0e212ad1;       (* arm_XTN Q17 Q22 8 *)
  0x4e441a7c;       (* arm_UZP1 Q28 Q19 Q4 16 *)
  0x4e445a73;       (* arm_UZP2 Q19 Q19 Q4 16 *)
  0x0e212b84;       (* arm_XTN Q4 Q28 8 *)
  0x0e212a74;       (* arm_XTN Q20 Q19 8 *)
  0x0f088739;       (* arm_SHRN Q25 Q25 8 8 *)
  0x2f0c5659;       (* arm_SLI_VEC Q25 Q18 4 64 8 *)
  0x0f0c84da;       (* arm_SHRN Q26 Q6 4 8 *)
  0x0c9f4018;       (* arm_ST3 [Q24; Q25; Q26] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f0887c6;       (* arm_SHRN Q6 Q30 8 8 *)
  0x2f0c5626;       (* arm_SLI_VEC Q6 Q17 4 64 8 *)
  0x0f0c86c7;       (* arm_SHRN Q7 Q22 4 8 *)
  0x0c9f4005;       (* arm_ST3 [Q5; Q6; Q7] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f088785;       (* arm_SHRN Q5 Q28 8 8 *)
  0x0f0c8666;       (* arm_SHRN Q6 Q19 4 8 *)
  0x2f0c5685;       (* arm_SLI_VEC Q5 Q20 4 64 8 *)
  0x0c9f4004;       (* arm_ST3 [Q4; Q5; Q6] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x3cc20426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0038;       (* arm_LDR Q24 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc2043e;       (* arm_LDR Q30 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0036;       (* arm_LDR Q22 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20425;       (* arm_LDR Q5 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0031;       (* arm_LDR Q17 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20433;       (* arm_LDR Q19 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fffae2;       (* arm_CBNZ X2 (word 2096988) *)
  0x4e561bd9;       (* arm_UZP1 Q25 Q30 Q22 16 *)
  0x4e565bd2;       (* arm_UZP2 Q18 Q30 Q22 16 *)
  0x4e5818de;       (* arm_UZP1 Q30 Q6 Q24 16 *)
  0x4e5858c6;       (* arm_UZP2 Q6 Q6 Q24 16 *)
  0x4e5118b8;       (* arm_UZP1 Q24 Q5 Q17 16 *)
  0x4e5158b6;       (* arm_UZP2 Q22 Q5 Q17 16 *)
  0x4e441a65;       (* arm_UZP1 Q5 Q19 Q4 16 *)
  0x4e445a71;       (* arm_UZP2 Q17 Q19 Q4 16 *)
  0x0e212b33;       (* arm_XTN Q19 Q25 8 *)
  0x0f088734;       (* arm_SHRN Q20 Q25 8 8 *)
  0x0e212a59;       (* arm_XTN Q25 Q18 8 *)
  0x0f0c8655;       (* arm_SHRN Q21 Q18 4 8 *)
  0x0e212bdc;       (* arm_XTN Q28 Q30 8 *)
  0x0f0887dd;       (* arm_SHRN Q29 Q30 8 8 *)
  0x0e2128d2;       (* arm_XTN Q18 Q6 8 *)
  0x0f0c84de;       (* arm_SHRN Q30 Q6 4 8 *)
  0x0e212b01;       (* arm_XTN Q1 Q24 8 *)
  0x0f088702;       (* arm_SHRN Q2 Q24 8 8 *)
  0x0e212ac6;       (* arm_XTN Q6 Q22 8 *)
  0x0f0c86c3;       (* arm_SHRN Q3 Q22 4 8 *)
  0x0e2128b6;       (* arm_XTN Q22 Q5 8 *)
  0x0f0884b7;       (* arm_SHRN Q23 Q5 8 8 *)
  0x0e212a25;       (* arm_XTN Q5 Q17 8 *)
  0x0f0c8638;       (* arm_SHRN Q24 Q17 4 8 *)
  0x2f0c5734;       (* arm_SLI_VEC Q20 Q25 4 64 8 *)
  0x2f0c565d;       (* arm_SLI_VEC Q29 Q18 4 64 8 *)
  0x0c9f401c;       (* arm_ST3 [Q28; Q29; Q30] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0c9f4013;       (* arm_ST3 [Q19; Q20; Q21] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x2f0c54c2;       (* arm_SLI_VEC Q2 Q6 4 64 8 *)
  0x0c9f4001;       (* arm_ST3 [Q1; Q2; Q3] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x2f0c54b7;       (* arm_SLI_VEC Q23 Q5 4 64 8 *)
  0x0c9f4016;       (* arm_ST3 [Q22; Q23; Q24] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_POLY_TOBYTES_EXEC = ARM_MK_EXEC_RULE mlkem_poly_tobytes_mc;;

(* ------------------------------------------------------------------------- *)
(* A construct handy to expand out some lists explicitly. The conversion     *)
(* is a bit stupid (quadratic) but good enough for this application.         *)
(* ------------------------------------------------------------------------- *)

let LIST_OF_FUN = define
 `LIST_OF_FUN 0 (f:num->A) = [] /\
  LIST_OF_FUN (SUC n) f = APPEND (LIST_OF_FUN n f) [f n]`;;

let LENGTH_LIST_OF_FUN = prove
 (`!(f:num->A) n. LENGTH (LIST_OF_FUN n f) = n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_FUN; LENGTH; LENGTH_APPEND; ADD_CLAUSES]);;

let MAP_LIST_OF_FUN = prove
 (`!f (g:A->B) n. MAP g (LIST_OF_FUN n f) = LIST_OF_FUN n (g o f)`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LIST_OF_FUN; MAP_APPEND; o_THM]);;

let EL_LIST_OF_FUN = prove
 (`!(f:num->A) n i. i < n ==> EL i (LIST_OF_FUN n f) = f i`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LT; LIST_OF_FUN; EL_APPEND] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[LENGTH_LIST_OF_FUN] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[SUB_REFL; EL; HD; LT_REFL]);;

let LIST_OF_FUN_ALT = prove
 (`(!(f:num->A). LIST_OF_FUN 0 f = []) /\
   (!(f:num->A) n.
        LIST_OF_FUN (SUC n) f = CONS (f 0) (LIST_OF_FUN n (f o SUC)))`,
  REWRITE_TAC[CONJUNCT1 LIST_OF_FUN] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_FUN; LENGTH; EL_CONS] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[NOT_SUC; EL_LIST_OF_FUN] THEN
  ASM_SIMP_TAC[LT_SUC; SUC_SUB1; EL_LIST_OF_FUN; o_THM]);;

let LIST_OF_FUN_EQ_SELF = prove
 (`!l:A list. LIST_OF_FUN (LENGTH l) (\i. EL i l) = l`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_FUN; EL_LIST_OF_FUN]);;

let LIST_OF_FUN_CONV =
  let baseconv = GEN_REWRITE_CONV I [CONJUNCT1 LIST_OF_FUN]
  and stepconv = GEN_REWRITE_CONV I [CONJUNCT2 LIST_OF_FUN] in
  let rec conv tm =
    try baseconv tm with Failure _ ->
    (LAND_CONV num_CONV THENC stepconv THENC LAND_CONV conv) tm in
  conv THENC GEN_REWRITE_CONV TOP_DEPTH_CONV [APPEND];;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let lemma =
  let th = (GEN_REWRITE_CONV I [word_interleave] THENC
            ONCE_DEPTH_CONV LENGTH_CONV THENC let_CONV)
           `word_interleave 8 [x:int64; y; z]:192 word` in
  let th' = REWRITE_RULE[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; IN_ELIM_THM;
             DIMINDEX_CONV `dimindex(:192)`; LET_DEF; LET_END_DEF] th in
  CONV_RULE(EXPAND_CASES_CONV THENC
            DEPTH_CONV (NUM_RED_CONV ORELSEC EL_CONV)) th';;

let MLKEM_POLY_TOBYTES_CORRECT = prove
 (`!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,384)) [(word pc,0x158); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_tobytes_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + 0x154) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the LENGTH l = 256 hypothesis ***)

  ASM_CASES_TAC `LENGTH(l:int16 list) = 256` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    ARM_QUICKSIM_TAC MLKEM_POLY_TOBYTES_EXEC
     [`read X0 s = a`; `read X1 s = z`; `read X2 s = i`] (1--169)] THEN

  (*** Digitize and tweak the input digits to match 128-bit load size  ****)

  UNDISCH_TAC
   `read(memory :> bytes(a,512)) s0 = num_of_wordlist(l:int16 list)` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_FUN_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_FUN_CONV))) THEN
  REWRITE_TAC[] THEN
  REPLICATE_TAC 3
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Unroll and simulate to the end ***)

  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_TOBYTES_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
   (1--169) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Now fiddle round to make things match up nicely ***)

  REWRITE_TAC[ARITH_RULE `384 = 8 * 48`] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM LIST_OF_FUN_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(funpow 3 RAND_CONV (LIST_OF_FUN_CONV)) THEN
  REWRITE_TAC[MAP] THEN
  REWRITE_TAC[num_of_wordlist; VAL] THEN

  (*** Now more or less brute-force except avoid creating big numbers ***)

  REWRITE_TAC[bignum_of_wordlist; VAL] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV
   (BIT_WORD_CONV ORELSEC
    GEN_REWRITE_CONV I [lemma] ORELSEC
    GEN_REWRITE_CONV I [BITVAL_CLAUSES; OR_CLAUSES; AND_CLAUSES])) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ABBREV_TAC `twae = &2:real` THEN REAL_ARITH_TAC);;

let MLKEM_POLY_TOBYTES_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,384)) [(word pc,0x158); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_tobytes_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_TOBYTES_EXEC
   MLKEM_POLY_TOBYTES_CORRECT);;
