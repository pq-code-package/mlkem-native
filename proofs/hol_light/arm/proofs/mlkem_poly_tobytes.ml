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
  0x3cc2043d;       (* arm_LDR Q29 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf003f;       (* arm_LDR Q31 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc00432;       (* arm_LDR Q18 X1 (Immediate_Offset (word 16)) *)
  0x3cc20437;       (* arm_LDR Q23 X1 (Postimmediate_Offset (word 32)) *)
  0x3dc01436;       (* arm_LDR Q22 X1 (Immediate_Offset (word 80)) *)
  0x3dc00431;       (* arm_LDR Q17 X1 (Immediate_Offset (word 16)) *)
  0x3dc00c21;       (* arm_LDR Q1 X1 (Immediate_Offset (word 48)) *)
  0x4e5f1ba5;       (* arm_UZP1 Q5 Q29 Q31 16 *)
  0x4e5f5bb4;       (* arm_UZP2 Q20 Q29 Q31 16 *)
  0x3cc2043f;       (* arm_LDR Q31 X1 (Postimmediate_Offset (word 32)) *)
  0x4e525af5;       (* arm_UZP2 Q21 Q23 Q18 16 *)
  0x0e212a9d;       (* arm_XTN Q29 Q20 8 *)
  0x0f0884ba;       (* arm_SHRN Q26 Q5 8 8 *)
  0x0e2128b9;       (* arm_XTN Q25 Q5 8 *)
  0x3cc2043c;       (* arm_LDR Q28 X1 (Postimmediate_Offset (word 32)) *)
  0x2f0c57ba;       (* arm_SLI_VEC Q26 Q29 4 64 8 *)
  0xd342fc42;       (* arm_LSR X2 X2 2 *)
  0xd1000842;       (* arm_SUB X2 X2 (rvalue (word 2)) *)
  0x3cc2043e;       (* arm_LDR Q30 X1 (Postimmediate_Offset (word 32)) *)
  0x4e521ae3;       (* arm_UZP1 Q3 Q23 Q18 16 *)
  0x3dc00432;       (* arm_LDR Q18 X1 (Immediate_Offset (word 16)) *)
  0x4e415b90;       (* arm_UZP2 Q16 Q28 Q1 16 *)
  0x0f0c869b;       (* arm_SHRN Q27 Q20 4 8 *)
  0x4e411b85;       (* arm_UZP1 Q5 Q28 Q1 16 *)
  0x0f088477;       (* arm_SHRN Q23 Q3 8 8 *)
  0x4e515be0;       (* arm_UZP2 Q0 Q31 Q17 16 *)
  0x4e511bff;       (* arm_UZP1 Q31 Q31 Q17 16 *)
  0x4e565bd4;       (* arm_UZP2 Q20 Q30 Q22 16 *)
  0x0f0c8606;       (* arm_SHRN Q6 Q16 4 8 *)
  0x0e212807;       (* arm_XTN Q7 Q0 8 *)
  0x0c9f4019;       (* arm_ST3 [Q25; Q26; Q27] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f0c86b8;       (* arm_SHRN Q24 Q21 4 8 *)
  0x0f0887fc;       (* arm_SHRN Q28 Q31 8 8 *)
  0x3dc01421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 80)) *)
  0x0f0c841d;       (* arm_SHRN Q29 Q0 4 8 *)
  0x3dc00c31;       (* arm_LDR Q17 X1 (Immediate_Offset (word 48)) *)
  0x0e2128a4;       (* arm_XTN Q4 Q5 8 *)
  0x0e212ab3;       (* arm_XTN Q19 Q21 8 *)
  0x4e561bc2;       (* arm_UZP1 Q2 Q30 Q22 16 *)
  0x0f0884a5;       (* arm_SHRN Q5 Q5 8 8 *)
  0x2f0c5677;       (* arm_SLI_VEC Q23 Q19 4 64 8 *)
  0x0e212876;       (* arm_XTN Q22 Q3 8 *)
  0x2f0c54fc;       (* arm_SLI_VEC Q28 Q7 4 64 8 *)
  0x0e212a83;       (* arm_XTN Q3 Q20 8 *)
  0x0f08845a;       (* arm_SHRN Q26 Q2 8 8 *)
  0x0e212859;       (* arm_XTN Q25 Q2 8 *)
  0x0e212bfb;       (* arm_XTN Q27 Q31 8 *)
  0x0c9f4016;       (* arm_ST3 [Q22; Q23; Q24] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0e212a10;       (* arm_XTN Q16 Q16 8 *)
  0x3cc20437;       (* arm_LDR Q23 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc2043f;       (* arm_LDR Q31 X1 (Postimmediate_Offset (word 32)) *)
  0x0c9f401b;       (* arm_ST3 [Q27; Q28; Q29] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x2f0c5605;       (* arm_SLI_VEC Q5 Q16 4 64 8 *)
  0x3cc2043c;       (* arm_LDR Q28 X1 (Postimmediate_Offset (word 32)) *)
  0x2f0c547a;       (* arm_SLI_VEC Q26 Q3 4 64 8 *)
  0x3dc00436;       (* arm_LDR Q22 X1 (Immediate_Offset (word 16)) *)
  0x4e525af5;       (* arm_UZP2 Q21 Q23 Q18 16 *)
  0x0c9f4004;       (* arm_ST3 [Q4; Q5; Q6] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0xf1000442;       (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  0xb5fffae2;       (* arm_CBNZ X2 (word 2096988) *)
  0x4e415b82;       (* arm_UZP2 Q2 Q28 Q1 16 *)
  0x4e411b80;       (* arm_UZP1 Q0 Q28 Q1 16 *)
  0x0f0c869b;       (* arm_SHRN Q27 Q20 4 8 *)
  0x4e521af2;       (* arm_UZP1 Q18 Q23 Q18 16 *)
  0x0f088405;       (* arm_SHRN Q5 Q0 8 8 *)
  0x0e21285d;       (* arm_XTN Q29 Q2 8 *)
  0x0c9f4019;       (* arm_ST3 [Q25; Q26; Q27] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f0c8446;       (* arm_SHRN Q6 Q2 4 8 *)
  0x3cc20439;       (* arm_LDR Q25 X1 (Postimmediate_Offset (word 32)) *)
  0x4e511bf8;       (* arm_UZP1 Q24 Q31 Q17 16 *)
  0x4e515bf0;       (* arm_UZP2 Q16 Q31 Q17 16 *)
  0x3cc20437;       (* arm_LDR Q23 X1 (Postimmediate_Offset (word 32)) *)
  0x0e212abc;       (* arm_XTN Q28 Q21 8 *)
  0x0f0c86b5;       (* arm_SHRN Q21 Q21 4 8 *)
  0x0e212a02;       (* arm_XTN Q2 Q16 8 *)
  0x0f088654;       (* arm_SHRN Q20 Q18 8 8 *)
  0x2f0c57a5;       (* arm_SLI_VEC Q5 Q29 4 64 8 *)
  0x0e212804;       (* arm_XTN Q4 Q0 8 *)
  0x2f0c5794;       (* arm_SLI_VEC Q20 Q28 4 64 8 *)
  0x0e212a53;       (* arm_XTN Q19 Q18 8 *)
  0x0f088712;       (* arm_SHRN Q18 Q24 8 8 *)
  0x0e212b11;       (* arm_XTN Q17 Q24 8 *)
  0x0c9f4013;       (* arm_ST3 [Q19; Q20; Q21] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f0c8613;       (* arm_SHRN Q19 Q16 4 8 *)
  0x4e561b3b;       (* arm_UZP1 Q27 Q25 Q22 16 *)
  0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
  0x2f0c5452;       (* arm_SLI_VEC Q18 Q2 4 64 8 *)
  0x3cdf0035;       (* arm_LDR Q21 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e212b7a;       (* arm_XTN Q26 Q27 8 *)
  0x0f08877b;       (* arm_SHRN Q27 Q27 8 8 *)
  0x0c9f4011;       (* arm_ST3 [Q17; Q18; Q19] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x4e565b3d;       (* arm_UZP2 Q29 Q25 Q22 16 *)
  0x3cc20434;       (* arm_LDR Q20 X1 (Postimmediate_Offset (word 32)) *)
  0x0c9f4004;       (* arm_ST3 [Q4; Q5; Q6] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x3cc2043f;       (* arm_LDR Q31 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0023;       (* arm_LDR Q3 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e551ae7;       (* arm_UZP1 Q7 Q23 Q21 16 *)
  0x0f0c87bc;       (* arm_SHRN Q28 Q29 4 8 *)
  0x4e555af9;       (* arm_UZP2 Q25 Q23 Q21 16 *)
  0x4e411a90;       (* arm_UZP1 Q16 Q20 Q1 16 *)
  0x4e415a84;       (* arm_UZP2 Q4 Q20 Q1 16 *)
  0x4e435be0;       (* arm_UZP2 Q0 Q31 Q3 16 *)
  0x4e431bf2;       (* arm_UZP1 Q18 Q31 Q3 16 *)
  0x0f088616;       (* arm_SHRN Q22 Q16 8 8 *)
  0x0e212a15;       (* arm_XTN Q21 Q16 8 *)
  0x0e212801;       (* arm_XTN Q1 Q0 8 *)
  0x0e212893;       (* arm_XTN Q19 Q4 8 *)
  0x0e212ba2;       (* arm_XTN Q2 Q29 8 *)
  0x0f0884e6;       (* arm_SHRN Q6 Q7 8 8 *)
  0x2f0c5676;       (* arm_SLI_VEC Q22 Q19 4 64 8 *)
  0x0e212b3e;       (* arm_XTN Q30 Q25 8 *)
  0x0e2128e5;       (* arm_XTN Q5 Q7 8 *)
  0x2f0c545b;       (* arm_SLI_VEC Q27 Q2 4 64 8 *)
  0x2f0c57c6;       (* arm_SLI_VEC Q6 Q30 4 64 8 *)
  0x0e212a50;       (* arm_XTN Q16 Q18 8 *)
  0x0f0c8727;       (* arm_SHRN Q7 Q25 4 8 *)
  0x0c9f401a;       (* arm_ST3 [Q26; Q27; Q28] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f0c8497;       (* arm_SHRN Q23 Q4 4 8 *)
  0x0f088651;       (* arm_SHRN Q17 Q18 8 8 *)
  0x0c9f4005;       (* arm_ST3 [Q5; Q6; Q7] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f0c8412;       (* arm_SHRN Q18 Q0 4 8 *)
  0x2f0c5431;       (* arm_SLI_VEC Q17 Q1 4 64 8 *)
  0x0c9f4015;       (* arm_ST3 [Q21; Q22; Q23] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0c9f4010;       (* arm_ST3 [Q16; Q17; Q18] X0 (Postimmediate_Offset (word 24)) 64 8 *)
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
        ALL (nonoverlapping (r,384)) [(word pc,0x1f8); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_tobytes_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + 0x1f4) /\
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
     [`read X0 s = a`; `read X1 s = z`; `read X2 s = i`] (1--167)] THEN

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
   (1--167) THEN
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

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_TOBYTES_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,384)) [(word pc,0x1f8); (a,512)]
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
