(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 5 bits.                     *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_common.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_d5_table.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_decompress_d5_aarch64_asm.o";;
 ****)

let mlkem_poly_decompress_d5_mc = define_assert_from_elf
  "mlkem_poly_decompress_d5_mc" "aarch64/mlkem/mlkem_poly_decompress_d5_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x4cdf2050;       (* arm_LDP4 Q16 Q17 Q18 Q19 X2 (Postimmediate_Offset (word 64)) *)
  0x4cdfa054;       (* arm_LDP Q20 Q21 X2 (Postimmediate_Offset (word 32)) *)
  0x4c407056;       (* arm_LDR Q22 X2 No_Offset *)
  0xd2800103;       (* arm_MOV X3 (rvalue (word 8)) *)
  0x91001024;       (* arm_ADD X4 X1 (rvalue (word 4)) *)
  0x4c407020;       (* arm_LDR Q0 X1 No_Offset *)
  0x4c407081;       (* arm_LDR Q1 X4 No_Offset *)
  0x91005021;       (* arm_ADD X1 X1 (rvalue (word 20)) *)
  0x4e100002;       (* arm_TBL Q2 [Q0] Q16 128 *)
  0x6e744442;       (* arm_USHL_VEC Q2 Q2 Q20 16 128 *)
  0x4e351c42;       (* arm_AND_VEC Q2 Q2 Q21 128 *)
  0x4e110003;       (* arm_TBL Q3 [Q0] Q17 128 *)
  0x6e744463;       (* arm_USHL_VEC Q3 Q3 Q20 16 128 *)
  0x4e351c63;       (* arm_AND_VEC Q3 Q3 Q21 128 *)
  0x4e120004;       (* arm_TBL Q4 [Q0] Q18 128 *)
  0x6e744484;       (* arm_USHL_VEC Q4 Q4 Q20 16 128 *)
  0x4e351c84;       (* arm_AND_VEC Q4 Q4 Q21 128 *)
  0x4e130025;       (* arm_TBL Q5 [Q1] Q19 128 *)
  0x6e7444a5;       (* arm_USHL_VEC Q5 Q5 Q20 16 128 *)
  0x4e351ca5;       (* arm_AND_VEC Q5 Q5 Q21 128 *)
  0x6e76b442;       (* arm_SQRDMULH_VEC Q2 Q2 Q22 16 128 *)
  0x6e76b463;       (* arm_SQRDMULH_VEC Q3 Q3 Q22 16 128 *)
  0x6e76b484;       (* arm_SQRDMULH_VEC Q4 Q4 Q22 16 128 *)
  0x6e76b4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q22 16 128 *)
  0xac820c02;       (* arm_STP Q2 Q3 X0 (Postimmediate_Offset (iword (&64))) *)
  0xad3f1404;       (* arm_STP Q4 Q5 X0 (Immediate_Offset (iword (-- &32))) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0xb5fffd23;       (* arm_CBNZ X3 (word 2097060) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_DECOMPRESS_D5_EXEC = ARM_MK_EXEC_RULE mlkem_poly_decompress_d5_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D5_MC =
  REWRITE_CONV[mlkem_poly_decompress_d5_mc] `LENGTH mlkem_poly_decompress_d5_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_DECOMPRESS_D5_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D5_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_DECOMPRESS_D5_CORE_START = new_definition
  `MLKEM_POLY_DECOMPRESS_D5_CORE_START = MLKEM_POLY_DECOMPRESS_D5_PREAMBLE_LENGTH`;;

let MLKEM_POLY_DECOMPRESS_D5_CORE_END = new_definition
  `MLKEM_POLY_DECOMPRESS_D5_CORE_END =
   LENGTH mlkem_poly_decompress_d5_mc - MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D5_MC;
               MLKEM_POLY_DECOMPRESS_D5_CORE_START;
               MLKEM_POLY_DECOMPRESS_D5_CORE_END;
               MLKEM_POLY_DECOMPRESS_D5_PREAMBLE_LENGTH;
               MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Splitting the input.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Split the 160-byte input into eight 160-bit words of 32 coefficients,
 * one for each loop iteration. *)

let NUM_OF_WORDLIST_SPLIT_5_256 = mk_split_theorem 5 256 32;;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D5 = mk_subword_cases 5 32;;

(* Each loop iteration reads its 20 bytes with two overlapping 16-byte
 * loads, of bytes 0..15 and of bytes 4..19. *)

let READ_MEMORY_WBYTES160_BYTES128 = prove
 (`!p (w:160 word) (s:armstate).
     read (memory :> wbytes p) s = w
     ==> read (memory :> bytes128 p) s = word_subword w (0,128) /\
         read (memory :> bytes128 (word_add p (word 4))) s =
         word_subword w (32,128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; BYTES128_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[DIV_1;
    ARITH_RULE `340282366920938463463374607431768211456 = 2 EXP (8 * 16)`;
    ARITH_RULE `4294967296 = 2 EXP (8 * 4)`;
    READ_BYTES_MOD; READ_BYTES_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Per-coefficient lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

(* The code gathers the 16-bit window holding a coefficient with TBL and
 * shifts it left by e with USHL, where 7 - e is the bit offset of the
 * coefficient in the window. Symbolic simulation turns USHL by a constant
 * non-negative amount into word_shl. AND with 0x1f << 7 = 3968 then leaves
 * x << 7 for the 5-bit coefficient x. For a lane
 *
 *   word_and (word 3968)
 *            (word_shl (word_join (word_subword w (_,_))
 *                                 (word_subword w (p,8))) e)
 *
 * of a 160-bit input word w, the coefficient starts at bit p + 7 - e of w.
 * We prove the identity by bit-blasting, once for each lane pattern with w
 * generalized, and then instantiate it. *)

let DECOMPRESS_D5_LANE_CONV =
  let w = `w:160 word` in
  let mask = `word 3968 : int16` in
  let cache = ref [] in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_and",_),c),
           Comb(Comb(Const("word_shl",_),j),e_tm)) when c = mask ->
        let lo = rand j in
        let wv = lhand lo in
        let p = dest_small_numeral (lhand (rand lo)) in
        let e = dest_small_numeral e_tm in
        let gtm = subst [w,wv] tm in
        let th =
          try assoc gtm !cache with Failure _ ->
          let rhs = subst [mk_small_numeral (p + 7 - e), `pos:num`]
            `word_shl (word_zx (word_subword (w:160 word) (pos,5) : 5 word)) 7
             : int16` in
          let th = WORD_BLAST (mk_eq(gtm,rhs)) in
          cache := (gtm,th) :: !cache; th in
        INST [wv,w] th
    | _ -> failwith "DECOMPRESS_D5_LANE_CONV";;

(* The code then multiplies x << 7 by 3329 << 3 = 26632 using SQRDMULH.
 * This is the instance a = 7, b = 3 of WORD_2SMULH_ROUND_DECOMPRESS, with
 * word_2smulh_round unfolded as it appears after symbolic simulation. *)

let DECOMPRESS_D5_SQRDMULH = prove
 (`!x:5 word.
        iword_saturate((&2 * ival(word_shl (word_zx x) 7 : int16) * &26632 +
                        &32768) div &65536) : int16 =
        decompress_d5 x`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`x:5 word`; `7`; `3`] WORD_2SMULH_ROUND_DECOMPRESS) THEN
  REWRITE_TAC[word_2smulh_round; decompress_d5] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC DEPTH_CONV WORD_RED_CONV THENC
           INT_REDUCE_CONV) THEN
  SIMP_TAC[]);;

(* Rewrite each output lane computed by the code into decompress_d5 applied
 * to a 5-bit field of an input word. *)

let DECOMPRESS_D5_OUTPUT_CONV =
  ONCE_DEPTH_CONV DECOMPRESS_D5_LANE_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECOMPRESS_D5_SQRDMULH];;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_DECOMPRESS_D5_CORRECT = prove
 (`!r a t (l:(5 word) list) pc.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d5_mc); (a,160); (t,112)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d5_mc /\
                  read PC s = word (pc + MLKEM_POLY_DECOMPRESS_D5_CORE_START) /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,160)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,112)) s =
                    num_of_wordlist mlkem_decompress_d5_table)
             (\s. read PC s = word(pc + MLKEM_POLY_DECOMPRESS_D5_CORE_END) /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d5 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `t:int64`; `l:(5 word) list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Split the input into eight 160-bit words of 32 coefficients ***)

  UNDISCH_TAC
   `read(memory :> bytes(a,160)) s0 = num_of_wordlist(l:(5 word) list)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NUM_OF_WORDLIST_SPLIT_5_256 th]) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP; o_DEF] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  STRIP_TAC THEN

  (*** Express the two overlapping 128-bit loads from each word ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP READ_MEMORY_WBYTES160_BYTES128 o
    check (can (term_match [] `read (memory :> wbytes p) s = (w:160 word)`) o
           concl))) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [WORD_ADD_ASSOC_CONSTS] THENC
     RAND_CONV(RAND_CONV NUM_ADD_CONV)))) THEN

  (*** Split the table into its seven 128-bit constant vectors ***)

  UNDISCH_TAC
   `read(memory :> bytes(t,112)) s0 = num_of_wordlist mlkem_decompress_d5_table` THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[mlkem_decompress_d5_table; pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Unroll and simulate to the end ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_DECOMPRESS_D5_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC []) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Express each output lane as decompress_d5 of an input coefficient ***)

  MAP_EVERY (fun i -> SUBGOAL_THEN
    (subst [mk_small_numeral (32 * i), `i:num`]
      `LENGTH (SUB_LIST (i,32) (l:(5 word) list)) = 32`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC])
    (0--7) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    CONV_RULE(RAND_CONV DECOMPRESS_D5_OUTPUT_CONV) o
    check (can (term_match [] `read (memory :> bytes128 r) s = xxx`) o
           concl))) THEN
  IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D5 THEN
  UNDISCH_THEN `LENGTH (l:(5 word) list) = 256`
   (fun th -> CONV_TAC(TOP_SWEEP_CONV(EL_SUB_LIST_CONV th)) THEN
              ASSUME_TAC th) THEN
  REPEAT DISCH_TAC THEN

  (*** Spell out the output list and compare 128 bits at a time ***)

  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_SWEEP_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP] THEN
  REPLICATE_TAC 3
   (CONV_TAC(ONCE_REWRITE_CONV[GSYM NUM_OF_PAIR_WORDLIST])) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM BYTES128_WBYTES]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_DECOMPRESS_D5_SUBROUTINE_CORRECT = prove
 (`!r a t (l:(5 word) list) pc returnaddress.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d5_mc); (a,160); (t,112)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d5_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,160)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,112)) s =
                    num_of_wordlist mlkem_decompress_d5_table)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d5 l) /\
                  (!i. i < 256
                       ==> &0 <= ival(EL i (MAP decompress_d5 l)) /\
                           ival(EL i (MAP decompress_d5 l)) < &3329))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_DECOMPRESS_D5_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D5_CORRECT) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP; IVAL_DECOMPRESS_D5_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_poly_decompress_d5" subroutine_signatures)
    MLKEM_POLY_DECOMPRESS_D5_SUBROUTINE_CORRECT
    MLKEM_POLY_DECOMPRESS_D5_EXEC;;

let MLKEM_POLY_DECOMPRESS_D5_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a t (l:(5 word) list) pc returnaddress.
           LENGTH l = 256 /\
           ALL (nonoverlapping (r,512))
               [word pc,LENGTH mlkem_poly_decompress_d5_mc; a,160; t,112]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_poly_decompress_d5_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a; t] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a t r pc returnaddress /\
                        memaccess_inbounds e2 [a,160; t,112; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_DECOMPRESS_D5_EXEC);;
