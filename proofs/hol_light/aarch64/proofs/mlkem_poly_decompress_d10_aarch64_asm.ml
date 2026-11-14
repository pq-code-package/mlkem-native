(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 10 bits.                    *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_common.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_d10_table.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_decompress_d10_aarch64_asm.o";;
 ****)

let mlkem_poly_decompress_d10_mc = define_assert_from_elf
  "mlkem_poly_decompress_d10_mc" "aarch64/mlkem/mlkem_poly_decompress_d10_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x4cdf2050;       (* arm_LDP4 Q16 Q17 Q18 Q19 X2 (Postimmediate_Offset (word 64)) *)
  0x4c407054;       (* arm_LDR Q20 X2 No_Offset *)
  0xd2800103;       (* arm_MOV X3 (rvalue (word 8)) *)
  0x91002824;       (* arm_ADD X4 X1 (rvalue (word 10)) *)
  0x91005025;       (* arm_ADD X5 X1 (rvalue (word 20)) *)
  0x91006026;       (* arm_ADD X6 X1 (rvalue (word 24)) *)
  0x4c407020;       (* arm_LDR Q0 X1 No_Offset *)
  0x4c407081;       (* arm_LDR Q1 X4 No_Offset *)
  0x4c4070a2;       (* arm_LDR Q2 X5 No_Offset *)
  0x4c4070c3;       (* arm_LDR Q3 X6 No_Offset *)
  0x9100a021;       (* arm_ADD X1 X1 (rvalue (word 40)) *)
  0x4e100004;       (* arm_TBL Q4 [Q0] Q16 128 *)
  0x6e724484;       (* arm_USHL_VEC Q4 Q4 Q18 16 128 *)
  0x4e331c84;       (* arm_AND_VEC Q4 Q4 Q19 128 *)
  0x4e100025;       (* arm_TBL Q5 [Q1] Q16 128 *)
  0x6e7244a5;       (* arm_USHL_VEC Q5 Q5 Q18 16 128 *)
  0x4e331ca5;       (* arm_AND_VEC Q5 Q5 Q19 128 *)
  0x4e100046;       (* arm_TBL Q6 [Q2] Q16 128 *)
  0x6e7244c6;       (* arm_USHL_VEC Q6 Q6 Q18 16 128 *)
  0x4e331cc6;       (* arm_AND_VEC Q6 Q6 Q19 128 *)
  0x4e110067;       (* arm_TBL Q7 [Q3] Q17 128 *)
  0x6e7244e7;       (* arm_USHL_VEC Q7 Q7 Q18 16 128 *)
  0x4e331ce7;       (* arm_AND_VEC Q7 Q7 Q19 128 *)
  0x6e74b484;       (* arm_SQRDMULH_VEC Q4 Q4 Q20 16 128 *)
  0x6e74b4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q20 16 128 *)
  0x6e74b4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q20 16 128 *)
  0x6e74b4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q20 16 128 *)
  0xac821404;       (* arm_STP Q4 Q5 X0 (Postimmediate_Offset (iword (&64))) *)
  0xad3f1c06;       (* arm_STP Q6 Q7 X0 (Immediate_Offset (iword (-- &32))) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0xb5fffca3;       (* arm_CBNZ X3 (word 2097044) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_DECOMPRESS_D10_EXEC = ARM_MK_EXEC_RULE mlkem_poly_decompress_d10_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D10_MC =
  REWRITE_CONV[mlkem_poly_decompress_d10_mc] `LENGTH mlkem_poly_decompress_d10_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_DECOMPRESS_D10_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D10_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_DECOMPRESS_D10_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D10_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_DECOMPRESS_D10_CORE_START = new_definition
  `MLKEM_POLY_DECOMPRESS_D10_CORE_START = MLKEM_POLY_DECOMPRESS_D10_PREAMBLE_LENGTH`;;

let MLKEM_POLY_DECOMPRESS_D10_CORE_END = new_definition
  `MLKEM_POLY_DECOMPRESS_D10_CORE_END =
   LENGTH mlkem_poly_decompress_d10_mc - MLKEM_POLY_DECOMPRESS_D10_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D10_MC;
               MLKEM_POLY_DECOMPRESS_D10_CORE_START;
               MLKEM_POLY_DECOMPRESS_D10_CORE_END;
               MLKEM_POLY_DECOMPRESS_D10_PREAMBLE_LENGTH;
               MLKEM_POLY_DECOMPRESS_D10_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Per-coefficient lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Split the 320-byte input into eight 320-bit words of 32 coefficients,
 * one for each loop iteration. *)

let NUM_OF_WORDLIST_SPLIT_10_256 = mk_split_theorem 10 256 32;;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D10 = mk_subword_cases 10 32;;

(* Each loop iteration loads 16 bytes at offsets 0, 10, 20 and 24 of its
 * 40-byte input chunk. These loads overlap, so we derive each of them from
 * the read of the whole chunk. *)

let READ_WBYTES320_BYTES128 = prove
 (`!a k (w:320 word) (s:armstate).
        k <= 24 /\ read (memory :> wbytes a) s = w
        ==> read (memory :> bytes128 (word_add a (word k))) s =
            word_subword w (8 * k,128)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; BYTES128_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 128 128 = 8 * 16`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  AP_THM_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* The code computes x << 2 for each 10-bit input coefficient x, then
 * multiplies by 3329 << 3 = 26632 using SQRDMULH. This is the instance
 * a = 2, b = 3 of WORD_2SMULH_ROUND_DECOMPRESS, with word_2smulh_round
 * unfolded as it appears after symbolic simulation. *)

let DECOMPRESS_D10_SQRDMULH = prove
 (`!x:10 word.
        iword_saturate((&2 * ival(word_shl (word_zx x) 2 : int16) * &26632 +
                        &32768) div &65536) : int16 =
        decompress_d10 x`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`x:10 word`; `2`; `3`] WORD_2SMULH_ROUND_DECOMPRESS) THEN
  REWRITE_TAC[word_2smulh_round; decompress_d10; DIMINDEX_16] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC DEPTH_CONV WORD_RED_CONV THENC
           INT_REDUCE_CONV) THEN
  SIMP_TAC[]);;

(* Rewrite an output lane computed by the code into decompress_d10 applied
 * to a 10-bit field of a 320-bit input chunk w. Before the SQRDMULH, the
 * lane is a combination of TBL, USHL and AND applied to bytes of w. The
 * lowest bit it reads is in byte j = p / 8 of w, and the coefficient
 * starts at bit 2 * (j MOD 5) of that byte (coefficients start at bit
 * offsets 0, 2, 4, 6 within the bytes of each 5-byte group). We prove that
 * the lane equals x << 2 for that coefficient x by bit-blasting, and then
 * apply DECOMPRESS_D10_SQRDMULH. *)

let DECOMPRESS_D10_LANE_CONV =
  let pat =
    `iword_saturate((&2 * ival(e:int16) * &26632 + &32768) div &65536):int16`
  and w320_ty = `:320 word` in
  let is_w320_subword w t =
    match t with
      Comb(Comb(Const("word_subword",_),x),_) -> x = w
    | _ -> false in
  fun tm ->
    let e = instantiate (term_match [] pat tm) `e:int16` in
    let w = find_term (fun t -> type_of t = w320_ty) e in
    let ps = map (fun t -> dest_small_numeral(lhand(rand t)))
                 (find_terms (is_w320_subword w) e) in
    let p = end_itlist min ps in
    let j = p / 8 in
    let pos = 8 * j + 2 * (j mod 5) in
    let rhs = subst [w,`w:320 word`; mk_small_numeral pos,`pos:num`]
      `word_shl (word_zx (word_subword (w:320 word) (pos,10):10 word)) 2
       :int16` in
    let eth = WORD_BLAST (mk_eq(e,rhs)) in
    (PURE_ONCE_REWRITE_CONV[eth] THENC REWR_CONV DECOMPRESS_D10_SQRDMULH) tm;;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_DECOMPRESS_D10_CORRECT = prove
 (`!r a t (l:(10 word) list) pc.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d10_mc); (a,320); (t,80)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d10_mc /\
                  read PC s = word (pc + MLKEM_POLY_DECOMPRESS_D10_CORE_START) /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,320)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,80)) s =
                    num_of_wordlist mlkem_decompress_d10_table)
             (\s. read PC s = word(pc + MLKEM_POLY_DECOMPRESS_D10_CORE_END) /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d10 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `t:int64`; `l:(10 word) list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Split the input into eight 320-bit words, one per iteration ***)

  UNDISCH_TAC
   `read(memory :> bytes(a,320)) s0 = num_of_wordlist(l:(10 word) list)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NUM_OF_WORDLIST_SPLIT_10_256 th]) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP; o_DEF] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN STRIP_TAC THEN

  (*** Derive the four overlapping 128-bit loads from each 320-bit word ***)

  REPEAT(FIRST_X_ASSUM(fun th ->
    let lhs,w = dest_eq(concl th) in
    if type_of w <> `:320 word` then failwith "" else
    let addr = rand(rand(rand(rator lhs))) in
    MAP_EVERY (fun k ->
      let kth = ARITH_RULE(mk_binary "<=" (mk_small_numeral k,`24`)) in
      ASSUME_TAC
       (CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
                  RAND_CONV(DEPTH_CONV NUM_MULT_CONV))
         (REWRITE_RULE[WORD_ADD_0]
           (MATCH_MP (SPECL [addr; mk_small_numeral k] READ_WBYTES320_BYTES128)
                     (CONJ kth th)))))
      [0; 10; 20; 24])) THEN

  (*** Split the table into its five 128-bit constant vectors ***)

  UNDISCH_TAC
   `read(memory :> bytes(t,80)) s0 =
    num_of_wordlist mlkem_decompress_d10_table` THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[mlkem_decompress_d10_table; pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Unroll and simulate to the end ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_DECOMPRESS_D10_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC []) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Express each output lane as decompress_d10 of an input coefficient ***)

  MAP_EVERY (fun i -> SUBGOAL_THEN
    (subst [mk_small_numeral (32 * i), `i:num`]
      `LENGTH (SUB_LIST (i,32) (l:(10 word) list)) = 32`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC])
    (0--7) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV DECOMPRESS_D10_LANE_CONV)) o
    check (fun th ->
      can (term_match [] `read (memory :> bytes128 r) s = xxx`) (concl th) &&
      vfree_in `r:int64` (lhand(concl th))))) THEN
  IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D10 THEN
  UNDISCH_THEN `LENGTH (l:(10 word) list) = 256`
   (fun th -> CONV_TAC(TOP_SWEEP_CONV(EL_SUB_LIST_CONV th)) THEN
              ASSUME_TAC th) THEN
  REPEAT DISCH_TAC THEN

  (*** Spell out the output list and compare 128 bits at a time ***)

  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC(TOP_SWEEP_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP] THEN
  REPLICATE_TAC 3
   (CONV_TAC(ONCE_REWRITE_CONV[GSYM NUM_OF_PAIR_WORDLIST])) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM BYTES128_WBYTES]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_DECOMPRESS_D10_SUBROUTINE_CORRECT = prove
 (`!r a t (l:(10 word) list) pc returnaddress.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d10_mc); (a,320); (t,80)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d10_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,320)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,80)) s =
                    num_of_wordlist mlkem_decompress_d10_table)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d10 l) /\
                  (!i. i < 256
                       ==> &0 <= ival(EL i (MAP decompress_d10 l)) /\
                           ival(EL i (MAP decompress_d10 l)) < &3329))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_DECOMPRESS_D10_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D10_CORRECT) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP; IVAL_DECOMPRESS_D10_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_poly_decompress_d10" subroutine_signatures)
    MLKEM_POLY_DECOMPRESS_D10_SUBROUTINE_CORRECT
    MLKEM_POLY_DECOMPRESS_D10_EXEC;;

let MLKEM_POLY_DECOMPRESS_D10_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a t (l:(10 word) list) pc returnaddress.
           LENGTH l = 256 /\
           ALL (nonoverlapping (r,512))
               [word pc,LENGTH mlkem_poly_decompress_d10_mc; a,320; t,80]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_poly_decompress_d10_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a; t] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a t r pc returnaddress /\
                        memaccess_inbounds e2 [a,320; t,80; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_DECOMPRESS_D10_EXEC);;
