(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 11 bits.                    *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_common.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_d11_table.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_decompress_d11_aarch64_asm.o";;
 ****)

let mlkem_poly_decompress_d11_mc = define_assert_from_elf
  "mlkem_poly_decompress_d11_mc" "aarch64/mlkem/mlkem_poly_decompress_d11_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x4cdf2058;       (* arm_LDP4 Q24 Q25 Q26 Q27 X2 (Postimmediate_Offset (word 64)) *)
  0x4cdfa05c;       (* arm_LDP Q28 Q29 X2 (Postimmediate_Offset (word 32)) *)
  0x4c40705e;       (* arm_LDR Q30 X2 No_Offset *)
  0xd2800103;       (* arm_MOV X3 (rvalue (word 8)) *)
  0x91002c24;       (* arm_ADD X4 X1 (rvalue (word 11)) *)
  0x91005825;       (* arm_ADD X5 X1 (rvalue (word 22)) *)
  0x91007026;       (* arm_ADD X6 X1 (rvalue (word 28)) *)
  0x4c407020;       (* arm_LDR Q0 X1 No_Offset *)
  0x4c407081;       (* arm_LDR Q1 X4 No_Offset *)
  0x4c4070a2;       (* arm_LDR Q2 X5 No_Offset *)
  0x4c4070c3;       (* arm_LDR Q3 X6 No_Offset *)
  0x9100b021;       (* arm_ADD X1 X1 (rvalue (word 44)) *)
  0x4e180004;       (* arm_TBL Q4 [Q0] Q24 128 *)
  0x4e190010;       (* arm_TBL Q16 [Q0] Q25 128 *)
  0x6e7c4484;       (* arm_USHL_VEC Q4 Q4 Q28 16 128 *)
  0x6f1c5604;       (* arm_SLI_VEC Q4 Q16 12 128 16 *)
  0x4e3d1c84;       (* arm_AND_VEC Q4 Q4 Q29 128 *)
  0x4e180025;       (* arm_TBL Q5 [Q1] Q24 128 *)
  0x4e190031;       (* arm_TBL Q17 [Q1] Q25 128 *)
  0x6e7c44a5;       (* arm_USHL_VEC Q5 Q5 Q28 16 128 *)
  0x6f1c5625;       (* arm_SLI_VEC Q5 Q17 12 128 16 *)
  0x4e3d1ca5;       (* arm_AND_VEC Q5 Q5 Q29 128 *)
  0x4e180046;       (* arm_TBL Q6 [Q2] Q24 128 *)
  0x4e190052;       (* arm_TBL Q18 [Q2] Q25 128 *)
  0x6e7c44c6;       (* arm_USHL_VEC Q6 Q6 Q28 16 128 *)
  0x6f1c5646;       (* arm_SLI_VEC Q6 Q18 12 128 16 *)
  0x4e3d1cc6;       (* arm_AND_VEC Q6 Q6 Q29 128 *)
  0x4e1a0067;       (* arm_TBL Q7 [Q3] Q26 128 *)
  0x4e1b0073;       (* arm_TBL Q19 [Q3] Q27 128 *)
  0x6e7c44e7;       (* arm_USHL_VEC Q7 Q7 Q28 16 128 *)
  0x6f1c5667;       (* arm_SLI_VEC Q7 Q19 12 128 16 *)
  0x4e3d1ce7;       (* arm_AND_VEC Q7 Q7 Q29 128 *)
  0x6e7eb484;       (* arm_SQRDMULH_VEC Q4 Q4 Q30 16 128 *)
  0x6e7eb4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q30 16 128 *)
  0x6e7eb4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q30 16 128 *)
  0x6e7eb4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q30 16 128 *)
  0xac821404;       (* arm_STP Q4 Q5 X0 (Postimmediate_Offset (iword (&64))) *)
  0xad3f1c06;       (* arm_STP Q6 Q7 X0 (Immediate_Offset (iword (-- &32))) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0xb5fffba3;       (* arm_CBNZ X3 (word 2097012) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_DECOMPRESS_D11_EXEC = ARM_MK_EXEC_RULE mlkem_poly_decompress_d11_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D11_MC =
  REWRITE_CONV[mlkem_poly_decompress_d11_mc] `LENGTH mlkem_poly_decompress_d11_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_DECOMPRESS_D11_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D11_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_DECOMPRESS_D11_CORE_START = new_definition
  `MLKEM_POLY_DECOMPRESS_D11_CORE_START = MLKEM_POLY_DECOMPRESS_D11_PREAMBLE_LENGTH`;;

let MLKEM_POLY_DECOMPRESS_D11_CORE_END = new_definition
  `MLKEM_POLY_DECOMPRESS_D11_CORE_END =
   LENGTH mlkem_poly_decompress_d11_mc - MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D11_MC;
               MLKEM_POLY_DECOMPRESS_D11_CORE_START;
               MLKEM_POLY_DECOMPRESS_D11_CORE_END;
               MLKEM_POLY_DECOMPRESS_D11_PREAMBLE_LENGTH;
               MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Per-coefficient lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Split the 352-byte input into eight 352-bit words of 32 coefficients,
 * one for each loop iteration. *)

let NUM_OF_WORDLIST_SPLIT_11_256 = mk_split_theorem 11 256 32;;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D11 = mk_subword_cases 11 32;;

(* Each loop iteration loads 16 bytes at offsets 0, 11, 22 and 28 of its
 * 44-byte input chunk. These loads overlap, so we derive each of them from
 * the read of the whole chunk. *)

let READ_WBYTES352_BYTES128 = prove
 (`!a k (w:352 word) (s:armstate).
        k <= 28 /\ read (memory :> wbytes a) s = w
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

(* `unpack` computes x << a for each 11-bit input coefficient x, where the
 * shift a depends on the lane: a = 1 for most coefficients, and a = 2, 3
 * for the coefficients 2 and 5 of each group of 8. `decompress` multiplies
 * by 3329 << b with a + b = 4 using SQRDMULH. This is the instance (a, b)
 * of WORD_2SMULH_ROUND_DECOMPRESS, with word_2smulh_round unfolded as it
 * appears after symbolic simulation. DECOMPRESS_D11_SQRDMULH b proves it
 * for b = 0, 1, 2, 3. *)

let DECOMPRESS_D11_SQRDMULH b =
  let a = 4 - b in
  let tm = subst [mk_small_numeral a,`a:num`;
                  mk_small_numeral (3329 * (1 lsl b)),`m:num`]
   `!x:11 word.
        iword_saturate((&2 * ival(word_shl (word_zx x) a : int16) * &m +
                        &32768) div &65536) : int16 =
        decompress_d11 x` in
  prove(tm,
    GEN_TAC THEN
    MP_TAC(ISPECL [`x:11 word`; mk_small_numeral a; mk_small_numeral b]
                  WORD_2SMULH_ROUND_DECOMPRESS) THEN
    REWRITE_TAC[word_2smulh_round; decompress_d11; DIMINDEX_16] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC DEPTH_CONV WORD_RED_CONV THENC
             INT_REDUCE_CONV) THEN
    SIMP_TAC[]);;

let DECOMPRESS_D11_SQRDMULH_CASES =
  map (fun b -> 3329 * (1 lsl b), (4 - b, DECOMPRESS_D11_SQRDMULH b))
      (0--3);;

(* Rewrite the output lane for coefficient c of a 352-bit input chunk w
 * into decompress_d11 of that coefficient. Before the SQRDMULH by
 * m = 3329 << b, the lane is the result of `unpack`, a combination of
 * TBL, USHL, SLI and AND applied to bytes of w. We prove that it equals
 * x << (4 - b) for the coefficient x at bits 11 * c .. 11 * c + 10 of w
 * by bit-blasting, and then apply DECOMPRESS_D11_SQRDMULH b. *)

let DECOMPRESS_D11_LANE_CONV c tm =
  let pat =
    `iword_saturate((&2 * ival(e:int16) * &m + &32768) div &65536):int16`
  in
  let inst = term_match [] pat tm in
  let e = instantiate inst `e:int16`
  and m = dest_small_numeral (instantiate inst `m:num`) in
  let a,sth = assoc m DECOMPRESS_D11_SQRDMULH_CASES in
  let w = find_term (can (term_match []
            `word(num_of_wordlist(ll:(11 word)list)):352 word`)) e in
  let rhs = subst [w,`w:352 word`; mk_small_numeral (11 * c),`p:num`;
                   mk_small_numeral a,`a:num`]
    `word_shl (word_zx (word_subword (w:352 word) (p,11):11 word)) a
     :int16` in
  let eth = WORD_BLAST (mk_eq(e,rhs)) in
  (PURE_ONCE_REWRITE_CONV[eth] THENC REWR_CONV sth) tm;;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_DECOMPRESS_D11_CORRECT = prove
 (`!r a t (l:(11 word) list) pc.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d11_mc); (a,352); (t,112)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d11_mc /\
                  read PC s = word (pc + MLKEM_POLY_DECOMPRESS_D11_CORE_START) /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,352)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,112)) s =
                    num_of_wordlist mlkem_decompress_d11_table)
             (\s. read PC s = word(pc + MLKEM_POLY_DECOMPRESS_D11_CORE_END) /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d11 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `t:int64`; `l:(11 word) list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Split the input into eight 352-bit words, one per iteration ***)

  UNDISCH_TAC
   `read(memory :> bytes(a,352)) s0 = num_of_wordlist(l:(11 word) list)` THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP NUM_OF_WORDLIST_SPLIT_11_256 th]) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP; o_DEF] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN STRIP_TAC THEN

  (*** Derive the four overlapping 128-bit loads from each 352-bit word ***)

  REPEAT(FIRST_X_ASSUM(fun th ->
    let lhs,w = dest_eq(concl th) in
    if type_of w <> `:352 word` then failwith "" else
    let addr = rand(rand(rand(rator lhs))) in
    MAP_EVERY (fun k ->
      let kth = ARITH_RULE(mk_binary "<=" (mk_small_numeral k,`28`)) in
      ASSUME_TAC
       (CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
                  RAND_CONV(DEPTH_CONV NUM_MULT_CONV))
         (REWRITE_RULE[WORD_ADD_0]
           (MATCH_MP (SPECL [addr; mk_small_numeral k] READ_WBYTES352_BYTES128)
                     (CONJ kth th)))))
      [0; 11; 22; 28])) THEN

  (*** Split the table into its seven 128-bit constant vectors ***)

  UNDISCH_TAC
   `read(memory :> bytes(t,112)) s0 =
    num_of_wordlist mlkem_decompress_d11_table` THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[mlkem_decompress_d11_table; pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Unroll and simulate to the end ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_DECOMPRESS_D11_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC []) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Express each output lane as decompress_d11 of an input coefficient ***)

  MAP_EVERY (fun i -> SUBGOAL_THEN
    (subst [mk_small_numeral (32 * i), `i:num`]
      `LENGTH (SUB_LIST (i,32) (l:(11 word) list)) = 32`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC])
    (0--7) THEN
  RULE_ASSUM_TAC(DECODE_STORE_RULE DECOMPRESS_D11_LANE_CONV 32) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_decode_output_store o concl))) THEN
  IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D11 THEN
  UNDISCH_THEN `LENGTH (l:(11 word) list) = 256`
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

let MLKEM_POLY_DECOMPRESS_D11_SUBROUTINE_CORRECT = prove
 (`!r a t (l:(11 word) list) pc returnaddress.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d11_mc); (a,352); (t,112)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d11_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,352)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,112)) s =
                    num_of_wordlist mlkem_decompress_d11_table)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d11 l) /\
                  (!i. i < 256
                       ==> &0 <= ival(EL i (MAP decompress_d11 l)) /\
                           ival(EL i (MAP decompress_d11 l)) < &3329))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_DECOMPRESS_D11_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D11_CORRECT) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP; IVAL_DECOMPRESS_D11_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_poly_decompress_d11" subroutine_signatures)
    MLKEM_POLY_DECOMPRESS_D11_SUBROUTINE_CORRECT
    MLKEM_POLY_DECOMPRESS_D11_EXEC;;

let MLKEM_POLY_DECOMPRESS_D11_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a t (l:(11 word) list) pc returnaddress.
           LENGTH l = 256 /\
           ALL (nonoverlapping (r,512))
               [word pc,LENGTH mlkem_poly_decompress_d11_mc; a,352; t,112]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_poly_decompress_d11_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a; t] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a t r pc returnaddress /\
                        memaccess_inbounds e2 [a,352; t,112; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_DECOMPRESS_D11_EXEC);;
