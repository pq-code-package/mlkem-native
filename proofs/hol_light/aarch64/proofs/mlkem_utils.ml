(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* For BRUTE_FORCE_WITH and COND_REWRITE_CONV *)
needs "mlkem_native/common/mlkem_specs.ml";;

(* ------------------------------------------------------------------------- *)
(* Some convenient proof tools.                                              *)
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

let MEMORY_128_FROM_16_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(16*i) in
      READ_MEMORY_MERGE_CONV 3 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* This tactic repeated calls `f n with monotonically increasing values of n
   until the target PC matches one of the assumptions.

   The goal must be of the form `ensure arm ...`. Clauses constraining the PC
   must be of the form `read PC some_state = some_value`. *)
let MAP_UNTIL_TARGET_PC f n = fun (asl, w) ->
  let is_pc_condition = can (term_match [] `read PC some_state = some_value`) in
  (* We assume that the goal has the form
     `ensure arm (\s. ... /\ read PC s = some_value /\ ...)` *)
  let extract_target_pc_from_goal goal =
    let _, insts, _ = term_match [] `eventually arm (\s'. P) some_state` goal in
    insts
      |> rev_assoc `P: bool`
      |> conjuncts
      |> find is_pc_condition in
  (* Find PC-constraining assumption from the list of all assumptions. *)
  let extract_pc_assumption asl =
    try Some (find (is_pc_condition o concl o snd) asl |> snd |> concl) with find -> None in
  (* Check if there is an assumption constraining the PC to the target PC *)
  let has_matching_pc_assumption asl target_pc =
    match extract_pc_assumption asl with
     | None -> false
     | Some(asm) -> can (term_match [`returnaddress: 64 word`; `pc: num`] target_pc) asm in
  let target_pc = extract_target_pc_from_goal w in
  (* ALL_TAC if we reached the target PC, NO_TAC otherwise, so
     TARGET_PC_REACHED_TAC target_pc ORELSE SOME_OTHER_TACTIC
     is effectively `if !(target_pc_reached) SOME_OTHER_TACTIC` *)
  let TARGET_PC_REACHED_TAC target_pc = fun (asl, w) ->
    if has_matching_pc_assumption asl target_pc then
      ALL_TAC (asl, w)
    else
      NO_TAC (asl, w) in
  let rec core n (asl, w) =
    (TARGET_PC_REACHED_TAC target_pc ORELSE (f n THEN core (n + 1))) (asl, w)
  in
    core n (asl, w);;

(* ------------------------------------------------------------------------- *)
(* Tools for per-coefficient routines such as compression.                   *)
(* ------------------------------------------------------------------------- *)

(* Replace the assumption tm, which must have the form
 *
 *   read (memory :> bytes (a,512)) s = num_of_wordlist (l:int16 list)
 *
 * by 32 assumptions
 *
 *   read (memory :> bytes128 (word_add a (word (16 * k)))) s =
 *     word_join (... (EL (8 * k + 1) l) (EL (8 * k) l))
 *
 * one for each 128-bit load. Requires `LENGTH l = 256` in the assumptions. *)
let POLY_BYTES128_TAC tm =
  UNDISCH_TAC tm THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
  REWRITE_TAC[] THEN
  REPLICATE_TAC 3
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC;;

(* Prove a statement `!x:N word. val x < n ==> P x` about a single
 * coefficient by evaluating P (word k) for each k < n after unfolding
 * the definitions defs. Used to show that the word-level formula computed
 * by a SIMD lane agrees with a FIPS 203 operation such as compress_d4. *)
let PROVE_BY_COEFF_ENUMERATION defs tm =
  let x,bod = dest_forall tm in
  let ant,con = dest_imp bod in
  let k = mk_var("k",`:num`) in
  let wk = mk_comb(mk_mconst("word",mk_fun_ty `:num` (type_of x)),k) in
  let core = mk_forall(k,mk_imp(mk_binop `(<):num->num->bool` k (rand ant),
                                vsubst [wk,x] con)) in
  let core_th = prove(core,
    BRUTE_FORCE_WITH
     (CONV_TAC(REWRITE_CONV defs THENC DEPTH_CONV WORD_NUM_RED_CONV))) in
  prove(tm,
    GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPEC (lhand ant) core_th) THEN ASM_REWRITE_TAC[WORD_VAL]);;

(* Rewrite all assumptions with a conditional theorem th of the form
 *
 *   !x. P x ==> s x = t x
 *
 * discharging each side condition P (EL k l), for a numeral k, using the
 * assumption bnd_tm of the form `!i. i < n ==> P (EL i l)`. *)
let REWRITE_ASSUMS_WITH_EL_BOUND_TAC bnd_tm th =
  let derive_instance bth tm =
    let bth' = PART_MATCH rand bth tm in
    MP bth' (EQT_ELIM(NUM_REDUCE_CONV (lhand(concl bth')))) in
  UNDISCH_THEN bnd_tm (fun bth ->
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV
      (COND_REWRITE_CONV (derive_instance bth) th))) THEN
    ASSUME_TAC bth);;

needs "s2n_bignum/arm/proofs/consttime.ml";;
