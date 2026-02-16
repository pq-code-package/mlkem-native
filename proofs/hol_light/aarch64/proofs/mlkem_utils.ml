(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

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

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

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

(* ========================================================================= *)
(* MEMACCESS_INBOUNDS_DEDUP_CONV: remove duplicate entries from the          *)
(* readable/writable range lists of memaccess_inbounds.                      *)
(*                                                                           *)
(* Workaround for mk_safety_spec producing duplicate entries.                *)
(* Remove once mk_safety_spec is fixed upstream in s2n-bignum.               *)
(* See: https://github.com/awslabs/s2n-bignum/issues/350                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

(* EX P l depends only on set_of_list l *)
let EX_SET_OF_LIST = prove(
  `!(P:A->bool) l l'. set_of_list l = set_of_list l' ==> (EX P l <=> EX P l')`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM EX_MEM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[]);;

(* equal sets => equal memaccess_inbounds *)
let MEMACCESS_INBOUNDS_SET_OF_LIST = prove(
  `!e rr rr' wr wr'.
    set_of_list rr = set_of_list rr' /\
    set_of_list wr = set_of_list wr'
    ==> (memaccess_inbounds e rr wr <=> memaccess_inbounds e rr' wr')`,
  REWRITE_TAC[memaccess_inbounds] THEN REPEAT STRIP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `ev:uarch_event` THEN
  SPEC_TAC(`ev:uarch_event`,`ev:uarch_event`) THEN
  MATCH_MP_TAC uarch_event_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EX_SET_OF_LIST THEN ASM_REWRITE_TAC[]);;

(* conversion on set_of_list [concrete list] removing duplicates *)
let SET_OF_LIST_DEDUP_CONV : conv =
  let sol = set_of_list in
  let ins_ac = INSERT_AC in
  fun tm ->
    let sol_tm,l = dest_comb tm in
    if fst(dest_const sol_tm) <> "set_of_list" then failwith "not set_of_list" else
    let elts = dest_list l in
    let ety = type_of (hd elts) in
    let rec dedup seen = function
      | [] -> []
      | h::t -> if exists (aconv h) seen then dedup seen t
                else h :: dedup (h::seen) t in
    let elts' = dedup [] elts in
    if length elts' = length elts then REFL tm else
    let l' = mk_list(elts', ety) in
    let tm' = mk_comb(sol_tm, l') in
    let expand = REWRITE_CONV[sol] in
    let normalize = REWRITE_CONV[ins_ac] in
    let th1 = (expand THENC normalize) tm in
    let th2 = (expand THENC normalize) tm' in
    TRANS th1 (SYM th2);;

(* Combined: dedup both range lists of memaccess_inbounds *)
let MEMACCESS_INBOUNDS_DEDUP_CONV : conv =
  let sol = `set_of_list:(int64#num)list->(int64#num)->bool` in
  fun tm ->
    let mib,args = strip_comb tm in
    if fst(dest_const mib) <> "memaccess_inbounds" then
      failwith "MEMACCESS_INBOUNDS_DEDUP_CONV" else
    let [e;rr;wr] = args in
    let th_rr = SET_OF_LIST_DEDUP_CONV (mk_comb(sol,rr))
    and th_wr = SET_OF_LIST_DEDUP_CONV (mk_comb(sol,wr)) in
    let rr' = rand(rhs(concl th_rr))
    and wr' = rand(rhs(concl th_wr)) in
    if aconv rr rr' && aconv wr wr' then REFL tm else
    SPEC e (MATCH_MP MEMACCESS_INBOUNDS_SET_OF_LIST (CONJ th_rr th_wr));;
