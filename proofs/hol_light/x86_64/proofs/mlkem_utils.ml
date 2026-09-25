(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Utility definitions for ML-KEM x86_64 proofs.                            *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/consttime.ml";;

(* This tactic repeated calls `f n with monotonically increasing values of n
   until the target RIP matches one of the assumptions.

   The goal must be of the form `ensure x86 ...`. Clauses constraining the RIP
   must be of the form `read RIP some_state = some_value`. *)
let MAP_UNTIL_TARGET_PC f n = fun (asl, w) ->
  let is_pc_condition = can (term_match [] `read RIP some_state = some_value`) in
  (* We assume that the goal has the form
     `ensure x86 (\s. ... /\ read RIP s = some_value /\ ...)` *)
  let extract_target_pc_from_goal goal =
    let _, insts, _ = term_match [] `eventually x86 (\s'. P) some_state` goal in
    insts
      |> rev_assoc `P: bool`
      |> conjuncts
      |> find is_pc_condition in
  (* Find RIP-constraining assumption from the list of all assumptions. *)
  let extract_pc_assumption asl =
    try Some (find (is_pc_condition o concl o snd) asl |> snd |> concl) with find -> None in
  (* Check if there is an assumption constraining the RIP to the target RIP *)
  let has_matching_pc_assumption asl target_pc =
    match extract_pc_assumption asl with
     | None -> false
     | Some(asm) -> can (term_match [`returnaddress: 64 word`; `pc: num`] target_pc) asm in
  let target_pc = extract_target_pc_from_goal w in
  (* ALL_TAC if we reached the target RIP, NO_TAC otherwise, so
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

(* Like X86_SIM_TAC, but steps until the target RIP instead of taking an
   explicit list of step numbers. *)
let X86_SIM_UNTIL_TARGET_PC_TAC execth =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_UNTIL_TARGET_PC (fun n -> X86_STEPS_TAC execth [n]) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;
