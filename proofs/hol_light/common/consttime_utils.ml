(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "common/safety.ml";;

(* ========================================================================= *)
(* MEMACCESS_INBOUNDS_DEDUP_CONV: remove duplicate entries from the          *)
(* readable/writable range lists of memaccess_inbounds.                      *)
(*                                                                           *)
(* Workaround for mk_safety_spec producing duplicate entries.                *)
(* Remove once mk_safety_spec is fixed upstream in s2n-bignum.               *)
(* See: https://github.com/awslabs/s2n-bignum/issues/350                    *)
(* ========================================================================= *)

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
