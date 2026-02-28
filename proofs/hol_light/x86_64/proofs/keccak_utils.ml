(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak utilities for x86_64 proofs.                                       *)
(* ========================================================================= *)

needs "common/keccak_spec.ml";;

let rho8_constant = define
 `rho8_constant:int64 list =
   [word 0x0605040302010007;
    word 0x0E0D0C0B0A09080F;
    word 0x1615141312111017;
    word 0x1E1D1C1B1A19181F]`;;

let rho56_constant = define
 `rho56_constant:int64 list =
   [word 0x0007060504030201;
    word 0x080F0E0D0C0B0A09;
    word 0x1017161514131211;
    word 0x181F1E1D1C1B1A19]`;;

(* ------------------------------------------------------------------------- *)
(* Some custom normalization for logical equivalence and conjunction, which  *)
(* is enough to handle the shallow differences in various ways of expressing *)
(* Keccak-related operations, to avoid the overkill of using a SAT solver.   *)
(* ------------------------------------------------------------------------- *)

let KECCAK_BITBLAST_TAC =
  let IFF_NOT_CONV =
    let pth = TAUT
     `((~p <=> q) <=> ~(p <=> q)) /\
      ((p <=> ~q) <=> ~(p <=> q))` in
    GEN_REWRITE_CONV REDEPTH_CONV [pth; NOT_CLAUSES; EQ_CLAUSES] in
  let [conv_e;conv_l;conv_r; conv_1e;conv_1r;
       conv_e1;conv_l1;conv_r1; conv_ee; conv_11; conv_t] =
    map (fun tm -> GEN_REWRITE_CONV I [TAUT tm])
   [`((p <=> q1) <=> (p <=> q2)) = (q1 <=> q2)`;
    `((p1 <=> q1) <=> (p2 <=> q2)) = (p1 <=> (q1 <=> (p2 <=> q2)))`;
    `((p1 <=> q1) <=> (p2 <=> q2)) = (p2 <=> (p1 <=> q1) <=> q2)`;
    `(p <=> (p <=> q2)) = q2`;
    `(p <=> (p2 <=> q2)) = (p2 <=> (p <=> q2))`;
    `((p <=> q1) <=> p) = q1`;
    `((p1 <=> q1) <=> p) = (p1 <=> (q1 <=> p))`;
    `((p1 <=> q1) <=> p) = (p <=> (p1 <=> q1))`;
    `(p <=> p) <=> T`;
    `(p <=> q) <=> (q <=> p)`;
    `(p <=> T) <=> p`] in
  let rec IFF_MERGE_CONV tm =
    match tm with
      Comb(Comb(e,Comb(Comb(Const("=",_),p1),q1)),
           Comb(Comb(Const("=",_),p2),q2)) ->
          if p1 = p2 then (conv_e THENC IFF_MERGE_CONV) tm
          else if p1 < p2 then (conv_l THENC IFF_RAND_CONV) tm
          else (conv_r THENC IFF_RAND_CONV) tm
    | Comb(Comb(e,p),Comb(Comb(Const("=",_),p2),q2)) ->
          if p = p2 then conv_1e tm
          else if p < p2 then REFL tm
          else (conv_1r THENC IFF_RAND_CONV) tm
    | Comb(Comb(e,Comb(Comb(Const("=",_),p1),q1)),p) ->
          if p = p1 then conv_e1 tm
          else if p1 < p then (conv_l1 THENC IFF_RAND_CONV) tm
          else (conv_r1 THENC IFF_RAND_CONV) tm
    | Comb(Comb(e,p),q) ->
          if p = q then conv_ee tm
          else if p < q then REFL tm
          else conv_11 tm
    | _ -> REFL tm
  and IFF_RAND_CONV tm =
    let th = RAND_CONV IFF_MERGE_CONV tm in
    CONV_RULE(RAND_CONV(TRY_CONV conv_t)) th in
  let rec IFF_CANON_CONV tm =
    match tm with
      Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) ->
          (BINOP_CONV IFF_CANON_CONV THENC IFF_MERGE_CONV) tm
    | _ -> REFL tm in
  let rec IFF_ATOM_CONV conv tm =
    match tm with
      Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) ->
        BINOP_CONV (IFF_ATOM_CONV conv) tm
    | _ -> conv tm in
  let rec AND_ATOM_CONV conv tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r) ->
        BINOP_CONV (AND_ATOM_CONV conv) tm
    | _ -> conv tm in
  let rec IFF_NORM_CONV tm =
    match tm with
        Comb(Comb(Const("/\\",_),l),r) ->
          let th = AND_ATOM_CONV IFF_NORM_CONV tm in
          CONV_RULE (RAND_CONV CONJ_CANON_CONV) th
      | Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) ->
          let th = IFF_ATOM_CONV IFF_NORM_CONV tm in
          CONV_RULE (RAND_CONV IFF_CANON_CONV) th
      | Comb(Const("~",_),l) -> RAND_CONV IFF_NORM_CONV tm
      | _ -> REFL tm in
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[WORD_RULE `word_add x x = word_shl x 1`] THEN
  BITBLAST_THEN(K ALL_TAC) THEN
  CONV_TAC(AND_ATOM_CONV
   (BINOP_CONV(IFF_NOT_CONV THENC IFF_NORM_CONV) THENC
    GEN_REWRITE_CONV I [REFL_CLAUSE])) THEN
  REWRITE_TAC[] THEN NO_TAC;;

(* ------------------------------------------------------------------------- *)
(* Additional definitions and tactics used in the proof.                     *)
(* ------------------------------------------------------------------------- *)

let PC_OFFSET_CONV =
  GEN_REWRITE_CONV DEPTH_CONV [ARITH_RULE `(m + a) + b = m + (a + b)`] THENC
  NUM_REDUCE_CONV;;

let MEMORY_256_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes256(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 32*i) in
      READ_MEMORY_MERGE_CONV 2 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let WORD_SUBWORD_JOIN_EXTRACT_64 = prove
 (`!a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (0,64)):int64) = d /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (64,64)):int64) = c /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (128,64)):int64) = b /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (192,64)):int64) = a`,
 REPEAT GEN_TAC THEN
  BITBLAST_TAC);;

let WORD_SUBWORD_JOIN_EXTRACT_128 = prove
 (`!a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (0,128)):int128) = ((word_join c d):int128) /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (128,128)):int128) = ((word_join a b):int128)`,
   REPEAT GEN_TAC THEN
   BITBLAST_TAC);;
