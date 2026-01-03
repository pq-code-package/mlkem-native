(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of Keccac (https://keccak.team/keccak_specs_summary.html).  *)
(* ========================================================================= *)

needs "Library/words.ml";;

(*** Some abbreviations on top of the word library ***)

parse_as_prefix "~~";;
override_interface("~~",`word_not:N word->N word`);;
parse_as_infix("&&",(13,"right"));;
override_interface("&&",`word_and:N word->N word->N word`);;
parse_as_infix("||",(13,"right"));;
override_interface("^^",`word_xor:N word->N word->N word`);;
parse_as_infix("^^",(13,"right"));;
override_interface("||",`word_or:N word->N word->N word`);;

(*** Keccak round constants RC[i] for i = 0..23 ***)

let round_constants = define
 `round_constants:int64 list =
   [word 0x0000000000000001;
    word 0x0000000000008082;
    word 0x800000000000808a;
    word 0x8000000080008000;
    word 0x000000000000808b;
    word 0x0000000080000001;
    word 0x8000000080008081;
    word 0x8000000000008009;
    word 0x000000000000008a;
    word 0x0000000000000088;
    word 0x0000000080008009;
    word 0x000000008000000a;
    word 0x000000008000808b;
    word 0x800000000000008b;
    word 0x8000000000008089;
    word 0x8000000000008003;
    word 0x8000000000008002;
    word 0x8000000000000080;
    word 0x000000000000800a;
    word 0x800000008000000a;
    word 0x8000000080008081;
    word 0x8000000000008080;
    word 0x0000000080000001;
    word 0x8000000080008008]`;;

(*** An individual round, with input and output lists in row-major order ***)

let keccak_round = define
 `(keccak_round:int64 -> int64 list->int64 list) RCi Alist =
  let A00 = EL  0 Alist
  and A10 = EL  1 Alist
  and A20 = EL  2 Alist
  and A30 = EL  3 Alist
  and A40 = EL  4 Alist
  and A01 = EL  5 Alist
  and A11 = EL  6 Alist
  and A21 = EL  7 Alist
  and A31 = EL  8 Alist
  and A41 = EL  9 Alist
  and A02 = EL 10 Alist
  and A12 = EL 11 Alist
  and A22 = EL 12 Alist
  and A32 = EL 13 Alist
  and A42 = EL 14 Alist
  and A03 = EL 15 Alist
  and A13 = EL 16 Alist
  and A23 = EL 17 Alist
  and A33 = EL 18 Alist
  and A43 = EL 19 Alist
  and A04 = EL 20 Alist
  and A14 = EL 21 Alist
  and A24 = EL 22 Alist
  and A34 = EL 23 Alist
  and A44 = EL 24 Alist in
  let C0 = A00 ^^ A01 ^^ A02 ^^ A03 ^^ A04
  and C1 = A10 ^^ A11 ^^ A12 ^^ A13 ^^ A14
  and C2 = A20 ^^ A21 ^^ A22 ^^ A23 ^^ A24
  and C3 = A30 ^^ A31 ^^ A32 ^^ A33 ^^ A34
  and C4 = A40 ^^ A41 ^^ A42 ^^ A43 ^^ A44 in
  let D0 = C4 ^^ word_rol C1 1
  and D1 = C0 ^^ word_rol C2 1
  and D2 = C1 ^^ word_rol C3 1
  and D3 = C2 ^^ word_rol C4 1
  and D4 = C3 ^^ word_rol C0 1 in
  let At00 = A00 ^^ D0
  and At01 = A01 ^^ D0
  and At02 = A02 ^^ D0
  and At03 = A03 ^^ D0
  and At04 = A04 ^^ D0
  and At10 = A10 ^^ D1
  and At11 = A11 ^^ D1
  and At12 = A12 ^^ D1
  and At13 = A13 ^^ D1
  and At14 = A14 ^^ D1
  and At20 = A20 ^^ D2
  and At21 = A21 ^^ D2
  and At22 = A22 ^^ D2
  and At23 = A23 ^^ D2
  and At24 = A24 ^^ D2
  and At30 = A30 ^^ D3
  and At31 = A31 ^^ D3
  and At32 = A32 ^^ D3
  and At33 = A33 ^^ D3
  and At34 = A34 ^^ D3
  and At40 = A40 ^^ D4
  and At41 = A41 ^^ D4
  and At42 = A42 ^^ D4
  and At43 = A43 ^^ D4
  and At44 = A44 ^^ D4 in
  let B00 = word_rol At00  0
  and B01 = word_rol At30 28
  and B02 = word_rol At10  1
  and B03 = word_rol At40 27
  and B04 = word_rol At20 62
  and B10 = word_rol At11 44
  and B11 = word_rol At41 20
  and B12 = word_rol At21  6
  and B13 = word_rol At01 36
  and B14 = word_rol At31 55
  and B20 = word_rol At22 43
  and B21 = word_rol At02  3
  and B22 = word_rol At32 25
  and B23 = word_rol At12 10
  and B24 = word_rol At42 39
  and B30 = word_rol At33 21
  and B31 = word_rol At13 45
  and B32 = word_rol At43  8
  and B33 = word_rol At23 15
  and B34 = word_rol At03 41
  and B40 = word_rol At44 14
  and B41 = word_rol At24 61
  and B42 = word_rol At04 18
  and B43 = word_rol At34 56
  and B44 = word_rol At14  2 in
  [(B00 ^^ (~~B10 && B20)) ^^ RCi;
   B10 ^^ (~~B20 && B30);
   B20 ^^ (~~B30 && B40);
   B30 ^^ (~~B40 && B00);
   B40 ^^ (~~B00 && B10);
   B01 ^^ (~~B11 && B21);
   B11 ^^ (~~B21 && B31);
   B21 ^^ (~~B31 && B41);
   B31 ^^ (~~B41 && B01);
   B41 ^^ (~~B01 && B11);
   B02 ^^ (~~B12 && B22);
   B12 ^^ (~~B22 && B32);
   B22 ^^ (~~B32 && B42);
   B32 ^^ (~~B42 && B02);
   B42 ^^ (~~B02 && B12);
   B03 ^^ (~~B13 && B23);
   B13 ^^ (~~B23 && B33);
   B23 ^^ (~~B33 && B43);
   B33 ^^ (~~B43 && B03);
   B43 ^^ (~~B03 && B13);
   B04 ^^ (~~B14 && B24);
   B14 ^^ (~~B24 && B34);
   B24 ^^ (~~B34 && B44);
   B34 ^^ (~~B44 && B04);
   B44 ^^ (~~B04 && B14)]`;;

(*** Hence a recursive definition of n rounds starting from l ***)

let keccak = define
 `keccak 0 l = l /\
  keccak (n + 1) l = keccak_round (EL n round_constants) (keccak n l)`;;

(* ------------------------------------------------------------------------- *)
(* A few lemmas that are useful when reasoning about Keccak.                 *)
(* ------------------------------------------------------------------------- *)

let LENGTH_KECCAK = prove
 (`!A i. LENGTH A = 25 ==> LENGTH(keccak i A) = 25`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak; ADD1; keccak_round] THEN
  REPEAT LET_TAC THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_EQ_25 = prove
 (`!l:A list.
        LENGTH l = 25 <=>
        l = [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l;
             EL 5 l; EL 6 l; EL 7 l; EL 8 l; EL 9 l;
             EL 10 l; EL 11 l; EL 12 l; EL 13 l; EL 14 l;
             EL 15 l; EL 16 l; EL 17 l; EL 18 l; EL 19 l;
             EL 20 l; EL 21 l; EL 22 l; EL 23 l; EL 24 l]`,
  GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC(LAND_CONV(TOP_DEPTH_CONV num_CONV)) THEN
    REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC]);;

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
