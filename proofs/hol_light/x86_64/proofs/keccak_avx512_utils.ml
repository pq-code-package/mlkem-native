(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the AVX-512 Keccak-f1600 routines, from the       *)
(* proofs in s2n-bignum of the same machine code: its                        *)
(* x86/proofs/utils/keccak_avx2.ml and keccak_avx512.ml, the tactics of      *)
(* its keccak_spec.ml that they use, and the tools of its                    *)
(* common/consttime.ml for proving correctness and safety in one             *)
(* theorem.                                                                  *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/base.ml";;
needs "mlkem_native/x86_64/proofs/keccak_utils.ml";;

(* ------------------------------------------------------------------------- *)
(* Some custom normalization for logical equivalence and conjunction, which  *)
(* is enough to handle the shallow differences in various ways of expressing *)
(* Keccak-related operations, to avoid the overkill of using a SAT solver.   *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_BITBLAST_TAC =
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
  MEMOIZED_BITBLAST_THEN(K ALL_TAC) THEN
  CONV_TAC(AND_ATOM_CONV
   (BINOP_CONV(IFF_NOT_CONV THENC IFF_NORM_CONV) THENC
    GEN_REWRITE_CONV I [REFL_CLAUSE])) THEN
  REWRITE_TAC[] THEN NO_TAC;;

(* ------------------------------------------------------------------------- *)
(* KECCAK_AVX512_BITBLAST_TAC with a cache, for permutations with many lane  *)
(* goals of the same form: several states computed in parallel, or loops     *)
(* that run the same code on other states. The goal with its lanes (the      *)
(* subterms EL n l of word type, in the order of find_terms) replaced by     *)
(* variables lane_0, lane_1, ... is proved by KECCAK_AVX512_BITBLAST_TAC     *)
(* once, and the theorem is instantiated for each later goal of the same     *)
(* form.                                                                     *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_BITBLAST_CACHED_TAC =
  let cache = ref ([]:(term * thm) list) in
  let lane t =
    match t with
      Comb(Comb(Const("EL",_),_),_) ->
        (try fst(dest_type(type_of t)) = "word" with Failure _ -> false)
    | _ -> false
  and reserved v =
    let n = name_of v in String.length n > 5 && String.sub n 0 5 = "lane_" in
  fun (asl,w as gl) ->
    if exists reserved (frees w) then KECCAK_AVX512_BITBLAST_TAC gl else
    let ls = find_terms lane w in
    let ilist = map2 (fun l k -> l,mk_var("lane_"^string_of_int k,type_of l))
                     ls (0--(length ls - 1)) in
    let w' = subst (map (fun (l,v) -> v,l) ilist) w in
    match (try Some(assoc w' !cache) with Failure _ ->
           try let th = prove(w',KECCAK_AVX512_BITBLAST_TAC) in
               cache := (w',th) :: !cache; Some th
           with Failure _ -> None) with
      Some th -> ACCEPT_TAC(INST ilist th) gl
    | None -> KECCAK_AVX512_BITBLAST_TAC gl;;

let KECCAK_AVX2_JOIN_EQ = prove
 (`!a b c d e f g h.
     word_join (word_join (a:int64) (b:int64):int128)
               (word_join (c:int64) (d:int64):int128):int256 =
     word_join (word_join (e:int64) (f:int64):int128)
               (word_join (g:int64) (h:int64):int128) <=>
     a = e /\ b = f /\ c = g /\ d = h`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `\x:int256. [word_subword x (192,64):int64; word_subword x (128,64);
                word_subword x (64,64); word_subword x (0,64)]`) THEN
  BETA_TAC THEN REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; CONS_11]);;

(*** The round counter in eax ***)

let KECCAK_AVX2_COUNTER = prove
 (`!i. i < 24
       ==> word_zx (word_sub (word_zx (word (24 - i):int64):int32) (word 1))
           :int64 = word (24 - (i + 1)) /\
           (val (word_sub (word_zx (word (24 - i):int64):int32) (word 1)) = 0
            <=> i + 1 = 24)`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let READ_MEMORY_BYTES256_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 32 <= m
        ==> read (memory :> bytes256(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES256_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP (8 * 32)`);
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** The twelve rows of the tables, as read in each round ***)

let KECCAK_AVX2_TABLE_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word tab,384)) s0 = n`)
           (concl th)
    then MP_TAC(end_itlist CONJ (map (fun k ->
           MATCH_MP READ_MEMORY_BYTES256_OF_NUM
            (CONJ th (ARITH_RULE(mk_binop `(<=):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_small_numeral(32 * k)) `32`)
               `384`))))
           (0--11)))
    else NO_TAC) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The simulation of a round splits the value of each register written into  *)
(* its four 64-bit lanes, each a simple function of the lanes of the inputs  *)
(* of the instruction, and abbreviates each lane that is not a variable or a *)
(* constant as a new variable y<n>, so that the terms do not grow. At the    *)
(* end of the round the abbreviations are expanded, and each lane of the     *)
(* result is compared with that of keccak_round by                           *)
(* KECCAK_AVX512_BITBLAST_TAC.                                               *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX2_JOIN32 = prove
 (`!x:N word p.
        word_join (word_subword x (p + 32,32):int32)
                  (word_subword x (p,32):int32):int64 =
        word_subword x (p,64)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
              DIMINDEX_32; DIMINDEX_64; ARITH_RULE `!n. MIN n n = n`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p + 32) + i - 32 = p + i /\ i - 32 < 32`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(*** Two adjacent 32-bit subwords (from VPBLENDD) as one of 64 bits ***)

let KECCAK_AVX2_JOIN32_CONV tm =
  match tm with
    Comb(Comb(Const("word_join",_),Comb(Comb(Const("word_subword",_),x),pa)),
         Comb(Comb(Const("word_subword",_),x'),pb)) when x = x' ->
      let a,_ = dest_pair pa and p,_ = dest_pair pb in
      if dest_small_numeral a <> dest_small_numeral p + 32 then
        failwith "KECCAK_AVX2_JOIN32_CONV" else
      let th = CONV_RULE(LAND_CONV(DEPTH_CONV NUM_ADD_CONV))
                (ISPECL [x; p] KECCAK_AVX2_JOIN32) in
      if lhs(concl th) = tm then th else failwith "KECCAK_AVX2_JOIN32_CONV"
  | _ -> failwith "KECCAK_AVX2_JOIN32_CONV";;

let KECCAK_AVX2_SUBWORD_COND_CONV th =
  let conv = DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV in
  fun tm ->
    let th1 = PART_MATCH (lhs o rand) th tm in
    CONV_RULE(RAND_CONV conv)
      (MP th1 (EQT_ELIM(conv(lhand(concl th1)))));;

let KECCAK_AVX2_LANE_CONV =
  TOP_DEPTH_CONV
   (KECCAK_AVX2_JOIN32_CONV ORELSEC
    REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    REWR_CONV WORD_SUBWORD_XOR ORELSEC
    KECCAK_AVX2_SUBWORD_COND_CONV WORD_SUBWORD_NOT ORELSEC
    KECCAK_AVX2_SUBWORD_COND_CONV WORD_SUBWORD_DUPLICATE ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let KECCAK_AVX2_SPLIT = prove
 (`!y:int256.
        y = word_join
             (word_join (word_subword y (192,64):int64)
                        (word_subword y (128,64):int64):int128)
             (word_join (word_subword y (64,64):int64)
                        (word_subword y (0,64):int64):int128)`,
  BITBLAST_TAC);;

let keccak_avx2_atom t =
  is_var t ||
  (is_comb t && is_const(rator t) && name_of(rator t) = "word" &&
   is_numeral(rand t));;

let keccak_avx2_lanes_of t =
  let h,l = dest_binop `word_join:int128->int128->int256` t in
  let h1,h0 = dest_binop `word_join:int64->int64->int128` h
  and l1,l0 = dest_binop `word_join:int64->int64->int128` l in
  [h1;h0;l1;l0];;

let keccak_avx2_lane_form t =
  try forall keccak_avx2_atom (keccak_avx2_lanes_of t)
  with Failure _ -> false;;

let keccak_avx2_lanes = ref 0;;

let KECCAK_AVX2_LANE_ABBREV_TAC k (asl,w) =
  let sv = mk_var("s"^string_of_int k,`:x86state`) in
  let is_target th =
    let c = concl th in
    is_eq c && type_of(lhs c) = `:int256` &&
    (match lhs c with
       Comb(Comb(Const("read",_),Const(n,_)),s) ->
         s = sv && String.length n > 3 && String.sub n 0 3 = "YMM"
     | _ -> false) &&
    not(keccak_avx2_lane_form(rhs c)) in
  match filter is_target (map snd asl) with
    [] -> ALL_TAC (asl,w)
  | th::_ ->
      let sth = CONV_RULE(RAND_CONV(BINOP_CONV(BINOP_CONV
                  KECCAK_AVX2_LANE_CONV)))
                 (SPEC (rhs(concl th)) KECCAK_AVX2_SPLIT) in
      let abv = setify(filter (not o keccak_avx2_atom)
                  (keccak_avx2_lanes_of(rhs(concl sth)))) in
      let mk1 e = (incr keccak_avx2_lanes;
                   mk_eq(mk_var("y"^string_of_int(!keccak_avx2_lanes),
                                `:int64`),e)) in
      (UNDISCH_THEN (concl th) (K ALL_TAC) THEN
       MP_TAC(TRANS th sth) THEN
       MAP_EVERY (fun e -> ABBREV_TAC(mk1 e)) abv THEN
       DISCH_TAC) (asl,w);;

(*** The simplification of the SIMD operations in the new value of a
 *** register, as SIMD_SIMPLIFY_TAC[] of common/mlkem_mldsa.ml
 ***)

let KECCAK_AVX2_SIMPLIFY_TAC =
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV
     (TOP_DEPTH_CONV
       (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
      DEPTH_CONV WORD_NUM_RED_CONV)) o
    check (can (term_match [] `read X (s:x86state):int256 = whatever`) o
           concl)));;

(*** The abbreviations of the lanes, to expand at the end. ABBREV_TAC also
 *** rewrites the older assumptions, so where a lane is computed twice the
 *** definition of the first abbreviation becomes y<new> = y<old>: the goal
 *** is rewritten with all the definitions until none applies, so their
 *** order does not matter.
 ***)

let keccak_avx2_lane_def c =
  is_eq c && is_var(rhs c) && String.sub (name_of(rhs c)) 0 1 = "y" &&
  not(can (find_term (fun t -> is_const t && name_of t = "read")) (lhs c));;

let KECCAK_AVX2_EXPAND_TAC (asl,w as gl) =
  PURE_REWRITE_TAC
   (map (SYM o snd) (filter (keccak_avx2_lane_def o concl o snd) asl)) gl;;

(*** The branch of the loop and the addresses of the tables ***)

let KECCAK_AVX2_BRANCH = prove
 (`!i. i < 24
       ==> (~(val (word_zx (word (24 - i):int64):int32) = val (word 1:int32))
            <=> i + 1 < 24)`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let KECCAK_AVX2_FOLD_TAC =
  IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD];;


let KECCAK_AVX512_TERNLOG_96 = WORD_BITWISE_RULE
 `word_or (word_and (word_not a) (word_and (word_not b) c))
   (word_or (word_and (word_not a) (word_and b (word_not c)))
     (word_or (word_and a (word_and (word_not b) (word_not c)))
              (word_and a (word_and b c)))):N word =
  word_xor a (word_xor b c)`;;

let KECCAK_AVX512_TERNLOG_D2 = WORD_BITWISE_RULE
 `word_or (word_and (word_not a) (word_and (word_not b) c))
   (word_or (word_and a (word_and (word_not b) (word_not c)))
     (word_or (word_and a (word_and b (word_not c)))
              (word_and a (word_and b c)))):N word =
  word_xor a (word_and (word_not b) c)`;;

(*** The simplification of the new value of a register after a step, as by
 *** KECCAK_AVX2_SIMPLIFY_TAC, with vpternlogq as XOR and AND-NOT first
 ***)

let KECCAK_AVX512_SIMPLIFY_TAC =
  let is_simd th =
    can (term_match [] `read X (s:x86state):int256 = whatever`) (concl th) ||
    can (term_match [] `read X (s:x86state):int128 = whatever`) (concl th) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV
     (GEN_REWRITE_CONV TOP_DEPTH_CONV
       [KECCAK_AVX512_TERNLOG_96; KECCAK_AVX512_TERNLOG_D2] THENC
      TOP_DEPTH_CONV
       (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
      DEPTH_CONV WORD_NUM_RED_CONV)) o
    check is_simd));;

(*** keccak_round of a list of 25 lanes, with the lets expanded ***)

let KECCAK_ROUND_EXPLICIT =
  let xs = map (fun k -> mk_var("x"^string_of_int k,`:int64`)) (0--24) in
  let tm = list_mk_comb(`keccak_round`,[`c:int64`; mk_list(xs,`:int64`)]) in
  GENL (`c:int64`::xs)
   ((REWRITE_CONV[keccak_round] THENC TOP_DEPTH_CONV let_CONV THENC
     TOP_DEPTH_CONV EL_CONV) tm);;

(* ------------------------------------------------------------------------- *)
(* The layout of the state in the registers. Both permutations keep lane k   *)
(* in register k at the start of each iteration of four rounds; each round   *)
(* writes the lanes back where pi took them from, so the lane in each        *)
(* register after rounds 1, 2 and 3 is given by keccak_avx512_layout1-3, and *)
(* after round 4, once the moves at its end have been made, by               *)
(* keccak_avx512_layout0 again. The lists give the lane in each register.    *)
(* ------------------------------------------------------------------------- *)

let keccak_avx512_layout0 = define
 `keccak_avx512_layout0 =
    [0;1;2;3;4;5;6;7;8;9;10;11;12;
     13;14;15;16;17;18;19;20;21;22;23;24]`;;

let keccak_avx512_layout1 = define
 `keccak_avx512_layout1 =
    [0;10;20;5;15;16;1;11;21;6;7;17;2;
     12;22;23;8;18;3;13;14;24;9;19;4]`;;

let keccak_avx512_layout2 = define
 `keccak_avx512_layout2 =
    [0;7;14;16;23;8;10;17;24;1;11;18;20;
     2;9;19;21;3;5;12;22;4;6;13;15]`;;

let keccak_avx512_layout3 = define
 `keccak_avx512_layout3 =
    [0;11;22;8;19;21;7;18;4;10;17;3;14;
     20;6;13;24;5;16;2;9;15;1;12;23]`;;

(* ------------------------------------------------------------------------- *)
(* The loop: rsi points to the round constants of the iteration, and rax to  *)
(* the end of the table, rsi + 192, so cmp rsi, rax ends the loop after six  *)
(* iterations.                                                               *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_RSI = prove
 (`!rc:int64 i.
     word_add (word_add rc (word (32 * i))) (word 32) =
     word_add rc (word (32 * (i + 1)))`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; WORD_ADD; WORD_ADD_ASSOC]);;

let KECCAK_AVX512_ZF = prove
 (`!rc:int64 i.
     i < 6
     ==> (val (word_sub (word_add (word_add rc (word (32 * i))) (word 32))
                        (word_add rc (word 192))) = 0 <=> i + 1 = 6)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `word_sub (word_add (word_add rc (word (32 * i))) (word 32))
             (word_add rc (word 192)):int64 =
    word_sub (word(32 * i + 32)) (word 192)`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    SPEC_TAC(`i:num`,`i:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV))]);;

let KECCAK_AVX512_BRANCH = prove
 (`!rc:int64 i.
     i < 6
     ==> (~(val (word_add (word_add rc (word (32 * i))) (word 32)) =
            val (word_add rc (word 192))) <=> i + 1 < 6)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_WORD_SUB_EQ_0] THEN
  ASM_SIMP_TAC[KECCAK_AVX512_ZF] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The simulation for the safety proofs.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The values in the SIMD registers do not matter for safety, and the
 *** simulation of a whole iteration with them would be slow, so they are
 *** dropped after each step
 ***)

let KECCAK_AVX512_SAFE_SIM_TAC execth n =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun k ->
    X86_STEPS_TAC execth [k] THEN
    DISCARD_ASSUMPTIONS_TAC
     (can (term_match [] `read X (s:x86state):int256 = y`) o concl))
   (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0];;

needs "s2n_bignum/x86/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* For the theorems that are correctness and safety in one ("FULL"): the     *)
(* events of the rest of an iteration reassociated to split off those of its *)
(* next round, and the branch back as a condition on the iteration.          *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_EVENTS_REASSOC_TAC =
  CONV_TAC(ONCE_DEPTH_CONV(fun t ->
    if is_eq t && is_var(lhs t) && name_of(lhs t) = "e2"
    then RAND_CONV(REWR_CONV(GSYM APPEND_ASSOC)) t
    else failwith "KECCAK_AVX512_EVENTS_REASSOC_TAC"));;

let KECCAK_AVX512_ZF_BRANCH = prove
 (`!rc:int64 i.
     i < 6
     ==> (~(val (word_sub (word_add (word_add rc (word (32 * i))) (word 32))
                          (word_add rc (word 192))) = 0) <=> i + 1 < 6)`,
  SIMP_TAC[KECCAK_AVX512_ZF] THEN ARITH_TAC);;

let KECCAK_AVX512_WORD_COND = prove
 (`!p x y. (if p then word x else word y):int64 = word(if p then x else y)`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness and safety in one theorem ("FULL"), by one symbolic           *)
(* execution: its precondition fixes the initial events e and its            *)
(* postcondition has the events as its last conjunct. EVENTS_SPLIT_TAC ctac  *)
(* splits that conjunct off a goal of such a postcondition, proving the rest *)
(* by ctac and the events by DISCHARGE_SAFETY_PROPERTY_TAC.                  *)
(* ENSURES_ANY_INITIAL and ENSURES_MONO_ALL give the correctness theorem     *)
(* from a FULL one: the initial events taken as any, and the precondition,   *)
(* postcondition and frame weakened.                                         *)
(* ------------------------------------------------------------------------- *)

let EVENTS_SPLIT_TAC ctac (asl,w as gl) =
  let cs = conjuncts w in
  let ev = last cs in
  if not (is_exists ev) then failwith "EVENTS_SPLIT_TAC" else
  let rest = list_mk_conj(butlast cs) in
  let th = CONJ_ACI_RULE(mk_eq(w,mk_conj(rest,ev))) in
  (GEN_REWRITE_TAC I [th] THEN
   CONJ_TAC THENL
    [ctac; ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC]) gl;;

let ENSURES_ANY_INITIAL = prove
 (`!(ev:S->A) (step:S->S->bool) P Q C.
        (!e. ensures step (\s. P s /\ ev s = e) Q C) ==> ensures step P Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let ENSURES_MONO_ALL = prove
 (`!(step:S->S->bool) P Q C P' Q' C'.
     ensures step P Q C
     ==> (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\
         (!s s'. C s s' ==> C' s s')
         ==> ensures step P' Q' C'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM_GEN THEN
  MAP_EVERY EXISTS_TAC [`C:S->S->bool`; `Q:S->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC `P:S->bool` THEN ASM_REWRITE_TAC[]);;
