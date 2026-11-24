(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the AVX-512 Keccak-f1600 routines,                *)
(* keccak_f1600_x1_avx512_asm and keccak_f1600_x4_avx512_asm.                *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/base.ml";;
needs "mlkem_native/x86_64/proofs/keccak_utils.ml";;

(* ------------------------------------------------------------------------- *)
(* KECCAK_BITBLAST_TAC with a cache, for permutations with many lane goals   *)
(* of the same form: several states computed in parallel, or loops that run  *)
(* the same code on other states. The goal with its lanes (the subterms      *)
(* EL n l of word type, in the order of find_terms) replaced by variables    *)
(* lane_0, lane_1, ... is proved by KECCAK_BITBLAST_TAC once, and the        *)
(* theorem is instantiated for each later goal of the same form.             *)
(* ------------------------------------------------------------------------- *)

let KECCAK_BITBLAST_CACHED_TAC =
  let cache = ref ([]:(term * thm) list) in
  let lane t =
    match t with
      Comb(Comb(Const("EL",_),_),_) ->
        (try fst(dest_type(type_of t)) = "word" with Failure _ -> false)
    | _ -> false
  and reserved v =
    let n = name_of v in String.length n > 5 && String.sub n 0 5 = "lane_" in
  fun (asl,w as gl) ->
    if exists reserved (frees w) then KECCAK_BITBLAST_TAC gl else
    let ls = find_terms lane w in
    let ilist = map2 (fun l k -> l,mk_var("lane_"^string_of_int k,type_of l))
                     ls (0--(length ls - 1)) in
    let w' = subst (map (fun (l,v) -> v,l) ilist) w in
    match (try Some(assoc w' !cache) with Failure _ ->
           try let th = prove(w',KECCAK_BITBLAST_TAC) in
               cache := (w',th) :: !cache; Some th
           with Failure _ -> None) with
      Some th -> ACCEPT_TAC(INST ilist th) gl
    | None -> KECCAK_BITBLAST_TAC gl;;

let KECCAK_AVX512_JOIN_EQ = prove
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

(* ------------------------------------------------------------------------- *)
(* The simulation of a round splits the value of each register written into  *)
(* its four 64-bit lanes, each a simple function of the lanes of the inputs  *)
(* of the instruction, and abbreviates each lane that is not a variable or a *)
(* constant as a new variable y<n>, so that the terms do not grow. At the    *)
(* end of the round the abbreviations are expanded, and each lane of the     *)
(* result is compared with that of keccak_round by KECCAK_BITBLAST_TAC.      *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_SUBWORD_COND_CONV th =
  let conv = DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV in
  fun tm ->
    let th1 = PART_MATCH (lhs o rand) th tm in
    CONV_RULE(RAND_CONV conv)
      (MP th1 (EQT_ELIM(conv(lhand(concl th1)))));;

let KECCAK_AVX512_LANE_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    REWR_CONV WORD_SUBWORD_XOR ORELSEC
    KECCAK_AVX512_SUBWORD_COND_CONV WORD_SUBWORD_NOT ORELSEC
    KECCAK_AVX512_SUBWORD_COND_CONV WORD_SUBWORD_DUPLICATE ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let KECCAK_AVX512_SPLIT = prove
 (`!y:int256.
        y = word_join
             (word_join (word_subword y (192,64):int64)
                        (word_subword y (128,64):int64):int128)
             (word_join (word_subword y (64,64):int64)
                        (word_subword y (0,64):int64):int128)`,
  BITBLAST_TAC);;

let keccak_avx512_atom t =
  is_var t ||
  (is_comb t && is_const(rator t) && name_of(rator t) = "word" &&
   is_numeral(rand t));;

let keccak_avx512_lanes_of t =
  let h,l = dest_binop `word_join:int128->int128->int256` t in
  let h1,h0 = dest_binop `word_join:int64->int64->int128` h
  and l1,l0 = dest_binop `word_join:int64->int64->int128` l in
  [h1;h0;l1;l0];;

let keccak_avx512_lane_form t =
  try forall keccak_avx512_atom (keccak_avx512_lanes_of t)
  with Failure _ -> false;;

let keccak_avx512_abbrev_count = ref 0;;

let KECCAK_AVX512_LANE_ABBREV_TAC k (asl,w) =
  let sv = mk_var("s"^string_of_int k,`:x86state`) in
  let is_target th =
    let c = concl th in
    is_eq c && type_of(lhs c) = `:int256` &&
    (match lhs c with
       Comb(Comb(Const("read",_),Const(n,_)),s) ->
         s = sv && String.length n > 3 && String.sub n 0 3 = "YMM"
     | _ -> false) &&
    not(keccak_avx512_lane_form(rhs c)) in
  match filter is_target (map snd asl) with
    [] -> ALL_TAC (asl,w)
  | th::_ ->
      let sth = CONV_RULE(RAND_CONV(BINOP_CONV(BINOP_CONV
                  KECCAK_AVX512_LANE_CONV)))
                 (SPEC (rhs(concl th)) KECCAK_AVX512_SPLIT) in
      let abv = setify(filter (not o keccak_avx512_atom)
                  (keccak_avx512_lanes_of(rhs(concl sth)))) in
      let mk1 e = (incr keccak_avx512_abbrev_count;
                   mk_eq(mk_var("y"^string_of_int(!keccak_avx512_abbrev_count),
                                `:int64`),e)) in
      (UNDISCH_THEN (concl th) (K ALL_TAC) THEN
       MP_TAC(TRANS th sth) THEN
       MAP_EVERY (fun e -> ABBREV_TAC(mk1 e)) abv THEN
       DISCH_TAC) (asl,w);;

(*** The simplification of the SIMD operations in the new value of a
 *** register, as SIMD_SIMPLIFY_TAC[] of common/mlkem_specs.ml
 ***)

let KECCAK_AVX512_SIMD_SIMPLIFY_TAC =
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

let keccak_avx512_lane_def c =
  is_eq c && is_var(rhs c) && String.sub (name_of(rhs c)) 0 1 = "y" &&
  not(can (find_term (fun t -> is_const t && name_of t = "read")) (lhs c));;

let KECCAK_AVX512_EXPAND_TAC (asl,w as gl) =
  PURE_REWRITE_TAC
   (map (SYM o snd) (filter (keccak_avx512_lane_def o concl o snd) asl)) gl;;

(*** The two functions of vpternlogq in the code, as the model computes
 *** them: the disjunction of the minterms selected by the immediate, those
 *** of the zero bits dropped
 ***)

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
 *** KECCAK_AVX512_SIMD_SIMPLIFY_TAC, with vpternlogq as XOR and AND-NOT first
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

(*** The branch back after the fourth round, as a condition on the
 *** iteration, and the new RIP as a word of a conditional address
 ***)

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
