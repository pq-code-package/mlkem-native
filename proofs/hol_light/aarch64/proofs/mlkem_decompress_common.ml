(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared lemmas for the AArch64 decompression proofs.                       *)
(* ========================================================================= *)

needs "mlkem_native/common/mlkem_specs.ml";;

(* ------------------------------------------------------------------------- *)
(* Decompress_d via a rounding doubling multiply-high (SQRDMULH).            *)
(*                                                                           *)
(* For a d-bit value x and a + b = 15 - d with b <= 3, we have               *)
(*                                                                           *)
(*   sqrdmulh(x << a, 3329 << b) = (2 * (x << a) * (3329 << b) + 2^15) >> 16 *)
(*                               = ((x * 3329 + 2^(d-1)) << (16-d)) >> 16    *)
(*                               = (x * 3329 + 2^(d-1)) >> d,                *)
(*                                                                           *)
(* which is Decompress_d(x). The conditions ensure that both operands are    *)
(* non-negative and below 2^15, so the multiplication does not saturate.     *)
(* How the shift 15 - d is split between the operands is up to the caller,   *)
(* so the lemma covers d = 4, 5, 10, 11 and any valid choice of a and b.     *)
(* ------------------------------------------------------------------------- *)

let WORD_2SMULH_ROUND_DECOMPRESS = prove
 (`!(x:N word) a b.
        dimindex(:N) + a + b = 15 /\ b <= 3
        ==> word_2smulh_round (word_shl (word_zx x) a : int16)
                              (word (3329 * 2 EXP b)) =
            word((val x * 3329 + 2 EXP (dimindex(:N) - 1)) DIV
                 2 EXP dimindex(:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN

  (*** The first operand is x * 2^a, and below 2^15 ***)

  SUBGOAL_THEN `val(x:N word) * 2 EXP a < 2 EXP 15` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP dimindex(:N) * 2 EXP a` THEN
    REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ; VAL_BOUND] THEN
    REWRITE_TAC[GSYM EXP_ADD; LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_shl (word_zx (x:N word)) a : int16) = val x * 2 EXP a`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_ZX_GEN; DIMINDEX_16] THEN
    SUBGOAL_THEN `val(x:N word) <= val x * 2 EXP a` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = m * 1`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `val(x:N word) MOD 2 EXP 16 = val x` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT;
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM] THEN
      MATCH_MP_TAC MOD_LT] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** The second operand is 3329 * 2^b, and below 2^15 ***)

  SUBGOAL_THEN `3329 * 2 EXP b < 2 EXP 15` ASSUME_TAC THENL
   [TRANS_TAC LET_TRANS `3329 * 2 EXP 3` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** So both signed values agree with the unsigned values ***)

  SUBGOAL_THEN
   `ival(word_shl (word_zx (x:N word)) a : int16) = &(val x * 2 EXP a) /\
    ival(word (3329 * 2 EXP b) : int16) = &(3329 * 2 EXP b)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(3329 * 2 EXP b) MOD 2 EXP 16 = 3329 * 2 EXP b`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) IVAL_EQ_VAL o lhand o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_16; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The core identity: cancel the common factor 2^(16-d) = 2^(1+a+b) ***)

  SUBGOAL_THEN
   `(2 * (val(x:N word) * 2 EXP a) * (3329 * 2 EXP b) + 2 EXP 15) DIV
    2 EXP 16 =
    (val x * 3329 + 2 EXP (dimindex(:N) - 1)) DIV 2 EXP dimindex(:N)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `2 EXP 16 = 2 EXP (1 + a + b) * 2 EXP dimindex(:N) /\
      2 EXP 15 = 2 EXP (1 + a + b) * 2 EXP (dimindex(:N) - 1)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 * (val(x:N word) * 2 EXP a) * (3329 * 2 EXP b) =
      2 EXP (1 + a + b) * (val x * 3329)`
    SUBST1_TAC THENL [REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN MATCH_MP_TAC DIV_MULT2 THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN

  (*** The result is at most 3329, so there is no saturation ***)

  SUBGOAL_THEN
   `(val(x:N word) * 3329 + 2 EXP (dimindex(:N) - 1)) DIV 2 EXP dimindex(:N)
    < 3330`
  ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN
    SPEC_TAC(`dimindex(:N)`,`d:num`) THEN
    SPEC_TAC(`val(x:N word)`,`v:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `2 EXP d = 2 * 2 EXP (d - 1)` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN

  REWRITE_TAC[word_2smulh_round; DIMINDEX_16] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_DIV;
              ARITH_RULE `16 - 1 = 15`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_16] THEN
  ABBREV_TAC
   `m = (val(x:N word) * 3329 + 2 EXP (dimindex(:N) - 1)) DIV
        2 EXP dimindex(:N)` THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  ASM_SIMP_TAC[INT_ARITH `~(&m:int < -- &32768)`; INT_GT; INT_OF_NUM_LT;
               ARITH_RULE `m < 3330 ==> ~(32767 < m)`; GSYM WORD_IWORD]);;

(* ------------------------------------------------------------------------- *)
(* Bounds for decompression (definitions in common/mlkem_specs.ml). These    *)
(* connect the HOL-Light specifications to the CBMC postconditions           *)
(* array_bound(r, 0, MLKEM_N, 0, MLKEM_Q).                                   *)
(* ------------------------------------------------------------------------- *)

let IVAL_DECOMPRESS_D4_BOUND = prove
 (`!x:4 word. &0 <= ival(decompress_d4 x) /\ ival(decompress_d4 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d4 (x:4 word)) < 3329` ASSUME_TAC THENL
   [REWRITE_TAC[decompress_d4; VAL_WORD; DIMINDEX_16] THEN
    MP_TAC(ISPEC `x:4 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_4] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d4 (x:4 word)` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

let IVAL_DECOMPRESS_D5_BOUND = prove
 (`!x:5 word. &0 <= ival(decompress_d5 x) /\ ival(decompress_d5 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d5 (x:5 word)) < 3329` ASSUME_TAC THENL
   [REWRITE_TAC[decompress_d5; VAL_WORD; DIMINDEX_16] THEN
    MP_TAC(ISPEC `x:5 word` VAL_BOUND) THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d5 (x:5 word)` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

let IVAL_DECOMPRESS_D10_BOUND = prove
 (`!x:10 word. &0 <= ival(decompress_d10 x) /\ ival(decompress_d10 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d10 (x:10 word)) < 3329` ASSUME_TAC THENL
   [REWRITE_TAC[decompress_d10; VAL_WORD; DIMINDEX_16] THEN
    MP_TAC(ISPEC `x:10 word` VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d10 (x:10 word)` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

let IVAL_DECOMPRESS_D11_BOUND = prove
 (`!x:11 word. &0 <= ival(decompress_d11 x) /\ ival(decompress_d11 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d11 (x:11 word)) < 3329` ASSUME_TAC THENL
   [REWRITE_TAC[decompress_d11; VAL_WORD; DIMINDEX_16] THEN
    MP_TAC(ISPEC `x:11 word` VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d11 (x:11 word)` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Generic word-list helpers, from s2n-bignum's common/mlkem_mldsa.ml.       *)
(* ------------------------------------------------------------------------- *)

(* Split a list of ncoeffs d-bit coefficients into chunks of chunk_size
 * coefficients, each viewed as one (d * chunk_size)-bit word. *)
let mk_split_theorem d ncoeffs chunk_size =
  let total = d * chunk_size in
  let nchunks = ncoeffs / chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  prove(
    subst [mk_small_numeral ncoeffs, `ncoeffs:num`;
           mk_small_numeral chunk_size, `cs:num`;
           mk_small_numeral nchunks, `nc:num`]
    (inst [d_ty, `:D`; total_ty, `:T`]
      `!(l: (D word) list). LENGTH l = ncoeffs ==>
         num_of_wordlist l =
         num_of_wordlist (MAP ((word:num->T word) o num_of_wordlist)
           (list_of_seq (\i. SUB_LIST (cs * i, cs) l) nc))`),
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN (subst [mk_small_numeral ncoeffs, `n:num`]
      (inst [d_ty, `:D`] `LENGTH (l : (D word) list) = n`)) (fun th ->
       GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [MATCH_MP (CONV_RULE NUM_REDUCE_CONV
           (ISPECL [mk_small_numeral chunk_size; mk_small_numeral nchunks;
                    `l:'a list`] SUBLIST_PARTITION)) th]
       THEN ASSUME_TAC th) THEN
    IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC
                                NUM_REDUCE_CONV)
      (ISPECL [inst [d_ty, `:D`] `ll: ((D word) list) list`;
               mk_small_numeral chunk_size]
        (INST_TYPE [d_ty, `:N`; total_ty, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
    CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
    ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
    ARITH_TAC);;

(* For a chunk of chunk_size d-bit coefficients viewed as one word, the
 * theorems `word_subword (word (num_of_wordlist ls)) (d*k,d) = EL k ls`
 * for k = 0, ..., chunk_size - 1. *)
let mk_subword_cases d chunk_size =
  let total = d * chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  let arith_simp =
    let lhs = mk_eq(mk_small_numeral total,
                mk_comb(mk_comb(`( * ):num->num->num`,
                  mk_small_numeral d), `n:num`)) in
    let rhs = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    ARITH_RULE (mk_eq(lhs, rhs)) in
  let meson_simp =
    let n_eq = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    let k_lt_n = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`), `n:num`) in
    let k_lt_cs = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`),
                    mk_small_numeral chunk_size) in
    MESON[] (mk_eq(mk_conj(n_eq, k_lt_n), mk_conj(n_eq, k_lt_cs))) in
  let base =
    let th = INST_TYPE [total_ty, `:KL`; d_ty, `:L`]
               WORD_SUBWORD_NUM_OF_WORDLIST in
    let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
    REWRITE_RULE[arith_simp; meson_simp] th in
  let mk k =
    let th = SPEC (mk_small_numeral k)
      (SPEC (inst [d_ty, `:L`] `ls:(L word)list`) base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0 -- (chunk_size - 1));;

(* ------------------------------------------------------------------------- *)
(* Matching the stores of a decode kernel to its input coefficients.         *)
(*                                                                           *)
(* The decode kernels store each vector of 8 output coefficients with one    *)
(* 16-byte store to r + off. After simulation, the stored value of a kernel  *)
(* that ends with `decompress` is a word_join tree of eight 16-bit lanes,    *)
(* the lowest lane holding output coefficient off / 2.                       *)
(*                                                                           *)
(* DECODE_JOIN_CONV lane_conv c applies lane_conv c, lane_conv (c + 1), ...  *)
(* to the lanes of such a tree, from the lowest one up. DECODE_STORE_RULE    *)
(* lane_conv n applies it to an assumption                                   *)
(*                                                                           *)
(*   read (memory :> bytes128 (word_add r (word off))) s = ...               *)
(*                                                                           *)
(* for a kernel whose loop iterations write n coefficients each, so that     *)
(* lane_conv receives the index of the coefficient within its iteration.     *)
(* Other assumptions are left unchanged.                                     *)
(* ------------------------------------------------------------------------- *)

let rec DECODE_JOIN_CONV lane_conv c tm =
  match tm with
    Comb(Comb(Const("word_join",_),h),l) ->
      let n = Num.int_of_num(dest_finty(hd(snd(dest_type(type_of l))))) / 16 in
      COMB2_CONV (RAND_CONV (DECODE_JOIN_CONV lane_conv (c + n)))
                 (DECODE_JOIN_CONV lane_conv c) tm
  | _ -> lane_conv c tm;;

let decode_store_address tm =
  let l,_ = dest_eq tm in
  let _,tmin,_ =
    term_match [] `read (memory :> bytes128 (addr:int64)) (s:armstate)` l in
  rev_assoc `addr:int64` tmin;;

let is_decode_output_store tm =
  try free_in `r:int64` (decode_store_address tm) with Failure _ -> false;;

let decode_store_offset tm =
  let addr = decode_store_address tm in
  if addr = `r:int64` then 0 else dest_small_numeral(rand(rand addr));;

let DECODE_STORE_RULE lane_conv n th =
  if not (is_decode_output_store (concl th)) then th else
  let c = (decode_store_offset (concl th) / 2) mod n in
  CONV_RULE (RAND_CONV (DECODE_JOIN_CONV lane_conv c)) th;;
