(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared definitions and lemmas for compression/decompression proofs.       *)
(* ========================================================================= *)

needs "common/mlkem_specs.ml";;

(* ------------------------------------------------------------------------- *)
(* Bound lemmas for decompression (definitions in common/mlkem_specs.ml)     *)
(* ------------------------------------------------------------------------- *)

let IVAL_EQ_VAL = prove
 (`!w:N word. val w < 2 EXP (dimindex(:N) - 1) ==> ival w = &(val w)`,
  GEN_TAC THEN REWRITE_TAC[IVAL_VAL; MSB_VAL; GSYM NOT_LE] THEN
  SIMP_TAC[BITVAL_CLAUSES] THEN REWRITE_TAC[INT_MUL_RZERO; INT_SUB_RZERO]);;

let IVAL_DECOMPRESS_D4_BOUND = prove
 (`!x:4 word. &0 <= ival(decompress_d4 x) /\ ival(decompress_d4 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d4 (x:4 word)) < 2 EXP 15` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d4; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:4 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_4] THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `val(decompress_d4 (x:4 word)) < 3329` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d4; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:4 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_4] THEN ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d4 (x:4 word):16 word` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

let IVAL_DECOMPRESS_D5_BOUND = prove
 (`!x:5 word. &0 <= ival(decompress_d5 x) /\ ival(decompress_d5 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d5 (x:5 word)) < 2 EXP 15` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d5; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:5 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `val(decompress_d5 (x:5 word)) < 3329` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d5; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:5 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d5 (x:5 word):16 word` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

let IVAL_DECOMPRESS_D10_BOUND = prove
 (`!x:10 word. &0 <= ival(decompress_d10 x) /\ ival(decompress_d10 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d10 (x:10 word)) < 2 EXP 15` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d10; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:10 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `val(decompress_d10 (x:10 word)) < 3329` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d10; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:10 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d10 (x:10 word):16 word` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

let IVAL_DECOMPRESS_D11_BOUND = prove
 (`!x:11 word. &0 <= ival(decompress_d11 x) /\ ival(decompress_d11 x) < &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(decompress_d11 (x:11 word)) < 2 EXP 15` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d11; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:11 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `val(decompress_d11 (x:11 word)) < 3329` ASSUME_TAC THENL
  [REWRITE_TAC[decompress_d11; VAL_WORD; DIMINDEX_16] THEN
   MP_TAC(ISPEC `x:11 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPEC `decompress_d11 (x:11 word):16 word` IVAL_EQ_VAL) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT; LE_0] THEN ASM_ARITH_TAC);;

(* Unique decomposition of numbers with bounded low part *)
let NUM_BIT_DECOMPOSE_UNIQ = prove(`!a b t k. a < 2 EXP k ==> (a + 2 EXP k * b = t <=> (a = t MOD 2 EXP k /\ b = t DIV 2 EXP k))`,
    REPEAT STRIP_TAC THEN EQ_TAC THENL [
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES];
      STRIP_TAC THEN
      MP_TAC (SPECL [`t:num`; `2 EXP k`] DIVISION) THEN
      SIMP_TAC[EXP_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* Applies a conversion under an n-fold recursive application of a binary operator.
 * In our case, we are interested in applying a conversion to each of the 2^n 'lanes'
 * in an n-fold application of `word_join`; those naturally arise as word representations
 * of SIMD registers. *)
let BINOP_CONV_N n cv =
  let rec go depth i tm =
    if depth <= 0 then cv i tm
    else
      let half = 1 lsl (depth - 1) in
      COMB2_CONV (RAND_CONV (go (depth-1) (half + i))) (go (depth-1) i) tm in
  go n 0;;

(* General byte splitting for memory reads *)
let READ_BYTES_SPLIT_ANY =  prove(`read (bytes(a : int64,k+l)) s = t <=>
         read (bytes(a,k)) s = t MOD 2 EXP (8*k) /\ read (bytes(word_add a (word k), l)) s = t DIV 2 EXP (8*k)`,
      let bound = prove(`read (bytes (a : int64,k)) s < 2 EXP (8*k)`, REWRITE_TAC[READ_BYTES_BOUND]) in
      REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC [READ_BYTES_COMBINE] THEN
      REWRITE_TAC [MATCH_MP NUM_BIT_DECOMPOSE_UNIQ bound]
  );;

(* Checks if a type is the type of words of the specified bitwidth. *)
let is_word_type_n n ty =
  is_type ty &&
  let name, args = dest_type ty in
  name = "word" && length args = 1 &&
  Num.int_of_num (dest_finty (hd args)) = n;;

(* Looks for a word subterm of the specified bitwidth, and returns it upon success. Returns None otherwise.
 * We use this to locate `word (num_of_wordlist ls)` word subterms of bitwidth 16*b, which stand out for
 * their large bitwidth and represent the 16-nibble input to an iteration in the decompression loop. *)
let rec find_word_subterm_n n tm =
  if is_word_type_n n (type_of tm) then Some tm
  else if is_comb tm then
    match find_word_subterm_n n (rator tm) with
    | Some t -> Some t
    | None -> find_word_subterm_n n (rand tm)
  else if is_abs tm then find_word_subterm_n n (body tm)
  else None;;

(* Check if term is a bytes256 memory read *)
let is_bytes256_read tm =
  try let f,_ = dest_eq tm in
      let r,_ = dest_comb f in
      let rd,c = dest_comb r in
      name_of rd = "read" &&
      let _,b = dest_binary ":>" c in
      let op,_ = dest_comb b in
      fst(dest_const op) = "bytes256"
  with Failure _ -> false;;

(* Rewrite multiplications by 2-powers as shifts *)
let WORD_MUL_2EXP = map (fun i -> WORD_BLAST (subst [mk_small_numeral (1 lsl i), `n:num`; mk_small_numeral i, `l:num`]
  `word_mul (x : 16 word) (word n) = word_shl x l`)) (0--12);;

(* Rewrite multiplications by 2-powers as shifts *)
let WORD32_MUL_2EXP = map (fun i -> WORD_BLAST (subst [mk_small_numeral (1 lsl i), `n:num`; mk_small_numeral i, `l:num`]
  `word_mul (x : 32 word) (word n) = word_shl x l`)) (0--12);;

(* Rewrite multiplications by 2-power multiples of 3329 as combinations of shift and mul. *)
let WORD_MUL_2EXP_3329 = map (fun i -> WORD_BLAST (subst [mk_small_numeral (3329 * (1 lsl i)), `n:num`; mk_small_numeral i, `l:num`]
  `word_mul (x : 32 word) (word n) = word_mul (word_shl x l) (word 3329)`)) (1--4);;

(* Apply a conversion inside the expression computing a `x |-> round(x * 3329 / 2^15)`
 * used in the AVX2 decompression routines. *)
let ROUNDING_MUL_3329_CONV cv tm =
  let pat = `word_subword (word_add (word_ushr (word_mul (XXX:32 word) (word 3329 : 32 word)) 14) (word 1)) (1, 16) : 16 word` in
  let _ = term_match [] pat tm in
  (LAND_CONV (LAND_CONV (LAND_CONV (LAND_CONV cv)))) tm;;

(* ------------------------------------------------------------------------- *)
(* Shared lemmas for compression and decompression for all d                 *)
(* ------------------------------------------------------------------------- *)

(* DECOMPRESS_LANE_CONV: This conversion takes an index i=0,..,15
 * and assumes to be given a word expression involving
 * - A unique 16*b subword,
 * - Only bit-blastable operations, like join, subword, shift.
 * It then asserts via WORD_BLAST that the expression -- however complex it may be --
 * is equivalent to the extraction of the i-th b-bit nibble from the
 * 16*b subword, zero-extended and potentially with some shift applied.
 *
 * This is the workhorse conversion relating the very complex 8/16/32/64-bit granular
 * word expression encountered during the decompression routines to the underlying
 * b-bit nibbles in the input data. Instead of replicating the precise bit extraction
 * logic here, we just check via bitblasting that the result is what we want. *)
let DECOMPRESS_LANE_CONV l b i tm =
  let word_bits = 16 * b in
  match find_word_subterm_n word_bits tm with
    | Some t_var ->
        let b_ty = mk_finty (Num.num_of_int b) in
        let t_ty = mk_finty (Num.num_of_int word_bits) in
        let goal = mk_eq(tm,
          subst [mk_small_numeral l, `l:num`; mk_small_numeral (b*i), `pos:num`;
                 mk_small_numeral b, `b:num`; t_var, mk_var("t", mk_type("word",[t_ty]))]
            (inst [b_ty, `:B`; t_ty, `:T`]
              `word_shl (word_zx (word_subword (t : T word) (pos,b) : B word) : 32 word) l`)) in
        (* For debugging: *)
        (* let _ = print_term goal in *)
        WORD_BLAST goal
    | None -> failwith ("no " ^ string_of_int word_bits ^ "-bit word found")

(* A dummy definition allowing us to mark terms which have already been processed, to prevent
 * further processing. *)
let WRAP = new_definition `WRAP (x : bool) : bool = x`;;

(* DECOMPRESS_256_CONV: Rewrites 16 lanes in a 256-bit word_join tree, then wraps them. *)
let DECOMPRESS_256_CONV l b = RAND_CONV (BINOP_CONV_N 4 (ROUNDING_MUL_3329_CONV o (DECOMPRESS_LANE_CONV l b))) THENC (ONCE_REWRITE_CONV [GSYM WRAP]);;

(* ------------------------------------------------------------------------- *)
(* Shared lemmas for compression and decompression for d=5                   *)
(* ------------------------------------------------------------------------- *)

let MOD_2_64_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t MOD 2 EXP 64) : 64 word = word_subword (word t : 80 word) (0, 64)`, 
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:80)`] THEN
    MP_TAC (SPECL [`t:num`; `2`; `80`; `64`] MOD_MOD_EXP_MIN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC));;

let DIV_2_64_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t DIV 2 EXP 64) : 16 word = word_subword (word t : 80 word) (64, 16)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_16] THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:80)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]));;

let BASE_SIMPS_D5 = [MOD_2_64_AS_SUBWORD; DIV_2_64_AS_SUBWORD];;

let NUM_OF_WORDLIST_SPLIT_5_256 = prove(
  `!(l: (5 word) list). LENGTH l = 256 ==> 
       num_of_wordlist l = num_of_wordlist (MAP ((word:num->80 word) o num_of_wordlist)
          (list_of_seq (\i. SUB_LIST (16 * i, 16) l) 16)
       )`,
  REPEAT STRIP_TAC THEN
  (* Rewrite LHS l using SUBLIST_PARTITION *)
  UNDISCH_THEN `LENGTH (l : (5 word) list) = 256` (fun th -> 
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPECL [`16`; `16`; `l:'a list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (ISPECL [`ll: ((5 word) list) list`; `16`] (INST_TYPE [`:5`, `:N`; `:80`, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let READ_BYTES_SPLIT_64_16 = prove(`read (bytes (a,10)) (s : 64 word -> 8 word) = t <=>
     read (bytes (a,8)) s = t MOD 2 EXP 64 /\
     read (bytes (word_add a (word 8),2)) s = t DIV 2 EXP 64`, 
  REWRITE_TAC [REWRITE_RULE [ARITH_RULE `8 + 2 = 10`; ARITH_RULE `8 * 8 = 64`]
  (INST [`8`,`k:num`; `2`,`l:num`] READ_BYTES_SPLIT_ANY)]);;

let DIMINDEX_80 = DIMINDEX_CONV `dimindex (:80)`

let READ_WBYTES_SPLIT_64_16 = prove(`read (wbytes a) s = (t : 80 word) <=>
     read (bytes64 a) s = word (val t MOD 2 EXP 64) /\
     read (bytes16 (word_add a (word 8))) s = word (val t DIV 2 EXP 64)`,
  let VAL_WORD_80_MOD_64 = prove(`val (word (val (t : 80 word) MOD 2 EXP 64) : 64 word) = val t MOD 2 EXP 64`,
    SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 64 64 = 64`]) in
  let VAL_WORD_80_DIV_64 = prove (`val (word (val (t : 80 word) DIV 2 EXP 64) : 16 word) = val t DIV 2 EXP 64`,
    REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `t:80 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_80] THEN ARITH_TAC) in
  REWRITE_TAC[BYTES64_WBYTES; BYTES16_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES; DIMINDEX_80; ARITH_RULE `80 DIV 8 = 10`;
    READ_BYTES_SPLIT_64_16; DIMINDEX_64; DIMINDEX_16; DIMINDEX_80; ARITH_RULE `64 DIV 8 = 8`; ARITH_RULE `16 DIV 8 = 2`; 
    VAL_WORD_80_MOD_64; VAL_WORD_80_DIV_64]);;

let READ_WBYTES_SPLIT_64_16' = prove(`t < 2 EXP 80 ==> (read (wbytes a) s = (word t : 80 word) <=>
     read (bytes64 a) s = word (t MOD 2 EXP 64) /\
     read (bytes16 (word_add a (word 8))) s = word (t DIV 2 EXP 64))`,
  STRIP_TAC THEN REWRITE_TAC [READ_WBYTES_SPLIT_64_16] THEN IMP_REWRITE_TAC [VAL_WORD_EXACT; DIMINDEX_80]);;

let READ_MEMORY_WBYTES_SPLIT_64_16 = prove(`t < 2 EXP 80 ==> (read (memory :> wbytes a) s = (word t : 80 word) <=>
     read (memory :> bytes64 a) s = word (t MOD 2 EXP 64) /\
     read (memory :> bytes16 (word_add a (word 8))) s = word (t DIV 2 EXP 64))`,
  STRIP_TAC THEN REWRITE_TAC [READ_COMPONENT_COMPOSE] THEN IMP_REWRITE_TAC [READ_WBYTES_SPLIT_64_16']);;
  
let WORD_SUBWORD_NUM_OF_WORDLIST_16_5 = prove(`!ls:(5 word)list k.
    LENGTH ls = 16 /\ k < 16
    ==> word_subword (word (num_of_wordlist ls) : 80 word) (5*k,5) : 5 word = EL k ls`,
  let th = INST_TYPE [`:80`,`:KL`; `:5`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
  let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
  REWRITE_TAC [REWRITE_RULE[ARITH_RULE `80 = 5 * n <=> n = 16`; MESON[] `n = 16 /\ k < n <=> n = 16 /\ k < 16`] th]);;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D5 =
  let base = WORD_SUBWORD_NUM_OF_WORDLIST_16_5 in
  let mk k =
    let th = SPEC (mk_small_numeral k) (SPEC `ls:(5 word)list` base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0--15);;
  
let DIMINDEX_5 = DIMINDEX_CONV `dimindex (:5)`

(* ------------------------------------------------------------------------- *)
(* Shared lemmas for compression and decompression for d=10                  *)
(* ------------------------------------------------------------------------- *)

let MOD_2_128_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t MOD 2 EXP 128) : 128 word = word_subword (word t : 160 word) (0, 128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:160)`] THEN
    MP_TAC (SPECL [`t:num`; `2`; `160`; `128`] MOD_MOD_EXP_MIN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC));;

let DIV_2_128_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t DIV 2 EXP 128) : 32 word = word_subword (word t : 160 word) (128, 32)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_32] THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:160)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]));;

let BASE_SIMPS_D10 = [MOD_2_128_AS_SUBWORD; DIV_2_128_AS_SUBWORD];;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for 10-bit word lists                                       *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_WORDLIST_SPLIT_10_256 = prove(
  `!(l: (10 word) list). LENGTH l = 256 ==>
       num_of_wordlist l = num_of_wordlist (MAP ((word:num->160 word) o num_of_wordlist)
          (list_of_seq (\i. SUB_LIST (16 * i, 16) l) 16)
       )`,
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `LENGTH (l : (10 word) list) = 256` (fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPECL [`16`; `16`; `l:'a list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (ISPECL [`ll: ((10 word) list) list`; `16`] (INST_TYPE [`:10`, `:N`; `:160`, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let READ_BYTES_SPLIT_128_32 = prove(`read (bytes (a,20)) (s : 64 word -> 8 word) = t <=>
     read (bytes (a,16)) s = t MOD 2 EXP 128 /\
     read (bytes (word_add a (word 16),4)) s = t DIV 2 EXP 128`,
  REWRITE_TAC [REWRITE_RULE [ARITH_RULE `16 + 4 = 20`; ARITH_RULE `8 * 16 = 128`]
  (INST [`16`,`k:num`; `4`,`l:num`] READ_BYTES_SPLIT_ANY)]);;

let DIMINDEX_160 = DIMINDEX_CONV `dimindex (:160)`;;

let READ_WBYTES_SPLIT_128_32 = prove(`read (wbytes a) s = (t : 160 word) <=>
     read (bytes128 a) s = word (val t MOD 2 EXP 128) /\
     read (bytes32 (word_add a (word 16))) s = word (val t DIV 2 EXP 128)`,
  let VAL_WORD_160_MOD_128 = prove(`val (word (val (t : 160 word) MOD 2 EXP 128) : 128 word) = val t MOD 2 EXP 128`,
    SIMP_TAC[VAL_WORD; DIMINDEX_128; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 128 128 = 128`]) in
  let VAL_WORD_160_DIV_128 = prove (`val (word (val (t : 160 word) DIV 2 EXP 128) : 32 word) = val t DIV 2 EXP 128`,
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `t:160 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_160] THEN ARITH_TAC) in
  REWRITE_TAC[BYTES128_WBYTES; BYTES32_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES; DIMINDEX_160; ARITH_RULE `160 DIV 8 = 20`;
    READ_BYTES_SPLIT_128_32; DIMINDEX_128; DIMINDEX_32; ARITH_RULE `128 DIV 8 = 16`; ARITH_RULE `32 DIV 8 = 4`;
    VAL_WORD_160_MOD_128; VAL_WORD_160_DIV_128]);;

let READ_WBYTES_SPLIT_128_32' = prove(`t < 2 EXP 160 ==> (read (wbytes a) s = (word t : 160 word) <=>
     read (bytes128 a) s = word (t MOD 2 EXP 128) /\
     read (bytes32 (word_add a (word 16))) s = word (t DIV 2 EXP 128))`,
  STRIP_TAC THEN REWRITE_TAC [READ_WBYTES_SPLIT_128_32] THEN IMP_REWRITE_TAC [VAL_WORD_EXACT; DIMINDEX_160]);;

let READ_MEMORY_WBYTES_SPLIT_128_32 = prove(`t < 2 EXP 160 ==> (read (memory :> wbytes a) s = (word t : 160 word) <=>
     read (memory :> bytes128 a) s = word (t MOD 2 EXP 128) /\
     read (memory :> bytes32 (word_add a (word 16))) s = word (t DIV 2 EXP 128))`,
  STRIP_TAC THEN REWRITE_TAC [READ_COMPONENT_COMPOSE] THEN IMP_REWRITE_TAC [READ_WBYTES_SPLIT_128_32']);;

let WORD_SUBWORD_NUM_OF_WORDLIST_16_10 = prove(`!ls:(10 word)list k.
    LENGTH ls = 16 /\ k < 16
    ==> word_subword (word (num_of_wordlist ls) : 160 word) (10*k,10) : 10 word = EL k ls`,
  let th = INST_TYPE [`:160`,`:KL`; `:10`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
  let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
  REWRITE_TAC [REWRITE_RULE[ARITH_RULE `160 = 10 * n <=> n = 16`; MESON[] `n = 16 /\ k < n <=> n = 16 /\ k < 16`] th]);;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D10 =
  let base = WORD_SUBWORD_NUM_OF_WORDLIST_16_10 in
  let mk k =
    let th = SPEC (mk_small_numeral k) (SPEC `ls:(10 word)list` base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0--15);;

(* ------------------------------------------------------------------------- *)
(* Shared lemmas for compression and decompression for d=11                  *)
(* ------------------------------------------------------------------------- *)

let MOD_2_128_AS_SUBWORD_176 = CONV_RULE NUM_REDUCE_CONV (prove(`word (t MOD 2 EXP 128) : 128 word = word_subword (word t : 176 word) (0, 128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:176)`] THEN
    MP_TAC (SPECL [`t:num`; `2`; `176`; `128`] MOD_MOD_EXP_MIN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC));;

let DIV_2_128_MOD_32_AS_SUBWORD_176 = CONV_RULE NUM_REDUCE_CONV (prove(
  `word ((t DIV 2 EXP 128) MOD 2 EXP 32) : 32 word = word_subword (word t : 176 word) (128, 32)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 32 32 = 32`; MOD_MOD_REFL] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 176 (128 + 32) = 128 + 32`]));;

let DIV_2_160_AS_SUBWORD_176 = CONV_RULE NUM_REDUCE_CONV (prove(`word (t DIV 2 EXP 160) : 16 word = word_subword (word t : 176 word) (160, 16)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_16] THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:176)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]));;

let BASE_SIMPS_D11 = [MOD_2_128_AS_SUBWORD_176; DIV_2_128_MOD_32_AS_SUBWORD_176; DIV_2_160_AS_SUBWORD_176];;

(* Split 256 11-bit coefficients into 16 chunks of 16 coefficients each *)
let NUM_OF_WORDLIST_SPLIT_11_256 = prove(
  `!(l: (11 word) list). LENGTH l = 256 ==>
       num_of_wordlist l = num_of_wordlist (MAP ((word:num->176 word) o num_of_wordlist)
          (list_of_seq (\i. SUB_LIST (16 * i, 16) l) 16)
       )`,
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `LENGTH (l : (11 word) list) = 256` (fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPECL [`16`; `16`; `l:'a list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (ISPECL [`ll: ((11 word) list) list`; `16`] (INST_TYPE [`:11`, `:N`; `:176`, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

(* Triple split: 22 bytes = 16 + 4 + 2 *)
let READ_BYTES_SPLIT_128_32_16 = prove(`read (bytes (a,22)) (s : 64 word -> 8 word) = t <=>
     read (bytes (a,16)) s = t MOD 2 EXP 128 /\
     read (bytes (word_add a (word 16),4)) s = (t DIV 2 EXP 128) MOD 2 EXP 32 /\
     read (bytes (word_add a (word 20),2)) s = t DIV 2 EXP 160`,
  REWRITE_TAC [REWRITE_RULE [ARITH_RULE `16 + 6 = 22`; ARITH_RULE `8 * 16 = 128`]
    (INST [`16`,`k:num`; `6`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC [REWRITE_RULE [ARITH_RULE `4 + 2 = 6`; ARITH_RULE `8 * 4 = 32`]
    (INST [`4`,`k:num`; `2`,`l:num`] READ_BYTES_SPLIT_ANY)] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

let DIMINDEX_176 = DIMINDEX_CONV `dimindex (:176)`;;

(* 176-bit word splitting: 128+32+16 bytes *)
let READ_WBYTES_SPLIT_128_32_16 = prove(`read (wbytes a) s = (t : 176 word) <=>
     read (bytes128 a) s = word (val t MOD 2 EXP 128) /\
     read (bytes32 (word_add a (word 16))) s = word ((val t DIV 2 EXP 128) MOD 2 EXP 32) /\
     read (bytes16 (word_add a (word 20))) s = word (val t DIV 2 EXP 160)`,
  let VAL_WORD_176_MOD_128 = prove(`val (word (val (t : 176 word) MOD 2 EXP 128) : 128 word) = val t MOD 2 EXP 128`,
    SIMP_TAC[VAL_WORD; DIMINDEX_128; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 128 128 = 128`]) in
  let VAL_WORD_176_DIV_128_MOD_32 = prove (`val (word ((val (t : 176 word) DIV 2 EXP 128) MOD 2 EXP 32) : 32 word) = (val t DIV 2 EXP 128) MOD 2 EXP 32`,
    SIMP_TAC[VAL_WORD; DIMINDEX_32; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 32 32 = 32`]) in
  let VAL_WORD_176_DIV_160 = prove (`val (word (val (t : 176 word) DIV 2 EXP 160) : 16 word) = val t DIV 2 EXP 160`,
    REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `t:176 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_176] THEN ARITH_TAC) in
  REWRITE_TAC[BYTES128_WBYTES; BYTES32_WBYTES; BYTES16_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES; DIMINDEX_176; ARITH_RULE `176 DIV 8 = 22`;
    READ_BYTES_SPLIT_128_32_16; DIMINDEX_128; DIMINDEX_32; DIMINDEX_16; ARITH_RULE `128 DIV 8 = 16`; ARITH_RULE `32 DIV 8 = 4`; ARITH_RULE `16 DIV 8 = 2`;
    VAL_WORD_176_MOD_128; VAL_WORD_176_DIV_128_MOD_32; VAL_WORD_176_DIV_160]);;

let READ_WBYTES_SPLIT_128_32_16' = prove(`t < 2 EXP 176 ==> (read (wbytes a) s = (word t : 176 word) <=>
     read (bytes128 a) s = word (t MOD 2 EXP 128) /\
     read (bytes32 (word_add a (word 16))) s = word ((t DIV 2 EXP 128) MOD 2 EXP 32) /\
     read (bytes16 (word_add a (word 20))) s = word (t DIV 2 EXP 160))`,
  STRIP_TAC THEN REWRITE_TAC [READ_WBYTES_SPLIT_128_32_16] THEN IMP_REWRITE_TAC [VAL_WORD_EXACT; DIMINDEX_176]);;

let READ_MEMORY_WBYTES_SPLIT_128_32_16 = prove(`t < 2 EXP 176 ==> (read (memory :> wbytes a) s = (word t : 176 word) <=>
     read (memory :> bytes128 a) s = word (t MOD 2 EXP 128) /\
     read (memory :> bytes32 (word_add a (word 16))) s = word ((t DIV 2 EXP 128) MOD 2 EXP 32) /\
     read (memory :> bytes16 (word_add a (word 20))) s = word (t DIV 2 EXP 160))`,
  STRIP_TAC THEN REWRITE_TAC [READ_COMPONENT_COMPOSE] THEN IMP_REWRITE_TAC [READ_WBYTES_SPLIT_128_32_16']);;

(* Merge separate memory reads back into 176-bit word *)
let READ_WBYTES_MERGE_128_32_16 = prove(`
     read (bytes128 a) s = x0 : 128 word ==>
     read (bytes32 (word_add a (word 16))) s = x1 : 32 word ==>
     read (bytes16 (word_add a (word 20))) s = x2 : 16 word ==>
     read (wbytes a) s = (word_join (word_join x2 x1 : 48 word) x0) : 176 word`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [READ_WBYTES_SPLIT_128_32_16] THEN
  NUM_REDUCE_TAC THEN
  REWRITE_TAC BASE_SIMPS_D11 THEN
  ASM_REWRITE_TAC [] THEN
  BITBLAST_TAC);;

let READ_MEMORY_WBYTES_MERGE_128_32_16 = prove(`
     read (memory :> bytes128 a) s = x0 : 128 word ==>
     read (memory :> bytes32 (word_add a (word 16))) s = x1 : 32 word ==>
     read (memory :> bytes16 (word_add a (word 20))) s = x2 : 16 word ==>
     read (memory :> wbytes a) s = (word_join (word_join x2 x1 : 48 word) x0) : 176 word`,
  REWRITE_TAC [READ_COMPONENT_COMPOSE] THEN
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC [READ_WBYTES_MERGE_128_32_16]);;

(* Extract 11-bit coefficients from 176-bit packed representation *)
let WORD_SUBWORD_NUM_OF_WORDLIST_16_11 = prove(`!ls:(11 word)list k.
    LENGTH ls = 16 /\ k < 16
    ==> word_subword (word (num_of_wordlist ls) : 176 word) (11*k,11) : 11 word = EL k ls`,
  let th = INST_TYPE [`:176`,`:KL`; `:11`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
  let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
  REWRITE_TAC [REWRITE_RULE[ARITH_RULE `176 = 11 * n <=> n = 16`; MESON[] `n = 16 /\ k < n <=> n = 16 /\ k < 16`] th]);;

(* Instantiated cases for all 16 coefficient positions *)
let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D11 =
  let base = WORD_SUBWORD_NUM_OF_WORDLIST_16_11 in
  let mk k =
    let th = SPEC (mk_small_numeral k) (SPEC `ls:(11 word)list` base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0--15);;

(* Specialized version for 176-bit words with 11-bit subwords *)
let WORD_PACKED_EQ_D11 = prove(
 `!(x:176 word) (y:176 word).
    (x = y <=>
     !i. i < 16
         ==> word_subword x (11*i, 11) : (11) word =
             word_subword y (11*i, 11))`,
  REPEAT GEN_TAC THEN
  MP_TAC(INST [`11`,`l:num`; `16`,`k:num`]
    (INST_TYPE [`:176`,`:N`; `:11`,`:M`] WORD_PACKED_EQ)) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;
