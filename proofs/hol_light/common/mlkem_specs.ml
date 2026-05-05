(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* This file is a trimmed down version of s2n-bignum's mlkem_mldsa.ml file.  *)
(* Common specifications and tactics for ML-KEM x86 and arm proofs.          *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "Library/isum.ml";;

(* ------------------------------------------------------------------------- *)
(* The pure forms of forward and inverse NTT with no reordering.             *)
(* ------------------------------------------------------------------------- *)

let pure_forward_ntt = define
 `pure_forward_ntt f k =
    isum (0..127) (\j. f(2 * j + k MOD 2) *
                       &17 pow ((2 * k DIV 2 + 1) * j))
    rem &3329`;;

let pure_inverse_ntt = define
 `pure_inverse_ntt f k =
    (&3303 * isum (0..127) (\j. f(2 * j + k MOD 2) *
                                &1175 pow ((2 * j + 1) * k DIV 2)))
    rem &3329`;;

(* ------------------------------------------------------------------------- *)
(* Bit-reversing order as used in the standard/default order.                *)
(* ------------------------------------------------------------------------- *)

let bitreverse7 = define
 `bitreverse7(n) = val(word_reversefields 1 (word n:7 word))`;;

let bitreverse_pairs = define
 `bitreverse_pairs i = 2 * bitreverse7 (i DIV 2) + i MOD 2`;;

let reorder = define
 `reorder p (a:num->int) = \i. a(p i)`;;

let avx2_ntt_order = define
 `avx2_ntt_order i =
    bitreverse7(64 * (i DIV 64) + ((i MOD 64) DIV 16) + 4 * (i MOD 16))`;;

let avx2_ntt_order' = define
 `avx2_ntt_order' i =
    let j = bitreverse7 i in
    (64 * (j DIV 64) + 16 * (j MOD 4) + (j MOD 64) DIV 4)`;;

let avx2_reorder = define
 `avx2_reorder i =
    let r = (i DIV 16) MOD 2
    and q = 16 * (i DIV 32) + i MOD 16 in
    2 * avx2_ntt_order q + r`;;

let avx2_reorder' = define
 `avx2_reorder' i =
    let r = i MOD 2
    and q = avx2_ntt_order'(i DIV 2) in
    (q DIV 16) * 32 + r * 16 + q MOD 16`;;

(* ------------------------------------------------------------------------- *)
(* Conversion of each element of an array to Montgomery form with B = 2^16.  *)
(* ------------------------------------------------------------------------- *)

let tomont_3329 = define
 `tomont_3329 (a:num->int) = \i. (&2 pow 16 * a i) rem &3329`;;

let tomont_8380417 = define
 `tomont_8380417 (a:num->int) = \i. (&2 pow 32 * a i) rem &8380417`;;

(* ------------------------------------------------------------------------- *)
(* The multiplication cache for fast base multiplication                     *)
(* ------------------------------------------------------------------------- *)

let mulcache = define
 `mulcache f k =
   (f (2 * k + 1) * (&17 pow (2 * (bitreverse7 k) + 1))) rem &3329`;;

(* ------------------------------------------------------------------------- *)
(* The precise specs of the actual ARM code.                                 *)
(* ------------------------------------------------------------------------- *)

let inverse_ntt = define
 `inverse_ntt f k =
    (&512 * isum (0..127)
                 (\j. f(2 * bitreverse7 j + k MOD 2) *
                       &1175 pow ((2 * j + 1) * k DIV 2)))
    rem &3329`;;

let forward_ntt = define
 `forward_ntt f k =
    isum (0..127) (\j. f(2 * j + k MOD 2) *
                       &17 pow ((2 * bitreverse7 (k DIV 2) + 1) * j))
    rem &3329`;;

(* ------------------------------------------------------------------------- *)
(* The precise specs of the actual x86 code.                                 *)
(* ------------------------------------------------------------------------- *)

let avx2_forward_ntt = define
 `avx2_forward_ntt f k =
    let r = (k DIV 16) MOD 2
    and q = 16 * (k DIV 32) + k MOD 16 in
    isum (0..127) (\j. f(2 * j + r) *
                       &17 pow ((2 * avx2_ntt_order q + 1) * j))
    rem &3329`;;

let avx2_inverse_ntt = define
 `avx2_inverse_ntt f k =
    (&512 * isum (0..127)
                 (\j. f(avx2_ntt_order' j DIV 16 * 32 +
                        k MOD 2 * 16 +
                        avx2_ntt_order' j MOD 16) *
                      &1175 pow ((2 * j + 1) * k DIV 2)))
    rem &3329`;;
(* ------------------------------------------------------------------------- *)
(* Show how these relate to the "pure" ones.                                 *)
(* ------------------------------------------------------------------------- *)

let FORWARD_NTT = prove
 (`forward_ntt = reorder bitreverse_pairs o pure_forward_ntt`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; bitreverse_pairs; reorder] THEN
  REWRITE_TAC[forward_ntt; pure_forward_ntt] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x + i MOD 2) DIV 2 = x`] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL]);;

let INVERSE_NTT = prove
 (`inverse_ntt = tomont_3329 o pure_inverse_ntt o reorder bitreverse_pairs`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; bitreverse_pairs; reorder] THEN
  REWRITE_TAC[inverse_ntt; pure_inverse_ntt; tomont_3329] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x + i MOD 2) DIV 2 = x`] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN
  MAP_EVERY X_GEN_TAC [`a:num->int`; `i:num`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN CONV_TAC INT_REDUCE_CONV);;

let AVX2_FORWARD_NTT = prove
 (`avx2_forward_ntt = reorder avx2_reorder o pure_forward_ntt`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; avx2_reorder; reorder] THEN
  REWRITE_TAC[avx2_forward_ntt; pure_forward_ntt] THEN
  MAP_EVERY X_GEN_TAC [`x:num->int`; `k:num`] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `x MOD 2 DIV 2 = 0`; ADD_CLAUSES]);;

let AVX2_INVERSE_NTT = prove
 (`avx2_inverse_ntt = tomont_3329 o pure_inverse_ntt o reorder avx2_reorder'`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; avx2_reorder'; reorder] THEN
  REWRITE_TAC[avx2_inverse_ntt; pure_inverse_ntt; tomont_3329] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x + i MOD 2) DIV 2 = x`] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN
  MAP_EVERY X_GEN_TAC [`x:num->int`; `k:num`] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Explicit computation rules to evaluate mod-3329 powers/sums less naively. *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE7_CLAUSES = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [bitreverse7] THENC DEPTH_CONV WORD_NUM_RED_CONV)
 (map (curry mk_comb `bitreverse7` o mk_small_numeral) (0--127)));;

let FORWARD_NTT_ALT = prove
 (`forward_ntt f k =
   isum (0..127)
        (\j. f(2 * j + k MOD 2) *
             (&17 pow ((2 * bitreverse7 (k DIV 2) + 1) * j)) rem &3329)
    rem &3329`,
  REWRITE_TAC[forward_ntt] THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let AVX2_FORWARD_NTT_ALT = prove
 (`avx2_forward_ntt f k =
   let r = (k DIV 16) MOD 2
   and q = 16 * (k DIV 32) + k MOD 16 in
   isum (0..127)
        (\j. f(2 * j + r) *
             (&17 pow ((2 * avx2_ntt_order q + 1) * j)) rem &3329)
    rem &3329`,
  REWRITE_TAC[avx2_forward_ntt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let INVERSE_NTT_ALT = prove
 (`inverse_ntt f k =
    isum (0..127)
      (\j. f(2 * bitreverse7 j + k MOD 2) *
           (&512 *
            (&1175 pow ((2 * j + 1) * k DIV 2)) rem &3329)
           rem &3329) rem &3329`,
  REWRITE_TAC[inverse_ntt; GSYM ISUM_LMUL] THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let AVX2_INVERSE_NTT_ALT = prove
 (`avx2_inverse_ntt f k =
    isum (0..127)
      (\j. f(avx2_ntt_order' j DIV 16 * 32 +
             k MOD 2 * 16 +
             avx2_ntt_order' j MOD 16) *
           (&512 *
            (&1175 pow ((2 * j + 1) * k DIV 2)) rem &3329)
           rem &3329) rem &3329`,
  REWRITE_TAC[avx2_inverse_ntt; GSYM ISUM_LMUL] THEN
  MATCH_MP_TAC (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let FORWARD_NTT_CONV =
  GEN_REWRITE_CONV I [FORWARD_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let AVX2_NTT_ORDER_CLAUSES = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [avx2_ntt_order] THENC DEPTH_CONV WORD_NUM_RED_CONV THENC
  GEN_REWRITE_CONV I [BITREVERSE7_CLAUSES])
 (map (curry mk_comb `avx2_ntt_order` o mk_small_numeral) (0--127)));;

let AVX2_NTT_ORDER_CLAUSES' = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [avx2_ntt_order'] THENC DEPTH_CONV WORD_NUM_RED_CONV THENC
 DEPTH_CONV let_CONV THENC
 GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES] THENC NUM_REDUCE_CONV)
 (map (curry mk_comb `avx2_ntt_order'` o mk_small_numeral) (0--127)));;

let AVX2_FORWARD_NTT_CONV =
  GEN_REWRITE_CONV I [AVX2_FORWARD_NTT_ALT] THENC
  NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [AVX2_NTT_ORDER_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let INVERSE_NTT_CONV =
  GEN_REWRITE_CONV I [INVERSE_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let AVX2_INVERSE_NTT_CONV =
  GEN_REWRITE_CONV I [AVX2_INVERSE_NTT_ALT] THENC
  NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [AVX2_NTT_ORDER_CLAUSES'] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Abbreviate the Barrett reduction and multiplication and Montgomery        *)
(* reduction patterns in the code.                                           *)
(* ------------------------------------------------------------------------- *)

let barred = define
 `(barred:int16->int16) x =
  word_sub x
   (word_mul
    (iword
    ((ival
      (iword_saturate((&2 * ival x * &20159) div &65536):int16) + &1024) div
     &2048))
   (word 3329))`;;

let barred_x86 = define
 `(barred_x86:int16->int16) x =
  word_sub
   (x)
   (word_mul
     (word_ishr
       (word_subword
         (word_mul ((word_sx x):int32) (word 20159))
         (16,16))
       (10))
     (word 3329))`;;

let barmul = define
 `barmul (k,b) (a:int16):int16 =
  word_sub (word_mul a b)
           (word_mul (iword_saturate((&2 * ival a * k + &32768) div &65536))
                     (word 3329))`;;

let montred = define
   `(montred:int32->int16) x =
    word_subword
     (word_add
       (word_mul ((word_sx:int16->int32)
                    (word_mul (word_subword x (0,16)) (word 3327)))
                 (word 3329))
       x)
     (16,16)`;;

(* ------------------------------------------------------------------------- *)
(* For the x86 version of ML-KEM                                             *)
(* ------------------------------------------------------------------------- *)

let montmul_x86 = define
  `montmul_x86 (x : int16) (y :int16) =
   word_sub
     (word_subword (word_mul (word_sx y : int32) (word_sx x)) (16,16) : int16)
     (word_subword
        (word_mul (word 3329) (word_sx (word_mul y (word_mul (word 62209) x)) : int32))
        (16,16))
  `;;

let montmul_odd_x86 = prove
 (`word_neg(montmul_x86 x y) =
   word_sub
     (word_subword
        (word_mul (word 3329) (word_sx (word_mul y (word_mul (word 62209) x)) : int32))
        (16,16))
     (word_subword (word_mul (word_sx y : int32) (word_sx x)) (16,16) : int16)`,
  REWRITE_TAC[montmul_x86] THEN CONV_TAC WORD_RULE);;

let ntt_montmul = define
 `ntt_montmul (a:int32, b:int16) (x:int16) =
  word_sub
  (word_subword (word_mul (word_sx (x:int16)) a:int32) (16,16):int16)
  (word_subword
    (word_mul (word_sx
      ((word_mul (x:int16) b:int16)))
      (word 3329:int32))
    (16,16))`;;

let ntt_montmul_alt = prove
(`ntt_montmul (a:int32, b:int16) (x:int16) =
  word_sub
  (word_subword (word_mul a (word_sx (x:int16)):int32) (16,16):int16)
  (word_subword
    (word_mul
      (word 3329:int32)
      (word_sx ((word_mul b (x:int16):int16))))
    (16,16))`,
  REWRITE_TAC[ntt_montmul; WORD_MUL_SYM]);;


let ntt_montmul_add = prove
 (`word_add y (ntt_montmul (a, b) x) =
   word_sub
   (word_add
       (y)
       (word_subword (word_mul (word_sx (x:int16)) a:int32) (16,16):int16))
   (word_subword
     (word_mul (word_sx
       ((word_mul (x:int16) b:int16)))
       (word 3329:int32))
     (16,16))`,
  REWRITE_TAC[ntt_montmul] THEN CONV_TAC WORD_RULE);;

let ntt_montmul_sub = prove
 (`word_sub y (ntt_montmul (a, b) x) =
   word_add
   (word_sub
       (y)
       (word_subword (word_mul (word_sx (x:int16)) a:int32) (16,16):int16))
   (word_subword
     (word_mul (word_sx
       ((word_mul (x:int16) b:int16)))
       (word 3329:int32))
     (16,16))`,
  REWRITE_TAC[ntt_montmul] THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Compression and decompression spec definitions (FIPS 203)                 *)
(* ------------------------------------------------------------------------- *)

(* compress_d computes round(2^d * u / 3329)                                 *)
(* which equals (u * 2^d + 1664) DIV 3329 for u in 0..3328.                  *)
(* This is Compress_d from FIPS 203, Eq (4.7).                               *)

let compress_d4 = new_definition
  `compress_d4 (x:16 word) : 4 word =
   word((val x * 16 + 1664) DIV 3329)`;;

let compress_d5 = new_definition
  `compress_d5 (x:16 word) : 5 word =
   word((val x * 32 + 1664) DIV 3329)`;;

let compress_d10 = new_definition
  `compress_d10 (x:16 word) : 10 word =
   word((val x * 1024 + 1664) DIV 3329)`;;

let compress_d11 = new_definition
  `compress_d11 (x:16 word) : 11 word =
   word((val x * 2048 + 1664) DIV 3329)`;;

(* decompress_d computes round(3329 * u / 2^d)                               *)
(* which equals (u * 3329 + 2^(d-1)) DIV 2^d.                                *)
(* This is Decompress_d from FIPS 203, Eq (4.8).                             *)

let decompress_d4 = new_definition
  `decompress_d4 (x:4 word) : 16 word =
   word((val x * 3329 + 8) DIV 16)`;;

let decompress_d5 = new_definition
  `decompress_d5 (x:5 word) : 16 word =
   word((val x * 3329 + 16) DIV 32)`;;

let decompress_d10 = new_definition
  `decompress_d10 (x:10 word) : 16 word =
   word((val x * 3329 + 512) DIV 1024)`;;

let decompress_d11 = new_definition
  `decompress_d11 (x:11 word) : 16 word =
   word((val x * 3329 + 1024) DIV 2048)`;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for word lists                                              *)

let EL_SUB_LIST = prove(
 `!l:'a list. !i k n. i < n /\ k + n <= LENGTH l
   ==> EL i (SUB_LIST (k, n) l) = EL (k + i) l`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH; LE; ADD_EQ_0] THEN ARITH_TAC;
    REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[LT; SUB_LIST_CLAUSES; ADD_CLAUSES] THENL [
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
      REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `0`; `n':num`]) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EL; TL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`; `n':num`; `SUC n''`]) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* EL_SUB_LIST_CONV: Rewrites EL i (SUB_LIST (base,len) ls) to EL (base+i) ls
   Takes a LENGTH ls = n theorem and checks i < len before applying. *)
let EL_SUB_LIST_CONV len_thm tm =
  (* Parse EL i (SUB_LIST (base,len) ls) *)
  let i_tm,sublist_tm = dest_comb tm in
  let el_const,i = dest_comb i_tm in
  let sublist_pair,ls = dest_comb sublist_tm in
  let sublist_const,pair_tm = dest_comb sublist_pair in
  let base,len = dest_pair pair_tm in
  (* Check i < len *)
  let i_num = dest_numeral i and
      len_num = dest_numeral len in
  if i_num >= len_num then failwith "EL_SUB_LIST_CONV: index out of bounds" else
  (* Apply EL_SUB_LIST theorem and simplify *)
  let th1 = ISPECL [ls; i; base; len] EL_SUB_LIST in
  let th2 = REWRITE_RULE[len_thm] th1 in
  let th3 = MP th2 (EQT_ELIM(NUM_REDUCE_CONV (fst(dest_imp(concl th2))))) in
  (* Evaluate base + i *)
  CONV_RULE (RAND_CONV (LAND_CONV NUM_ADD_CONV)) th3;;

(* Derived from LENGTH_SUB_LIST *)
let LENGTH_SUB_LIST_0 = prove
 (`!n (l:'a list). n <= LENGTH l ==> LENGTH (SUB_LIST (0, n) l) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_ARITH_TAC);;

let SUB_LIST_SUB_LIST_0 = prove(
 `!k n m (l:'a list). k + n <= m /\ m <= LENGTH l
   ==> SUB_LIST (k, n) (SUB_LIST (0, m) l) = SUB_LIST (k, n) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; SUB_0] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n' < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (ISPECL [`SUB_LIST (0,m) l:'a list`; `n':num`; `k:num`; `n:num`] EL_SUB_LIST) THEN
  MP_TAC (ISPECL [`l:'a list`; `n':num`; `k:num`; `n:num`] EL_SUB_LIST) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
  SUBGOAL_THEN `k + n <= LENGTH (l:'a list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k + n <= MIN m (LENGTH (l:'a list))` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (ISPECL [`l:'a list`; `k + n':num`; `0`; `m:num`] EL_SUB_LIST) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Variant of SUB_LIST_TOPSPLIT with equality hypothesis *)
let SUB_LIST_SPLIT_EQ = prove
 (`!n r (l:'a list). n + r = LENGTH l
   ==> APPEND (SUB_LIST (0, n) l) (SUB_LIST (n, r) l) = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`l:'a list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC[ADD_SUB2]);;

let APPEND_ITLIST_APPEND_NIL = prove
 (`!(l:('a list) list) (x:'a list). APPEND (ITLIST APPEND l []) x = ITLIST APPEND l x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; APPEND] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN ASM_REWRITE_TAC[]);;

let LIST_OF_SEQ_EQ = prove
 (`!(f:num->'a) g n. (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[list_of_seq] THEN
  DISCH_TAC THEN BINOP_TAC THENL [
    FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC
  ]);;

let SUBLIST_PARTITION = prove
 (`!r s (l:'a list). LENGTH l = r * s ==>
       l = ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) l) s) []`,
  GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[MULT_CLAUSES; list_of_seq; ITLIST; LENGTH_EQ_NIL];

    REWRITE_TAC[list_of_seq; ITLIST_EXTRA; APPEND_NIL] THEN
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `SUB_LIST (0, r * s) l =
       ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) (SUB_LIST (0, r * s) l)) s) []:'a list`
      ASSUME_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LENGTH_SUB_LIST_0 THEN ASM_ARITH_TAC;
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `list_of_seq (\i. SUB_LIST (r * i, r) (SUB_LIST (0, r * s) l):'a list) s =
       list_of_seq (\i. SUB_LIST (r * i, r) l) s`
      ASSUME_TAC THENL [
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUB_LIST_SUB_LIST_0 THEN CONJ_TAC THENL [
        REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `APPEND (SUB_LIST (0, r * s) l) (SUB_LIST (r * s, r) l) = l:'a list`
      ASSUME_TAC THENL [
      MATCH_MP_TAC SUB_LIST_SPLIT_EQ THEN ASM_REWRITE_TAC[MULT_SUC] THEN ARITH_TAC;
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `SUB_LIST (0, r * s) l =
       ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) l) s) []:'a list`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `APPEND (SUB_LIST (0,r * s) l) (SUB_LIST (r * s,r) l) = l:'a list` THEN
    UNDISCH_TAC `SUB_LIST (0,r * s) l = ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i,r) l) s) []:'a list` THEN
    SIMP_TAC[APPEND_ITLIST_APPEND_NIL]
  ]);;

(* ------------------------------------------------------------------------- *)
(* From |- (x == y) (mod m) /\ P   to   |- (x == y) (mod n) /\ P             *)
(* ------------------------------------------------------------------------- *)

let WEAKEN_INTCONG_RULE =
  let prule = (MATCH_MP o prove)
   (`(x:int == y) (mod m) ==> !n. m rem n = &0 ==> (x == y) (mod n)`,
    REWRITE_TAC[INT_REM_EQ_0] THEN INTEGER_TAC)
  and conv = GEN_REWRITE_CONV I [INT_REM_ZERO; INT_REM_REFL] ORELSEC
             INT_REM_CONV
  and zth = REFL `&0:int` in
  let lrule n th =
    let th1 = SPEC (mk_intconst n) (prule th) in
    let th2 = LAND_CONV conv (lhand(concl th1)) in
    MP th1 (EQ_MP (SYM th2) zth) in
  fun n th ->
    let th1,th2 = CONJ_PAIR th in
    CONJ (lrule n th1) th2;;

(* ------------------------------------------------------------------------- *)
(* Unify modulus and conjoin a pair of (x == y) (mod m) /\ P thoerems.       *)
(* ------------------------------------------------------------------------- *)

let UNIFY_INTCONG_RULE th1 th2 =
  let p1 = dest_intconst (rand(rand(lhand(concl th1))))
  and p2 = dest_intconst (rand(rand(lhand(concl th2)))) in
  let d = gcd_num p1 p2 in
  CONJ (WEAKEN_INTCONG_RULE d th1) (WEAKEN_INTCONG_RULE d th2);;

(* ------------------------------------------------------------------------- *)
(* Process list of ineqequality into standard congbounds for atomic terms.   *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_INT_REDUCE_CONV =
  DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC DIMINDEX_CONV) THENC
  INT_REDUCE_CONV;;

let PROCESS_BOUND_ASSUMPTIONS =
  let cth = prove
   (`(ival x <= b <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b) /\
     (b <= ival x <=>
      b <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (ival(x:N word) > b <=>
      b + &1 <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (b > ival(x:N word) <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b - &1) /\
     (ival(x:N word) >= b <=>
      b <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (b >= ival(x:N word) <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b) /\
     (ival(x:N word) < b <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b - &1) /\
     (b < ival(x:N word) <=>
     b + &1 <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (abs(ival(x:N word)) <= b <=>
      --b <= ival x /\ ival x <= b) /\
     (abs(ival(x:N word)) < b <=>
      &1 - b <= ival x /\ ival x <= b - &1)`,
    REWRITE_TAC[IVAL_BOUND; INT_ARITH `x:int <= y - &1 <=> x < y`] THEN
    INT_ARITH_TAC)
  and pth = prove
   (`!l u (x:N word).
          l <= ival x /\ ival x <= u
          ==> (ival x == ival x) (mod &0) /\ l <= ival x /\ ival x <= u`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INTEGER_TAC) in
  let rule =
    MATCH_MP pth o
    CONV_RULE (BINOP2_CONV (LAND_CONV DIMINDEX_INT_REDUCE_CONV)
                           (RAND_CONV DIMINDEX_INT_REDUCE_CONV)) o
    GEN_REWRITE_RULE I [cth] in
  let rec process lfn ths =
    match ths with
      [] -> lfn
    | th::oths ->
          let lfn' =
            try let th' = rule th in
                let tm = rand(concl th') in
                if is_intconst (rand(rand tm)) && is_intconst (lhand(lhand tm))
                then (rand(lhand(rand tm)) |-> th') lfn
                else lfn
            with Failure _ -> lfn in
          process lfn' oths in
  process undefined;;

(* ------------------------------------------------------------------------- *)
(* Congruence-and-bound propagation, just recursion on the expression tree.  *)
(* ------------------------------------------------------------------------- *)

let CONGBOUND_CONST = prove
 (`!(x:N word) n.
        ival x = n
        ==> (ival x == n) (mod &0) /\ n <= ival x /\ ival x <= n`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INT_LE_REFL] THEN INTEGER_TAC);;

let CONGBOUND_ATOM = prove
 (`!x:N word. (ival x == ival x) (mod &0) /\
              --(&2 pow (dimindex(:N) - 1)) <= ival x /\
              ival x <= &2 pow (dimindex(:N) - 1) - &1`,
  GEN_TAC THEN REWRITE_TAC[INT_ARITH `x:int <= y - &1 <=> x < y`] THEN
  REWRITE_TAC[IVAL_BOUND] THEN INTEGER_TAC);;

let CONGBOUND_ATOM_GEN = prove
 (`!x:N word. abs(ival x) <= n
              ==> (ival x == ival x) (mod &0) /\
                  --n <= ival x /\ ival x <= n`,
  REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`] THEN INT_ARITH_TAC);;

let CONGBOUND_IWORD = prove
 (`!x. ((x == x') (mod p) /\ l <= x /\ x <= u)
       ==> --(&2 pow (dimindex(:N) - 1)) <= l /\
           u <= &2 pow (dimindex(:N) - 1) - &1
           ==> (ival(iword x:N word) == x') (mod p) /\
               l <= ival(iword x:N word) /\ ival(iword x:N word) <= u`,
  GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rand o rand o snd) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

let CONGBOUND_WORD_SX = prove
 (`!x:M word.
        ((ival x == x') (mod p) /\ l <= ival x /\ ival x <= u)
        ==> --(&2 pow (dimindex(:N) - 1)) <= l /\
            u <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_sx x:N word) == x') (mod p) /\
                l <= ival(word_sx x:N word) /\ ival(word_sx x:N word) <= u`,
  REWRITE_TAC[word_sx; CONGBOUND_IWORD]);;

let CONGBOUND_WORD_NEG = prove
 (`!x:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux)
        ==> --lx <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_neg x) == --x') (mod p) /\
                --ux <= ival(word_neg x) /\
                ival(word_neg x) <= --lx`,
  GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_neg x:N word) = --(ival x)` SUBST1_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN WORD_ARITH_TAC;
    ASM_SIMP_TAC[INTEGER_RULE
     `(x:int == x') (mod p) ==> (--x == --x') (mod p)`] THEN
    ASM_ARITH_TAC]);;

let CONGBOUND_WORD_ADD = prove
 (`!x y:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod p) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1)) <= lx + ly /\
            ux + uy <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_add x y) == x' + y') (mod p) /\
                lx + ly <= ival(word_add x y) /\
                ival(word_add x y) <= ux + uy`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD_IMODULAR; imodular] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_ADD] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_WORD_SUB = prove
 (`!x y:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod p) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1)) <= lx - uy /\
            ux - ly <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_sub x y) == x' - y') (mod p) /\
                lx - uy <= ival(word_sub x y) /\
                ival(word_sub x y) <= ux - ly`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SUB_IMODULAR; imodular] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_SUB] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_WORD_MUL = prove
 (`!x y:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod p) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1))
            <= min (lx * ly) (min (lx * uy) (min (ux * ly) (ux * uy))) /\
            max (lx * ly) (max (lx * uy) (max (ux * ly) (ux * uy)))
            <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_mul x y) == x' * y') (mod p) /\
                min (lx * ly) (min (lx * uy) (min (ux * ly) (ux * uy)))
                <= ival(word_mul x y) /\
                ival(word_mul x y)
                <= max (lx * ly) (max (lx * uy) (max (ux * ly) (ux * uy)))`,
  let lemma = prove
     (`l:int <= x /\ x <= u
       ==> !a. a * l <= a * x /\ a * x <= a * u \/
               a * u <= a * x /\ a * x <= a * l`,
      MESON_TAC[INT_LE_NEGTOTAL; INT_LE_LMUL;
                INT_ARITH `a * x:int <= a * y <=> --a * y <= --a * x`]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(ASSUME_TAC o SPEC `ival(x:N word)` o MATCH_MP lemma) THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN DISCH_THEN(fun th ->
        ASSUME_TAC(SPEC `ly:int` th) THEN ASSUME_TAC(SPEC `uy:int` th)) THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_MUL] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_BARRED = prove
 (`!a a' l u.
        ((ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u)
        ==> (ival(barred a) == a') (mod &3329) /\
            -- &1664 <= ival(barred a) /\ ival(barred a) <= &1664`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[barred] THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub a (word_mul b (word n)) = iword(ival a - ival b * &n)`] THEN
  REPEAT(W(fun (asl,w) ->
     let t = hd(sort free_in
        (find_terms (can (term_match [] `ival(iword x)`)) w)) in
     let th = PART_MATCH (lhand o rand) IVAL_IWORD t in
     MP_TAC th THEN REWRITE_TAC[DIMINDEX_16] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ANTS_TAC THENL [BOUNDER_TAC[]; DISCH_THEN SUBST1_TAC])) THEN
  MATCH_MP_TAC(MESON[]
   `(x == k) (mod n) /\
    (a <= x /\ x <= b) /\
    (a <= x /\ x <= b ==> ival(iword x:int16) = x)
    ==> (ival(iword x:int16) == k) (mod n) /\
        a <= ival(iword x:int16) /\ ival(iword x:int16) <= b`) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a - x * n:int == a') (mod n) <=> (a == a') (mod n)`] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `a:int16` IVAL_BOUND);
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD] THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_BARRED_X86 = prove
 (`!a a' l u.
        ((ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u)
        ==> (ival(barred_x86 a) == a') (mod &3329) /\
            &0 <= ival(barred_x86 a) /\ ival(barred_x86 a) <= &6657`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[barred_x86] THEN
  REWRITE_TAC[WORD_BLAST
   `word_ishr (word_subword (x:int32) (16,16):int16) 10 =
    word_sx(word_ishr x 26)`] THEN
  REWRITE_TAC[WORD_RULE
   `word_sub a (word_mul b (word n)) = iword(ival a - ival b * &n)`] THEN
  REWRITE_TAC[BITBLAST_RULE
   `ival(word_sx(word_ishr (x:int32) 26):int16) = ival(word_ishr x 26)`] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular; IVAL_WORD_ISHR] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_16; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  SUBGOAL_THEN
   `ival(iword(ival(a:int16) * &20159):int32) = ival a * &20159`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `a:int16` IVAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a - x * p:int == a') (mod p) <=> (a == a') (mod p)`] THEN
  MP_TAC(ISPEC `a:int16` IVAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC
 );;

let CONGBOUND_BARMUL = prove
 (`!a a' l u.
        ((ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u)
        ==> !k b. abs(k) <= &32767 /\
                  (max (abs l) (abs u) *
                   abs(&65536 * ival b - &6658 * k) + &109150207) div &65536
                  <= &32767
                  ==> (ival(barmul(k,b) a) == a' * ival b) (mod &3329) /\
                      --(max (abs l) (abs u) *
                         abs(&65536 * ival b - &6658 * k) + &109084672)
                         div &65536
                      <= ival(barmul(k,b) a) /\
                      ival(barmul(k,b) a) <=
                      (max (abs l) (abs u) * abs(&65536 * ival b - &6658 * k) +
                       &109150207) div &65536`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[barmul] THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN ASM BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_mul a b) (word_mul (iword k) (word c)) =
    iword(ival a * ival b - &c * k)`] THEN
  MATCH_MP_TAC(MESON[]
   `(x == k) (mod n) /\
    (a <= x /\ x <= b ==> ival(iword x:int16) = x) /\
    (a <= x /\ x <= b)
    ==> (ival(iword x:int16) == k) (mod n) /\
        a <= ival(iword x:int16) /\ ival(iword x:int16) <= b`) THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(a:int == a') (mod n) ==> (a * b - n * c == a' * b) (mod n)`] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH
   `&65536 * l + &109084672 <= a * (&65536 * b - &6658 * k) /\
    a * (&65536 * b - &6658 * k) <= &65536 * u - &109084672
    ==> l <= a * b - &3329 * (&2 * a * k + &32768) div &65536 /\
        a * b - &3329 * (&2 * a * k + &32768) div &65536 <= u`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `abs(y):int <= --x ==> x <= y`);
    MATCH_MP_TAC(INT_ARITH `abs(y):int <= x ==> y <= x`)] THEN
  REWRITE_TAC[INT_ABS_MUL] THEN
  TRANS_TAC INT_LE_TRANS
   `max (abs l) (abs u) * abs(&65536 * ival(b:int16) - &6658 * k)` THEN
  ASM_SIMP_TAC[INT_LE_RMUL; INT_ABS_POS; INT_ARITH
   `l:int <= x /\ x <= u ==> abs x <= max (abs l) (abs u)`] THEN
  CONV_TAC INT_ARITH);;

let CONGBOUND_MONTMUL_X86 = prove
 (`!x y. ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux) /\
         ((ival y == y') (mod &3329) /\ ly <= ival y /\ ival y <= uy)
         ==> (ival(montmul_x86 x y) ==
              &(inverse_mod 3329 65536) * x' * y') (mod &3329) /\
             (min (lx * ly) (min (lx * uy) (min (ux * ly) (ux * uy))) -
              &109081343) div &65536 <= ival(montmul_x86 x y) /\
             ival(montmul_x86 x y)
             <= (max (lx * ly) (max (lx * uy) (max (ux * ly) (ux * uy))) +
                 &109150207) div &65536`,
  let lemma = prove
   (`l:int <= x /\ x <= u
     ==> !a. a * l <= a * x /\ a * x <= a * u \/
             a * u <= a * x /\ a * x <= a * l`,
    MESON_TAC[INT_LE_NEGTOTAL; INT_LE_LMUL;
              INT_ARITH `a * x:int <= a * y <=> --a * y <= --a * x`])
  and ilemma = prove
   (`!x:int32. ival(word_subword x (16,16):int16) = ival x div &2 pow 16`,
    REWRITE_TAC[GSYM DIMINDEX_16; GSYM IVAL_WORD_ISHR] THEN
    GEN_TAC THEN REWRITE_TAC[DIMINDEX_16] THEN BITBLAST_TAC) in
  let mainlemma = prove
   (`!x:int32 y:int32.
          (ival x == ival y) (mod (&2 pow 16))
          ==> &2 pow 16 *
              ival(word_sub (word_subword x (16,16))
                            (word_subword y (16,16)):int16) =
              ival(word_sub x y)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH
     `b rem &2 pow 16 = &0 /\ a = &2 pow 16 * b div &2 pow 16 ==> a = b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_SUB_IMODULAR; imodular; INT_REM_EQ_0] THEN
      SIMP_TAC[INT_DIVIDES_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE;
      AP_TERM_TAC THEN REWRITE_TAC[GSYM ilemma] THEN AP_TERM_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_REM_EQ]) THEN
    SIMP_TAC[INT_REM_IVAL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
    BITBLAST_TAC) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `(&2:int) pow 16`; `&3329:int`] (INTEGER_RULE
 `!d e n:int. (e * d == &1) (mod n)
              ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 16 * l <= &2 pow 16 * x`] THEN
  REWRITE_TAC[montmul_x86] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE
   `!x:int16 y:int16.
        iword(ival y * ival(iword(c * ival x):int16)):int16 =
        iword(c * ival x * ival y)`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) mainlemma o
   lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[GSYM INT_REM_EQ; INT_REM_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    SIMP_TAC[INT_REM_IVAL_IWORD; DIMINDEX_16; ARITH; DIMINDEX_32] THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
     `(a * b:int == &1) (mod p) ==> (y * x == a * b * x * y) (mod p)`) THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM IWORD_INT_SUB]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_32; ARITH] THEN BOUNDER_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ONCE_REWRITE_TAC[INT_ARITH `ival x * ival y = ival y * ival x`] THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(x:int == x') (mod p) /\ (y == y') (mod p)
    ==> (x * y - p * z == x' * y') (mod p)`] THEN
  MATCH_MP_TAC(INT_ARITH
  `(l <= p /\ p <= u) /\ (&65535 - c <= q /\ q <= b)
   ==> &2 pow 16 * (l - b) div &65536 <= p - q /\
       p - q <= &2 pow 16 * (u + c) div &65536`) THEN
  CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(ASSUME_TAC o SPEC `ival(x:int16)` o MATCH_MP lemma) THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN DISCH_THEN(fun th ->
        ASSUME_TAC(SPEC `ly:int` th) THEN ASSUME_TAC(SPEC `uy:int` th)) THEN
  ASM_INT_ARITH_TAC);;

let MONTRED_LEMMA = prove
 (`!x. &2 pow 16 * ival(montred x) =
       ival(word_add
         (word_mul (word_sx(iword(ival x * &3327):int16)) (word 3329)) x)`,
  GEN_TAC THEN REWRITE_TAC[montred] THEN REWRITE_TAC[WORD_BLAST
   `word_subword (x:int32) (0,16):int16 = word_sx x`] THEN
  REWRITE_TAC[IWORD_INT_MUL; GSYM word_sx; GSYM WORD_IWORD] THEN
  REWRITE_TAC[WORD_BLAST `(word_sx:int32->int16) x = word_zx x`] THEN
  CONV_TAC INT_REDUCE_CONV THEN MATCH_MP_TAC(BITBLAST_RULE
   `word_and x (word 65535):int32 = word 0
    ==> &65536 * ival(word_subword x (16,16):int16) = ival x`) THEN
  REWRITE_TAC[BITBLAST_RULE
   `word_and x (word 65535):int32 = word 0 <=> word_zx x:int16 = word 0`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_ADD o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o lhand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`] THEN
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM DIVIDES_MOD; DIMINDEX_16] THEN
  CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b + 1 == 0) (mod d) ==> d divides ((x * a) * b + x)`) THEN
  REWRITE_TAC[CONG] THEN ARITH_TAC);;

let CONGBOUND_MONTRED = prove
 (`!a a' l u.
      (ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u
      ==> --(&2038398976) <= l /\ u <= &2038402304
          ==> (ival(montred a) == &(inverse_mod 3329 65536) * a') (mod &3329) /\
              (l - &109084672) div &2 pow 16 <= ival(montred a) /\
              ival(montred a) <= &1 + (u + &109081343) div &2 pow 16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `(&2:int) pow 16`; `&3329:int`] (INTEGER_RULE
 `!d e n:int. (e * d == &1) (mod n)
              ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 16 * l <= &2 pow 16 * x`] THEN
  REWRITE_TAC[MONTRED_LEMMA] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_mul a b) c = iword(ival a * ival b + ival c)`] THEN
  ASM_SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
   lhand o rator o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  W(MP_TAC o C ISPEC IVAL_BOUND o
    rand o funpow 3 lhand o rand o lhand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a * p + x:int == y) (mod p) <=> (x == y) (mod p)`] THEN
  ASM_INT_ARITH_TAC);;

let CONGBOUND_NTT_MONTMUL = prove
 (`!x x' lx ux.
       ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux)
       ==> !a b. --(&32768) <= ival a /\
                 ival a <= &32767 /\
                 (&3329 * ival b) rem &65536 = ival a rem &65536
                 ==> (ival(ntt_montmul (a,b) x) ==
                     &(inverse_mod 3329 65536) * ival a * x')
                     (mod &3329) /\
                     (min (ival a * lx) (ival a * ux) - &109081343)
                     div &65536 <= ival(ntt_montmul (a,b) x) /\
                     ival(ntt_montmul (a,b) x) <=
                     (max (ival a * lx) (ival a * ux) + &109150208)
                     div &2 pow 16`,
  let lemma = prove
   (`l:int <= x /\ x <= u
     ==> !a. a * l <= a * x /\ a * x <= a * u \/
             a * u <= a * x /\ a * x <= a * l`,
    MESON_TAC[INT_LE_NEGTOTAL; INT_LE_LMUL;
              INT_ARITH `a * x:int <= a * y <=> --a * y <= --a * x`])
  and ilemma = prove
   (`!x:int32. ival(word_subword x (16,16):int16) = ival x div &2 pow 16`,
    REWRITE_TAC[GSYM DIMINDEX_16; GSYM IVAL_WORD_ISHR] THEN
    GEN_TAC THEN REWRITE_TAC[DIMINDEX_16] THEN BITBLAST_TAC) in
  let mainlemma = prove
   (`!x:int32 y:int32.
          (ival x == ival y) (mod (&2 pow 16))
          ==> &2 pow 16 *
              ival(word_sub (word_subword x (16,16))
                            (word_subword y (16,16)):int16) =
              ival(word_sub x y)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH
     `b rem &2 pow 16 = &0 /\ a = &2 pow 16 * b div &2 pow 16 ==> a = b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_SUB_IMODULAR; imodular; INT_REM_EQ_0] THEN
      SIMP_TAC[INT_DIVIDES_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE;
      AP_TERM_TAC THEN REWRITE_TAC[GSYM ilemma] THEN AP_TERM_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_REM_EQ]) THEN
    SIMP_TAC[INT_REM_IVAL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
    BITBLAST_TAC) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `(&2:int) pow 16`; `&3329:int`] (INTEGER_RULE
 `!d e n:int. (e * d == &1) (mod n)
              ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 16 * l <= &2 pow 16 * x`] THEN
  REWRITE_TAC[ntt_montmul] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_32; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  W(MP_TAC o PART_MATCH (lhand o rand) mainlemma o
   lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[GSYM INT_REM_EQ; INT_REM_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
    SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH_LE; ARITH_LT] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_IWORD_CONG;
                GSYM DIMINDEX_16] THEN
    REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[INT_MUL_SYM];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM IWORD_INT_SUB]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[DIMINDEX_32; ARITH] THEN ASM BOUNDER_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH_LE; ARITH_LT] THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(x:int == x') (mod p) ==> (x * a - q * p == a * x') (mod p)`] THEN
  REWRITE_TAC[GSYM(INT_REDUCE_CONV `(&2:int) pow 16`)] THEN
  MATCH_MP_TAC(INT_ARITH
  `(l <= p /\ p <= u) /\ (&65535 - c <= q /\ q <= b)
   ==> &2 pow 16 * (l - b) div &2 pow 16 <= p - q /\
       p - q <= &2 pow 16 * (u + c) div &2 pow 16`) THEN
  CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ival(a:int32)` o
    MATCH_MP lemma o CONJUNCT2) THEN
  INT_ARITH_TAC);;

let CONCL_BOUNDS_RULE =
  CONV_RULE(BINOP2_CONV
          (LAND_CONV(RAND_CONV DIMINDEX_INT_REDUCE_CONV))
          (BINOP2_CONV
           (LAND_CONV DIMINDEX_INT_REDUCE_CONV)
           (RAND_CONV DIMINDEX_INT_REDUCE_CONV)));;

let SIDE_ELIM_RULE th =
  MP th (EQT_ELIM(DIMINDEX_INT_REDUCE_CONV(lhand(concl th))));;

let rec ASM_CONGBOUND_RULE lfn tm =
    try apply lfn tm with Failure _ ->
    match tm with
      Comb(Const("word",_),n) when is_numeral n ->
        let th1 = ISPEC tm CONGBOUND_CONST in
        let th2 = WORD_RED_CONV(lhand(lhand(snd(strip_forall(concl th1))))) in
        MATCH_MP th1 th2
    | Comb(Const("iword",_),n) when is_intconst n ->
        let th0 = WORD_IWORD_CONV tm in
        let th1 = ISPEC (rand(concl th0)) CONGBOUND_CONST in
        let th2 = WORD_RED_CONV(lhand(lhand(snd(strip_forall(concl th1))))) in
        SUBS[SYM th0] (MATCH_MP th1 th2)
    | Comb(Comb(Const("barmul",_),kb),t) ->
        let ktm,btm = dest_pair kb and th0 = ASM_CONGBOUND_RULE lfn t in
        let th0' = WEAKEN_INTCONG_RULE (num 3329) th0 in
        let th1 = SPECL [ktm;btm] (MATCH_MP CONGBOUND_BARMUL th0') in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("montmul_x86",_),ltm),rtm) ->
        let lth = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn ltm)
        and rth = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn rtm) in
        let th1 = MATCH_MP CONGBOUND_MONTMUL_X86
                   (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(th1)
    | Comb(Const("barred",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn t) in
        MATCH_MP CONGBOUND_BARRED th1
    | Comb(Const("barred_x86",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn t) in
        MATCH_MP CONGBOUND_BARRED_X86 th1
    | Comb(Const("montred",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn t) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE(MATCH_MP CONGBOUND_MONTRED th1))
    | Comb(Comb(Const("ntt_montmul",_),ab),t) ->
        let atm,btm = dest_pair ab and th0 = ASM_CONGBOUND_RULE lfn t in
        let th0' = WEAKEN_INTCONG_RULE (num 3329) th0 in
        let th1 = SPECL [atm;btm] (MATCH_MP CONGBOUND_NTT_MONTMUL th0') in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Const("word_sx",_),t) ->
        let th0 = ASM_CONGBOUND_RULE lfn t in
        let tyin = type_match
         (type_of(rator(rand(lhand(funpow 4 rand (snd(dest_forall
            (concl CONGBOUND_WORD_SX)))))))) (type_of(rator tm)) [] in
        let th1 = MATCH_MP (INST_TYPE tyin CONGBOUND_WORD_SX) th0 in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Const("word_neg",_),t) ->
        let th0 = ASM_CONGBOUND_RULE lfn t in
        let th1 = MATCH_MP CONGBOUND_WORD_NEG th0 in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("word_add",_),ltm),rtm) ->
        let lth = ASM_CONGBOUND_RULE lfn ltm
        and rth = ASM_CONGBOUND_RULE lfn rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_ADD (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("word_sub",_),ltm),rtm) ->
        let lth = ASM_CONGBOUND_RULE lfn ltm
        and rth = ASM_CONGBOUND_RULE lfn rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_SUB (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("word_mul",_),ltm),rtm) ->
        let lth = ASM_CONGBOUND_RULE lfn ltm
        and rth = ASM_CONGBOUND_RULE lfn rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_MUL (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | _ -> CONCL_BOUNDS_RULE(ISPEC tm CONGBOUND_ATOM);;

let GEN_CONGBOUND_RULE aboths =
  ASM_CONGBOUND_RULE (PROCESS_BOUND_ASSUMPTIONS aboths);;

let CONGBOUND_RULE = GEN_CONGBOUND_RULE [];;

let rec LOCAL_CONGBOUND_RULE lfn asms =
  match asms with
    [] -> lfn
  | th::ths ->
      let bod,var = dest_eq (concl th) in
      let th1 = ASM_CONGBOUND_RULE lfn bod in
      let th2 = SUBS[th] th1 in
      let lfn' = (var |-> th2) lfn in
      LOCAL_CONGBOUND_RULE lfn' ths;;

(* ------------------------------------------------------------------------- *)
(* Simplify SIMD cruft and fold relevant definitions when encountered.       *)
(* The ABBREV form also introduces abbreviations for relevant subterms.      *)
(* ------------------------------------------------------------------------- *)

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let arm_simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  let x86_simdable = can (term_match [] `read X (s:x86state):int256 = whatever`) in
  let simdable tm = arm_simdable tm || x86_simdable tm in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

let is_local_definition unfold_defs =
  let pats = map (lhand o snd o strip_forall o concl) unfold_defs in
  let pam t = exists (fun p -> can(term_match [] p) t) pats in
  fun tm -> is_eq tm && is_var(rand tm) && pam(lhand tm);;

let AUTO_ABBREV_TAC tm =
  let gv = genvar(type_of tm) in
  ABBREV_TAC(mk_eq(gv,tm));;

let SIMD_SIMPLIFY_ABBREV_TAC =
  let arm_simdable =
    can (term_match [] `read X (s:armstate):int128 = whatever`)
  and x86_simdable =
    can (term_match [] `read X (s:x86state):int256 = whatever`) in
  let simdable tm = arm_simdable tm || x86_simdable tm in
  fun unfold_defs unfold_aux ->
    let pats = map (lhand o snd o strip_forall o concl) unfold_defs in
    let pam t = exists (fun p -> can(term_match [] p) t) pats in
    let ttac th (asl,w) =
      let th' = CONV_RULE(RAND_CONV
                 (SIMD_SIMPLIFY_CONV (unfold_defs @ unfold_aux))) th in
      let asms =
        map snd (filter (is_local_definition unfold_defs o concl o snd) asl) in
      let th'' = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) asms th' in
      let tms = sort free_in (find_terms pam (rand(concl th''))) in
      (MP_TAC th'' THEN MAP_EVERY AUTO_ABBREV_TAC tms THEN DISCH_TAC) (asl,w) in
  TRY(FIRST_X_ASSUM(ttac o check (simdable o concl)));;

(* ------------------------------------------------------------------------- *)
(* Prove a bound quantified formula case-by-case                             *)
(* ------------------------------------------------------------------------- *)

let PEEL_LEMMA = prove(
  `!P n. (!i. i < SUC n ==> P i) <=> (!i. i < n ==> P i) /\ P n`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_TAC THEN CONJ_TAC THENL [
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num = n` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let BRUTE_FORCE_WITH tac =
  let rec go (asl, w as gl) =
    let (i, body) = dest_forall w in
    let (ant, _) = dest_imp body in
    let n_tm = rand ant in
    let n = dest_small_numeral n_tm in
    if n = 0 then (GEN_TAC THEN SIMP_TAC[LT]) gl
    else
      let suc_eq = num_CONV n_tm in
      (CONV_TAC(BINDER_CONV(LAND_CONV(RAND_CONV(REWR_CONV suc_eq)))) THEN
       GEN_REWRITE_TAC I [PEEL_LEMMA] THEN
       CONJ_TAC THENL [ALL_TAC; 
         (fun gl2 -> try let r = tac gl2 in
           Printf.printf "Case %d proved\n%!" (n-1); r
          with e -> Printf.printf "Failed to prove case %d\n%!" (n-1); raise e)
       ] THEN
       go) gl
  in go;;

(* ------------------------------------------------------------------------- *)
(* Some word lemmas, likely of more general use                              *)
(* ------------------------------------------------------------------------- *)

let COND_REWRITE_CONV solve thm : conv = fun tm ->
  let thm' = PART_MATCH (lhand o snd o dest_imp) thm tm in
  let precond = fst(dest_imp(concl thm')) in
  MP thm' (solve precond);;

let WORD_64_SUB_8_8_JOIN_16 = WORD_BLAST `!(x : 64 word).
         word_join (word_subword x (8,8) : 8 word) (word_subword x (0,8) : 8 word) =
         word_subword x (0,16) : 16 word`;;

let WORD_JOIN_AND_TYBIT0 = prove(
  `word_and (word_join (a:N word) (b:N word) : (N tybit0) word) (word_join (c:N word) (d:N word)) =
   word_join (word_and a c) (word_and b d)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_JOIN; DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < 2 * dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (q <=> p /\ q)`) THEN ASM_ARITH_TAC);;

let WORD_JOIN_NOT_TYBIT0 = prove(
  `word_not (word_join (a:N word) (b:N word) : (N tybit0) word) =
   word_join (word_not a) (word_not b)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_NOT; BIT_WORD_JOIN; DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < 2 * dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (~q <=> p /\ ~q)`) THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_USHR_JOIN = prove(
  `word_subword (word_ushr (x:(N tybit0) word) (dimindex(:N))) (0,dimindex(:N)) : N word =
   word_subword x (dimindex(:N), dimindex(:N))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_SUBWORD; BIT_WORD_USHR; DIMINDEX_TYBIT0] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES; ADD_SYM]);;

let WORD_SUBWORD_USHR_64 = REWRITE_RULE[DIMINDEX_CONV `dimindex(:64)`]
  (INST_TYPE [`:64`,`:N`] WORD_SUBWORD_USHR_JOIN);;  
  
let WORD_SUBWORD_USHR_HIGH = prove(
  `word_subword (word_ushr (x:(N tybit0) word) (dimindex(:N))) (dimindex(:N),dimindex(:N)) : N word = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_SUBWORD; BIT_WORD_USHR; BIT_WORD_0; DIMINDEX_TYBIT0] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (INST_TYPE [`:N tybit0`,`:N`] BIT_TRIVIAL)) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ASM_ARITH_TAC);;

(* Commutativity of multiplication and shift *)
let WORD_MUL_SHL = prove(`!x y n. word_mul (word_shl y n) x = word_shl (word_mul x y) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD_SHL; EXP_2] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_AC]);;

(* Exact multiplication when no overflow *)
let VAL_WORD_MUL_EXACT = prove(
  `!x y. val x * val y < 2 EXP dimindex(:N)
         ==> val(word_mul x y : N word) = val x * val y`,
  REWRITE_TAC[VAL_WORD_MUL] THEN SIMP_TAC[MOD_LT]);;

(* Exact word construction when no overflow *)
let VAL_WORD_EXACT = prove(
  `!n. n < 2 EXP dimindex(:N) ==> val(word n : N word) = n`,
  REWRITE_TAC[VAL_WORD] THEN SIMP_TAC[MOD_LT]);;

(* Exact zero-extension when target is large enough *)
let VAL_WORD_ZX_EXACT = prove(
  `!(x:M word). val x < 2 EXP dimindex(:N) ==> val(word_zx x : N word) = val x`,
  REWRITE_TAC[VAL_WORD_ZX_GEN] THEN SIMP_TAC[MOD_LT]);;

(* Double zero-extension is identity *)
let WORD_ZX_128_256_128 = prove(
  `!(x : 128 word). word_zx (word_zx x : 256 word) = x`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_128; DIMINDEX_256] THEN
  SUBGOAL_THEN `val (x:128 word) < 2 EXP 256` ASSUME_TAC THENL
  [MP_TAC(ISPEC `x:128 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_128] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
   ASM_SIMP_TAC[MOD_LT; WORD_VAL]]);;

(* Word equality via subword comparison *)
let WORD_PACKED_EQ = prove(
 `!(x:N word) (y:N word).
    dimindex(:N) = l * k /\ 0 < l /\ l <= dimindex(:M)
    ==> (x = y <=>
         !i. i < k
             ==> word_subword x (l*i, l) : (M) word =
                 word_subword y (l*i, l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
   DISCH_TAC THEN
   GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `j:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `j DIV l`) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `j < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `0 < l ==> ~(l = 0)`; MULT_SYM];
    DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\(w:M word). bit (j MOD l) w` th)) THEN
    REWRITE_TAC[BIT_WORD_SUBWORD] THEN
    SUBGOAL_THEN `j MOD l < MIN l (dimindex(:M))`
      (fun th -> REWRITE_TAC[th]) THENL
    [ASM_SIMP_TAC[ARITH_RULE `l <= m ==> MIN l m = l`;
                   MOD_LT_EQ; ARITH_RULE `0 < l ==> ~(l = 0)`];
     ASM_SIMP_TAC[DIVISION_SIMP; ARITH_RULE `0 < l ==> ~(l = 0)`]]]]);;

(* Extract k-th element from packed wordlist *)
let WORD_SUBWORD_NUM_OF_WORDLIST = prove
 (`!(ls:(L word)list) k.
    dimindex(:KL) = dimindex(:L) * LENGTH ls /\
    k < LENGTH ls
    ==> word_subword (word (num_of_wordlist ls) : KL word) (dimindex(:L)*k, dimindex(:L)) : L word = EL k ls`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN n n = n`] THEN
  SUBGOAL_THEN `val (word (num_of_wordlist (ls:(L word)list)) : KL word) = num_of_wordlist ls` SUBST1_TAC THENL
  [W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o lhand o snd) THEN
   ANTS_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (dimindex(:L) * LENGTH (ls:(L word)list))` THEN
    REWRITE_TAC[NUM_OF_WORDLIST_BOUND; LE_EXP; LE_REFL] THEN ASM_ARITH_TAC;
    SIMP_TAC[]];
   MP_TAC(ISPECL [`ls:(L word)list`; `k:num`] NUM_OF_WORDLIST_EL) THEN
   ASM_REWRITE_TAC[]]);;

(* Convert byte sequence to hierarchical word_join structure *)
let BYTES128_JOIN = prove(
  `!(b0:8 word) (b1:8 word) (b2:8 word) (b3:8 word)
    (b4:8 word) (b5:8 word) (b6:8 word) (b7:8 word)
    (b8:8 word) (b9:8 word) (b10:8 word) (b11:8 word)
    (b12:8 word) (b13:8 word) (b14:8 word) (b15:8 word).
    (word_zx:256 word->128 word)
    ((word_zx:128 word->256 word)
   (word(val b0 * 2 EXP (8 * 0) +
          val b1 * 2 EXP (8 * 1) +
          val b2 * 2 EXP (8 * 2) +
          val b3 * 2 EXP (8 * 3) +
          val b4 * 2 EXP (8 * 4) +
          val b5 * 2 EXP (8 * 5) +
          val b6 * 2 EXP (8 * 6) +
          val b7 * 2 EXP (8 * 7) +
          val b8 * 2 EXP (8 * 8) +
          val b9 * 2 EXP (8 * 9) +
          val b10 * 2 EXP (8 * 10) +
          val b11 * 2 EXP (8 * 11) +
          val b12 * 2 EXP (8 * 12) +
          val b13 * 2 EXP (8 * 13) +
          val b14 * 2 EXP (8 * 14) +
          val b15 * 2 EXP (8 * 15)) :128 word)) =
    word_join
      (word_join (word_join b15 b14 :16 word) (word_join b13 b12 :16 word) :32 word)
      (word_join
        (word_join (word_join b11 b10 :16 word) (word_join b9 b8 :16 word) :32 word)
        (word_join
          (word_join (word_join b7 b6 :16 word) (word_join b5 b4 :16 word) :32 word)
          (word_join (word_join b3 b2 :16 word) (word_join b1 b0 :16 word) :32 word)
          :64 word) :96 word) :128 word`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[WORD_ZX_128_256_128; DIMINDEX_128; DIMINDEX_256] THEN
  SUBGOAL_THEN `val (b0 : 8 word) * 2 EXP (8 * 0) +
                val (b1 : 8 word) * 2 EXP (8 * 1) +
                val (b2 : 8 word) * 2 EXP (8 * 2) +
                val (b3 : 8 word) * 2 EXP (8 * 3) +
                val (b4 : 8 word) * 2 EXP (8 * 4) +
                val (b5 : 8 word) * 2 EXP (8 * 5) +
                val (b6 : 8 word) * 2 EXP (8 * 6) +
                val (b7 : 8 word) * 2 EXP (8 * 7) +
                val (b8 : 8 word) * 2 EXP (8 * 8) +
                val (b9 : 8 word) * 2 EXP (8 * 9) +
                val (b10 : 8 word) * 2 EXP (8 * 10) +
                val (b11 : 8 word) * 2 EXP (8 * 11) +
                val (b12 : 8 word) * 2 EXP (8 * 12) +
                val (b13 : 8 word) * 2 EXP (8 * 13) +
                val (b14 : 8 word) * 2 EXP (8 * 14) +
                val (b15 : 8 word) * 2 EXP (8 * 15) = num_of_wordlist [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15]`
    SUBST1_TAC THENL [REWRITE_TAC [num_of_wordlist; LEFT_ADD_DISTRIB; GSYM EXP_ADD; DIMINDEX_CONV `dimindex(:8)`] THEN ARITH_TAC; ALL_TAC] THEN
    REPLICATE_TAC 4 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist] THEN
    REWRITE_TAC [num_of_wordlist] THEN
    CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    BITBLAST_TAC);;


let BYTES256_JOIN = prove(
  `!(b0:8 word) (b1:8 word) (b2:8 word) (b3:8 word)
    (b4:8 word) (b5:8 word) (b6:8 word) (b7:8 word)
    (b8:8 word) (b9:8 word) (b10:8 word) (b11:8 word)
    (b12:8 word) (b13:8 word) (b14:8 word) (b15:8 word)
    (b16:8 word) (b17:8 word) (b18:8 word) (b19:8 word)
    (b20:8 word) (b21:8 word) (b22:8 word) (b23:8 word)
    (b24:8 word) (b25:8 word) (b26:8 word) (b27:8 word)
    (b28:8 word) (b29:8 word) (b30:8 word) (b31:8 word).
    word(val b0 * 2 EXP (8 * 0) +
         val b1 * 2 EXP (8 * 1) +
         val b2 * 2 EXP (8 * 2) +
         val b3 * 2 EXP (8 * 3) +
         val b4 * 2 EXP (8 * 4) +
         val b5 * 2 EXP (8 * 5) +
         val b6 * 2 EXP (8 * 6) +
         val b7 * 2 EXP (8 * 7) +
         val b8 * 2 EXP (8 * 8) +
         val b9 * 2 EXP (8 * 9) +
         val b10 * 2 EXP (8 * 10) +
         val b11 * 2 EXP (8 * 11) +
         val b12 * 2 EXP (8 * 12) +
         val b13 * 2 EXP (8 * 13) +
         val b14 * 2 EXP (8 * 14) +
         val b15 * 2 EXP (8 * 15) +
         val b16 * 2 EXP (8 * 16) +
         val b17 * 2 EXP (8 * 17) +
         val b18 * 2 EXP (8 * 18) +
         val b19 * 2 EXP (8 * 19) +
         val b20 * 2 EXP (8 * 20) +
         val b21 * 2 EXP (8 * 21) +
         val b22 * 2 EXP (8 * 22) +
         val b23 * 2 EXP (8 * 23) +
         val b24 * 2 EXP (8 * 24) +
         val b25 * 2 EXP (8 * 25) +
         val b26 * 2 EXP (8 * 26) +
         val b27 * 2 EXP (8 * 27) +
         val b28 * 2 EXP (8 * 28) +
         val b29 * 2 EXP (8 * 29) +
         val b30 * 2 EXP (8 * 30) +
         val b31 * 2 EXP (8 * 31)) :256 word =
    word_join
      (word_join
        (word_join (word_join b31 b30 :16 word) (word_join b29 b28 :16 word) :32 word)
        (word_join (word_join b27 b26 :16 word) (word_join b25 b24 :16 word) :32 word)
        :64 word)
      (word_join
        (word_join
          (word_join (word_join b23 b22 :16 word) (word_join b21 b20 :16 word) :32 word)
          (word_join (word_join b19 b18 :16 word) (word_join b17 b16 :16 word) :32 word)
          :64 word)
        (word_join
          (word_join
            (word_join (word_join b15 b14 :16 word) (word_join b13 b12 :16 word) :32 word)
            (word_join (word_join b11 b10 :16 word) (word_join b9 b8 :16 word) :32 word)
            :64 word)
          (word_join
            (word_join (word_join b7 b6 :16 word) (word_join b5 b4 :16 word) :32 word)
            (word_join (word_join b3 b2 :16 word) (word_join b1 b0 :16 word) :32 word)
            :64 word)
          :128 word)
        :192 word)
      :256 word`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `val (b0 : 8 word) * 2 EXP (8 * 0) +
                val (b1 : 8 word) * 2 EXP (8 * 1) +
                val (b2 : 8 word) * 2 EXP (8 * 2) +
                val (b3 : 8 word) * 2 EXP (8 * 3) +
                val (b4 : 8 word) * 2 EXP (8 * 4) +
                val (b5 : 8 word) * 2 EXP (8 * 5) +
                val (b6 : 8 word) * 2 EXP (8 * 6) +
                val (b7 : 8 word) * 2 EXP (8 * 7) +
                val (b8 : 8 word) * 2 EXP (8 * 8) +
                val (b9 : 8 word) * 2 EXP (8 * 9) +
                val (b10 : 8 word) * 2 EXP (8 * 10) +
                val (b11 : 8 word) * 2 EXP (8 * 11) +
                val (b12 : 8 word) * 2 EXP (8 * 12) +
                val (b13 : 8 word) * 2 EXP (8 * 13) +
                val (b14 : 8 word) * 2 EXP (8 * 14) +
                val (b15 : 8 word) * 2 EXP (8 * 15) +
                val (b16 : 8 word) * 2 EXP (8 * 16) +
                val (b17 : 8 word) * 2 EXP (8 * 17) +
                val (b18 : 8 word) * 2 EXP (8 * 18) +
                val (b19 : 8 word) * 2 EXP (8 * 19) +
                val (b20 : 8 word) * 2 EXP (8 * 20) +
                val (b21 : 8 word) * 2 EXP (8 * 21) +
                val (b22 : 8 word) * 2 EXP (8 * 22) +
                val (b23 : 8 word) * 2 EXP (8 * 23) +
                val (b24 : 8 word) * 2 EXP (8 * 24) +
                val (b25 : 8 word) * 2 EXP (8 * 25) +
                val (b26 : 8 word) * 2 EXP (8 * 26) +
                val (b27 : 8 word) * 2 EXP (8 * 27) +
                val (b28 : 8 word) * 2 EXP (8 * 28) +
                val (b29 : 8 word) * 2 EXP (8 * 29) +
                val (b30 : 8 word) * 2 EXP (8 * 30) +
                val (b31 : 8 word) * 2 EXP (8 * 31) = num_of_wordlist [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18; b19; b20; b21; b22; b23; b24; b25; b26; b27; b28; b29; b30; b31]`
    SUBST1_TAC THENL [REWRITE_TAC [num_of_wordlist; LEFT_ADD_DISTRIB; GSYM EXP_ADD; DIMINDEX_CONV `dimindex(:8)`] THEN ARITH_TAC; ALL_TAC] THEN
    REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist] THEN
    REWRITE_TAC [num_of_wordlist] THEN
    CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    BITBLAST_TAC);;

(* Flatten nested wordlists for hierarchical packing *)
let NUM_OF_WORDLIST_FLATTEN = prove
 (`!(ll:((N word) list) list) k.
     ALL (\l. LENGTH l = k) ll /\
     dimindex(:N) * k = dimindex(:M)
     ==> num_of_wordlist (ITLIST APPEND ll []) =
         num_of_wordlist (MAP ((word:num->M word) o num_of_wordlist) ll)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MAP; num_of_wordlist; ALL] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; num_of_wordlist; o_THM] THEN
  ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  IMP_REWRITE_TAC [VAL_WORD_EXACT] THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(h:(N word)list))` THEN
  REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH] THEN
  ASM_REWRITE_TAC[LE_REFL]);;

