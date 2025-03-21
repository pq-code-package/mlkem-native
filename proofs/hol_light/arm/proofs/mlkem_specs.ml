(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Common specifications and tactics for ML-KEM, mainly related to the NTT
 * and the base multiplication.  *)
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

(* ------------------------------------------------------------------------- *)
(* Conversion of each element of an array to Montgomery form with B = 2^16.  *)
(* ------------------------------------------------------------------------- *)

let tomont_3329 = define
 `tomont_3329 (a:num->int) = \i. (&2 pow 16 * a i) rem &3329`;;

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

let FORWARD_NTT_CONV =
  GEN_REWRITE_CONV I [FORWARD_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES] THENC
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
(* Congruence-and-bound propagation, just recursion on the expression tree.  *)
(* ------------------------------------------------------------------------- *)

let CONGBOUND_ATOM = prove
 (`!x:N word. (ival x == ival x) (mod &3329) /\
              --(&2 pow (dimindex(:N) - 1)) <= ival x /\
              ival x <= &2 pow (dimindex(:N) - 1) - &1`,
  GEN_TAC THEN REWRITE_TAC[INT_ARITH `x:int <= y - &1 <=> x < y`] THEN
  REWRITE_TAC[IVAL_BOUND] THEN INTEGER_TAC);;

let CONGBOUND_ATOM_GEN = prove
 (`!x:N word. abs(ival x) <= n
              ==> (ival x == ival x) (mod &3329) /\ --n <= ival x /\ ival x <= n`,
  REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`] THEN INT_ARITH_TAC);;

let CONGBOUND_IWORD = prove
 (`!x. ((x == x') (mod &3329) /\ l <= x /\ x <= u)
       ==> --(&2 pow (dimindex(:N) - 1)) <= l /\ u <= &2 pow (dimindex(:N) - 1) - &1
           ==> (ival(iword x:N word) == x') (mod &3329) /\
               l <= ival(iword x:N word) /\ ival(iword x:N word) <= u`,
  GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o lhand o rand o rand o snd) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

let CONGBOUND_WORD_SX = prove
 (`!x:M word.
        ((ival x == x') (mod &3329) /\ l <= ival x /\ ival x <= u)
        ==> --(&2 pow (dimindex(:N) - 1)) <= l /\ u <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_sx x:N word) == x') (mod &3329) /\
                l <= ival(word_sx x:N word) /\ ival(word_sx x:N word) <= u`,
  REWRITE_TAC[word_sx; CONGBOUND_IWORD]);;

let CONGBOUND_WORD_ADD = prove
 (`!x y:N word.
        ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod &3329) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1)) <= lx + ly /\
            ux + uy <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_add x y) == x' + y') (mod &3329) /\
                lx + ly <= ival(word_add x y) /\
                ival(word_add x y) <= ux + uy`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD_IMODULAR; imodular] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_ADD] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_WORD_SUB = prove
 (`!x y:N word.
        ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod &3329) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1)) <= lx - uy /\
            ux - ly <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_sub x y) == x' - y') (mod &3329) /\
                lx - uy <= ival(word_sub x y) /\
                ival(word_sub x y) <= ux - ly`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SUB_IMODULAR; imodular] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_SUB] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_WORD_MUL = prove
 (`!x y:N word.
        ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod &3329) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1))
            <= min (lx * ly) (min (lx * uy) (min (ux * ly) (ux * uy))) /\
            max (lx * ly) (max (lx * uy) (max (ux * ly) (ux * uy)))
            <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_mul x y) == x' * y') (mod &3329) /\
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

let DIMINDEX_INT_REDUCE_CONV =
  DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC DIMINDEX_CONV) THENC
  INT_REDUCE_CONV;;

let CONCL_BOUNDS_RULE =
  CONV_RULE(BINOP2_CONV
          (LAND_CONV(RAND_CONV DIMINDEX_INT_REDUCE_CONV))
          (BINOP2_CONV
           (LAND_CONV DIMINDEX_INT_REDUCE_CONV)
           (RAND_CONV DIMINDEX_INT_REDUCE_CONV)));;

let SIDE_ELIM_RULE th =
  MP th (EQT_ELIM(DIMINDEX_INT_REDUCE_CONV(lhand(concl th))));;

let rec GEN_CONGBOUND_RULE aboths tm =
  match tm with
    Comb(Comb(Const("barmul",_),kb),t) ->
        let ktm,btm = dest_pair kb and th0 = GEN_CONGBOUND_RULE aboths t in
        let th1 = SPECL [ktm;btm] (MATCH_MP CONGBOUND_BARMUL th0) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
  | Comb(Const("barred",_),t) ->
        let th1 = GEN_CONGBOUND_RULE aboths t in
        MATCH_MP CONGBOUND_BARRED th1
  | Comb(Const("montred",_),t) ->
        let th1 = GEN_CONGBOUND_RULE aboths t in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE(MATCH_MP CONGBOUND_MONTRED th1))
  | Comb(Const("word_sx",_),t) ->
        let th0 = GEN_CONGBOUND_RULE aboths t in
        let tyin = type_match
         (type_of(rator(rand(lhand(funpow 4 rand (snd(dest_forall
            (concl CONGBOUND_WORD_SX)))))))) (type_of(rator tm)) [] in
        let th1 = MATCH_MP (INST_TYPE tyin CONGBOUND_WORD_SX) th0 in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
  | Comb(Comb(Const("word_add",_),ltm),rtm) ->
        let lth = GEN_CONGBOUND_RULE aboths ltm
        and rth = GEN_CONGBOUND_RULE aboths rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_ADD (CONJ lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
  | Comb(Comb(Const("word_sub",_),ltm),rtm) ->
        let lth = GEN_CONGBOUND_RULE aboths ltm
        and rth = GEN_CONGBOUND_RULE aboths rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_SUB (CONJ lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
  | Comb(Comb(Const("word_mul",_),ltm),rtm) ->
        let lth = GEN_CONGBOUND_RULE aboths ltm
        and rth = GEN_CONGBOUND_RULE aboths rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_MUL (CONJ lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
  | _ -> (try MATCH_MP CONGBOUND_ATOM_GEN
               (find ((=) tm o rand o rand o lhand o concl) aboths)
          with Failure _ -> CONCL_BOUNDS_RULE(ISPEC tm CONGBOUND_ATOM));;

let CONGBOUND_RULE = GEN_CONGBOUND_RULE [];;
