(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Common specifications and tactics for ML-KEM, mainly related to the NTT.  *)
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
(* Abbreviate the Barrett reduction and multiplication patterns in the code. *)
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

(* ------------------------------------------------------------------------- *)
(* Congruence-and-bound propagation, just recursion on the expression tree.  *)
(* ------------------------------------------------------------------------- *)

let CONGBOUND_ATOM = prove
 (`!x:int16. (ival x == ival x) (mod &3329) /\
             -- &32768 <= ival x /\ ival x <= &32767`,
  GEN_TAC THEN CONJ_TAC THENL [CONV_TAC INTEGER_RULE; BOUNDER_TAC[]]);;

let CONGBOUND_ATOM_GEN = prove
 (`!x:int16. abs(ival x) <= n
           ==> (ival x == ival x) (mod &3329) /\ --n <= ival x /\ ival x <= n`,
  REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`] THEN INT_ARITH_TAC);;

let CONGBOUND_WORD_ADD = prove
 (`!x y:int16.
        ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod &3329) /\ ly <= ival y /\ ival y <= uy)
        ==> -- &32768 <= lx + ly /\ ux + uy <= &32767
            ==> (ival(word_add x y) == x' + y') (mod &3329) /\
                lx + ly <= ival(word_add x y) /\
                ival(word_add x y) <= ux + uy`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_add x y:int16) = ival x + ival y` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow dimindex(:16)` THEN
    REWRITE_TAC[ICONG_WORD_ADD] THEN
    MP_TAC(ISPEC `word_add x y:int16` IVAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_INT_ARITH_TAC;
    ASM_SIMP_TAC[INT_CONG_ADD] THEN ASM_INT_ARITH_TAC]);;

let CONGBOUND_WORD_SUB = prove
 (`!x y:int16.
        ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod &3329) /\ ly <= ival y /\ ival y <= uy)
        ==> -- &32768 <= lx - uy /\ ux - ly <= &32767
            ==> (ival(word_sub x y) == x' - y') (mod &3329) /\
                lx - uy <= ival(word_sub x y) /\
                ival(word_sub x y) <= ux - ly`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_sub x y:int16) = ival x - ival y` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow dimindex(:16)` THEN
    REWRITE_TAC[ICONG_WORD_SUB] THEN
    MP_TAC(ISPEC `word_sub x y:int16` IVAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_INT_ARITH_TAC;
    ASM_SIMP_TAC[INT_CONG_SUB] THEN ASM_INT_ARITH_TAC]);;

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

let rec GEN_CONGBOUND_RULE aboths tm =
  match tm with
    Comb(Comb(Const("barmul",_),kb),t) ->
        let ktm,btm = dest_pair kb and th0 = GEN_CONGBOUND_RULE aboths t in
        let th1 = SPECL [ktm;btm] (MATCH_MP CONGBOUND_BARMUL th0) in
        let th2 = DEPTH_CONV WORD_NUM_RED_CONV (lhand(concl th1)) in
        let th3 = MP th1 (EQT_ELIM th2) in
        CONV_RULE(BINOP2_CONV
          (LAND_CONV(RAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)))
          (BINOP2_CONV
           (LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV))
           (RAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)))) th3
  | Comb(Const("barred",_),t) ->
        let th1 = GEN_CONGBOUND_RULE aboths t in
        MATCH_MP CONGBOUND_BARRED th1
  | Comb(Comb(Const("word_add",_),ltm),rtm) ->
        let lth = GEN_CONGBOUND_RULE aboths ltm
        and rth = GEN_CONGBOUND_RULE aboths rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_ADD (CONJ lth rth) in
        let th2 = DEPTH_CONV WORD_NUM_RED_CONV (lhand(concl th1)) in
        let th3 = MP th1 (EQT_ELIM th2) in
        CONV_RULE(RAND_CONV (BINOP2_CONV
           (LAND_CONV INT_ADD_CONV) (RAND_CONV INT_ADD_CONV))) th3
  | Comb(Comb(Const("word_sub",_),ltm),rtm) ->
        let lth = GEN_CONGBOUND_RULE aboths ltm
        and rth = GEN_CONGBOUND_RULE aboths rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_SUB (CONJ lth rth) in
        let th2 = DEPTH_CONV WORD_NUM_RED_CONV (lhand(concl th1)) in
        let th3 = MP th1 (EQT_ELIM th2) in
        CONV_RULE(RAND_CONV (BINOP2_CONV
           (LAND_CONV INT_SUB_CONV) (RAND_CONV INT_SUB_CONV))) th3
  | _ -> (try MATCH_MP CONGBOUND_ATOM_GEN
               (find ((=) tm o rand o rand o lhand o concl) aboths)
          with Failure _ -> ISPEC tm CONGBOUND_ATOM);;

let CONGBOUND_RULE = GEN_CONGBOUND_RULE [];;
