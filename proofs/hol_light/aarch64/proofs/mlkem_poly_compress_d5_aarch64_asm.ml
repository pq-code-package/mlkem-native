(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 5 bits.                         *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_compress_d5_table.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_compress_d5_aarch64_asm.o";;
 ****)

let mlkem_poly_compress_d5_mc = define_assert_from_elf
  "mlkem_poly_compress_d5_mc" "aarch64/mlkem/mlkem_poly_compress_d5_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x4c40a05d;       (* arm_LDP Q29 Q30 X2 No_Offset *)
  0xd2800083;       (* arm_MOV X3 (rvalue (word 4)) *)
  0x4cdf8420;       (* arm_LD2 Q0 Q1 X1 (Postimmediate_Offset (word 32)) 128 16 *)
  0x4cdf8422;       (* arm_LD2 Q2 Q3 X1 (Postimmediate_Offset (word 32)) 128 16 *)
  0x4cdf8424;       (* arm_LD2 Q4 Q5 X1 (Postimmediate_Offset (word 32)) 128 16 *)
  0x4cdf8426;       (* arm_LD2 Q6 Q7 X1 (Postimmediate_Offset (word 32)) 128 16 *)
  0x6e7db400;       (* arm_SQRDMULH_VEC Q0 Q0 Q29 16 128 *)
  0x6e7db421;       (* arm_SQRDMULH_VEC Q1 Q1 Q29 16 128 *)
  0x6e7db442;       (* arm_SQRDMULH_VEC Q2 Q2 Q29 16 128 *)
  0x6e7db463;       (* arm_SQRDMULH_VEC Q3 Q3 Q29 16 128 *)
  0x6e7db484;       (* arm_SQRDMULH_VEC Q4 Q4 Q29 16 128 *)
  0x6e7db4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q29 16 128 *)
  0x6e7db4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q29 16 128 *)
  0x6e7db4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q29 16 128 *)
  0x6f155420;       (* arm_SLI_VEC Q0 Q1 5 128 16 *)
  0x4e406810;       (* arm_TRN2 Q16 Q0 Q0 16 128 *)
  0x6f2a5600;       (* arm_SLI_VEC Q0 Q16 10 128 32 *)
  0x4e806810;       (* arm_TRN2 Q16 Q0 Q0 32 128 *)
  0x6f545600;       (* arm_SLI_VEC Q0 Q16 20 128 64 *)
  0x6f155462;       (* arm_SLI_VEC Q2 Q3 5 128 16 *)
  0x4e426851;       (* arm_TRN2 Q17 Q2 Q2 16 128 *)
  0x6f2a5622;       (* arm_SLI_VEC Q2 Q17 10 128 32 *)
  0x4e826851;       (* arm_TRN2 Q17 Q2 Q2 32 128 *)
  0x6f545622;       (* arm_SLI_VEC Q2 Q17 20 128 64 *)
  0x6f1554a4;       (* arm_SLI_VEC Q4 Q5 5 128 16 *)
  0x4e446892;       (* arm_TRN2 Q18 Q4 Q4 16 128 *)
  0x6f2a5644;       (* arm_SLI_VEC Q4 Q18 10 128 32 *)
  0x4e846892;       (* arm_TRN2 Q18 Q4 Q4 32 128 *)
  0x6f545644;       (* arm_SLI_VEC Q4 Q18 20 128 64 *)
  0x6f1554e6;       (* arm_SLI_VEC Q6 Q7 5 128 16 *)
  0x4e4668d3;       (* arm_TRN2 Q19 Q6 Q6 16 128 *)
  0x6f2a5666;       (* arm_SLI_VEC Q6 Q19 10 128 32 *)
  0x4e8668d3;       (* arm_TRN2 Q19 Q6 Q6 32 128 *)
  0x6f545666;       (* arm_SLI_VEC Q6 Q19 20 128 64 *)
  0x4e1e0000;       (* arm_TBL Q0 [Q0] Q30 128 *)
  0x4e1e0042;       (* arm_TBL Q2 [Q2] Q30 128 *)
  0x4e1e0084;       (* arm_TBL Q4 [Q4] Q30 128 *)
  0x4e1e00c6;       (* arm_TBL Q6 [Q6] Q30 128 *)
  0x6e025014;       (* arm_EXT Q20 Q0 Q2 80 *)
  0x6e042294;       (* arm_EXT Q20 Q20 Q4 32 *)
  0x6e065095;       (* arm_EXT Q21 Q4 Q6 80 *)
  0x0c9f7000;       (* arm_STR D0 X0 (Postimmediate_Offset (word 8)) *)
  0x4c9f7014;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f7015;       (* arm_STR Q21 X0 (Postimmediate_Offset (word 16)) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0xb5fffaa3;       (* arm_CBNZ X3 (word 2096980) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_COMPRESS_D5_EXEC = ARM_MK_EXEC_RULE mlkem_poly_compress_d5_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_COMPRESS_D5_MC =
  REWRITE_CONV[mlkem_poly_compress_d5_mc] `LENGTH mlkem_poly_compress_d5_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_COMPRESS_D5_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D5_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_COMPRESS_D5_CORE_START = new_definition
  `MLKEM_POLY_COMPRESS_D5_CORE_START = MLKEM_POLY_COMPRESS_D5_PREAMBLE_LENGTH`;;

let MLKEM_POLY_COMPRESS_D5_CORE_END = new_definition
  `MLKEM_POLY_COMPRESS_D5_CORE_END =
   LENGTH mlkem_poly_compress_d5_mc - MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_COMPRESS_D5_MC;
               MLKEM_POLY_COMPRESS_D5_CORE_START;
               MLKEM_POLY_COMPRESS_D5_CORE_END;
               MLKEM_POLY_COMPRESS_D5_PREAMBLE_LENGTH;
               MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Per-coefficient formula.                                                  *)
(*                                                                           *)
(* Each coefficient x passes through                                         *)
(*                                                                           *)
(*   sqrdmulh x, 315   (16-bit lanes)                                        *)
(*                                                                           *)
(* and the packing keeps the low 5 bits of the result. compress_d5_aarch64   *)
(* is the 16-bit lane computed by sqrdmulh, stated in the form that the      *)
(* symbolic simulation produces, so that SIMD_SIMPLIFY_TAC can fold it.      *)
(* ------------------------------------------------------------------------- *)

let compress_d5_aarch64 = new_definition
 `compress_d5_aarch64 (x:int16) : int16 =
  iword_saturate((&2 * ival x * &315 + &32768) div &65536)`;;

(* The low 5 bits of compress_d5_aarch64 x are compress_d5 x for all
 * x in [0, 3328]; checked for each of the 3329 values. *)
let COMPRESS_D5_AARCH64_CORRECT = PROVE_BY_COEFF_ENUMERATION
  [compress_d5_aarch64; compress_d5]
  `!x:int16. val x < 3329
             ==> word_subword (compress_d5_aarch64 x) (0,5) : 5 word =
                 compress_d5 x`;;

(* ------------------------------------------------------------------------- *)
(* Packing.                                                                  *)
(*                                                                           *)
(* LD2 puts the even coefficients of 16 consecutive ones into one register   *)
(* and the odd ones into another. With y0, y1, ... the 16-bit lanes of       *)
(* consecutive coefficients after sqrdmulh, the code computes                *)
(*                                                                           *)
(*   16-bit lanes: p = (y1 << 5) | (y0 & 0x1f)                               *)
(*   32-bit lanes: q = (t << 10) | (p0 & 0x3ff),     t = p1:p1               *)
(*   64-bit lanes: g = (t << 20) | (q0 & 0xfffff),   t = q1:q1               *)
(*                                                                           *)
(* where p0, p1 (q0, q1) are the lower and upper halves of a 32-bit (64-bit) *)
(* lane, and t is the result of TRN2, which copies the upper half into both  *)
(* halves. TBL then picks bytes 0..4 of each 64-bit lane g. The AND lemmas   *)
(* rewrite the masking of a joined lane, which otherwise copies the upper    *)
(* half into the result of every SLI. The byte lemmas show that bytes 0..4   *)
(* of g are the bytes of the 40-bit word that joins the low 5 bits of y0,    *)
(* ..., y7. They hold for any y0, ..., y7, so the bits above the low 5 bits  *)
(* of each coefficient (bit 5 is set if y = 32) never reach the stored       *)
(* bytes.                                                                    *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_JOIN_1023 = WORD_BLAST
 `!(h:int16) (l:int16).
        word_and (word_join h l : int32) (word 1023) =
        word_zx (word_and l (word 1023))`;;

let WORD_AND_JOIN_1048575 = WORD_BLAST
 `!(h:int32) (l:int32).
        word_and (word_join h l : int64) (word 1048575) =
        word_zx (word_and l (word 1048575))`;;

(* The 64-bit lane g computed from y0, ..., y7 by the three levels of
 * packing, after the lemmas above *)
let pack_lane_tm =
  let y i = Printf.sprintf "(y%d:int16)" i in
  let p j =
    Printf.sprintf "(word_or (word_shl %s 5) (word_and %s (word 31)):int16)"
      (y (2*j+1)) (y (2*j)) in
  let q k =
    Printf.sprintf
      "(word_or (word_shl (word_join %s %s:int32) 10) \
                (word_zx (word_and %s (word 1023)):int32))"
      (p (2*k+1)) (p (2*k+1)) (p (2*k)) in
  parse_term (Printf.sprintf
    "word_or (word_shl (word_join %s %s:int64) 20) \
             (word_zx (word_and %s (word 1048575)):int64)"
    (q 1) (q 1) (q 0));;

(* The 40 bits that ByteEncode_5 produces for y0, ..., y7 *)
let pack_group_tm =
  let field i = Printf.sprintf "(word_subword (y%d:int16) (0,5):5 word)" i in
  let rec go i =
    if i = 0 then field 0 else
    Printf.sprintf "(word_join %s %s:%d word)" (field i) (go (i - 1))
      ((i + 1) * 5) in
  parse_term (go 7);;

(* Bytes 0, ..., 4 of the lane in terms of the group *)
let PACK_BYTE_LEMMAS =
  let vars = map (fun i -> mk_var("y" ^ string_of_int i, `:int16`)) (0--7) in
  let mk k =
    let pos = mk_small_numeral (8 * k) in
    let lhs = subst [pack_lane_tm,`x:int64`; pos,`p:num`]
                `word_subword (x:int64) (p,8):byte`
    and rhs = subst [pack_group_tm,`y:40 word`; pos,`p:num`]
                `word_subword (y:40 word) (p,8):byte` in
    WORD_BLAST (list_mk_forall(vars, mk_eq(lhs, rhs))) in
  map mk (0--4);;

(* Everything SIMD_SIMPLIFY_TAC should fold or rewrite after each step *)
let COMPRESS_D5_SIMPS =
  compress_d5_aarch64 ::
  map GSYM ([WORD_AND_JOIN_1023; WORD_AND_JOIN_1048575] @ PACK_BYTE_LEMMAS);;

(* ------------------------------------------------------------------------- *)
(* Input layout.                                                             *)
(*                                                                           *)
(* Each LD2 reads 32 bytes, 16 coefficients, as one 256-bit word.            *)
(* ------------------------------------------------------------------------- *)

(* Replace the assumption tm, which must have the form
 *
 *   read (memory :> bytes (a,512)) s = num_of_wordlist (l:int16 list)
 *
 * by 16 assumptions
 *
 *   read (memory :> bytes256 (word_add a (word (32 * k)))) s =
 *     word_join (... (EL (16 * k + 1) l) (EL (16 * k) l))
 *
 * one for each LD2, in the form in which the symbolic simulation of LD2
 * reads memory. Requires `LENGTH l = 256` in the assumptions. *)
let POLY_BYTES256_TAC tm =
  UNDISCH_TAC tm THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
  REWRITE_TAC[] THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Output layout.                                                            *)
(*                                                                           *)
(* Each block of 40 output bytes (64 coefficients) is written by an 8-byte   *)
(* store followed by two 16-byte stores, so all stores start at multiples of *)
(* 8 bytes. The proof splits the 16-byte stores into 8-byte halves, and the  *)
(* expected output, viewed as one 1280-bit word, into 20 64-bit words.       *)
(* ------------------------------------------------------------------------- *)

(* Generic: for an n-bit word w with n = m * k, val w is the number formed by
 * the k m-bit subwords of w, as a little-endian word list. *)
let mk_val_as_wordlist n m =
  let k = n / m in
  let s = Printf.sprintf in
  let w = s "(w:%d word)" n in
  let ls_def = s "list_of_seq (\\i. word_subword %s (%d * i,%d):%d word) %d"
                 w m m m k in
  let tm = parse_term (s "!w:%d word. val w = num_of_wordlist (%s)" n ls_def) in
  let ls = s "(ls:(%d word)list)" m in
  let n_ty = mk_finty (Num.num_of_int n)
  and m_ty = mk_finty (Num.num_of_int m) in
  let th = prove(tm,
    GEN_TAC THEN
    ABBREV_TAC (parse_term (s "%s = %s" ls ls_def)) THEN
    SUBGOAL_THEN (parse_term (s "LENGTH %s = %d" ls k)) ASSUME_TAC THENL
     [EXPAND_TAC "ls" THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
    SUBGOAL_THEN (parse_term (s "(word (num_of_wordlist %s) : %d word) = %s"
                                ls n w))
    MP_TAC THENL
     [MP_TAC(ISPECL [parse_term (s "(word (num_of_wordlist %s) : %d word)"
                                   ls n);
                     parse_term w]
        (INST [mk_small_numeral m,`l:num`; mk_small_numeral k,`k:num`]
          (INST_TYPE [n_ty,`:N`; m_ty,`:M`] WORD_PACKED_EQ))) THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [parse_term ls; `i:num`]
        (INST_TYPE [n_ty,`:KL`; m_ty,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST)) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN
      EXPAND_TAC "ls" THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC VAL_WORD_EXACT THEN
      MP_TAC(ISPEC (parse_term ls) NUM_OF_WORDLIST_BOUND_LENGTH) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV]) in
  CONV_RULE(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV THENC
            DEPTH_CONV BETA_CONV THENC DEPTH_CONV NUM_MULT_CONV) th;;

let VAL_1280_AS_BYTES64 = mk_val_as_wordlist 1280 64;;

(* Generic: split each assumption `read (memory :> bytes128 a) s = v` into
 * `read (memory :> bytes64 a) s = word_subword v (0,64)` and the same for
 * a + 8 and bits 64..127, with the address a + 8 in normal form. *)
let SPLIT_STORES128_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [WORD_ADD_ASSOC_CONSTS] THENC
     RAND_CONV(RAND_CONV NUM_ADD_CONV)))) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D5_CORRECT = prove
 (`!r a t (l:int16 list) pc.
        ALL (nonoverlapping (r,160))
            [(word pc,LENGTH mlkem_poly_compress_d5_mc); (a,512); (t,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_compress_d5_mc /\
                  read PC s = word (pc + MLKEM_POLY_COMPRESS_D5_CORE_START) /\
                  C_ARGUMENTS [r;a;t] s /\
                  LENGTH l = 256 /\
                  (!i. i < 256
                       ==> &0 <= ival (EL i l) /\ ival (EL i l) <= &3328) /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,32)) s =
                    num_of_wordlist mlkem_compress_d5_table)
             (\s. read PC s = word(pc + MLKEM_POLY_COMPRESS_D5_CORE_END) /\
                  read(memory :> bytes(r,160)) s =
                    num_of_wordlist (MAP compress_d5 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `t:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Restate the input bound in terms of val ***)

  SUBGOAL_THEN `!i. i < 256 ==> val (EL i (l:int16 list)) < 3329`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IVAL_VAL; DIMINDEX_16; bitval; BIT_VAL] THEN
    MP_TAC(ISPEC `EL i (l:int16 list)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Digitize the input to match the 256-bit loads of LD2 ***)

  POLY_BYTES256_TAC
   `read(memory :> bytes(a,512)) s0 = num_of_wordlist(l:int16 list)` THEN

  (*** Split the table into its two 128-bit constant vectors ***)

  UNDISCH_TAC
   `read(memory :> bytes(t,32)) s0 =
    num_of_wordlist mlkem_compress_d5_table` THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[mlkem_compress_d5_table; pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Simulate to the end, folding the per-lane formula and packing ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_COMPRESS_D5_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC COMPRESS_D5_SIMPS) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Keep only the memory facts; split the stores into 64-bit words ***)

  DISCARD_NONMATCHING_ASSUMPTIONS
   [`read (memory :> bytes128 a) s = x`;
    `read (memory :> bytes64 a) s = x`;
    `!i. i < 256 ==> val (EL i (l:int16 list)) < 3329`;
    `LENGTH (l:int16 list) = 256`] THEN
  SPLIT_STORES128_TAC THEN

  (*** Replace compress_d5 by the low 5 bits of compress_d5_aarch64 ***)

  SUBGOAL_THEN
   `MAP compress_d5 (l:int16 list) =
    MAP (\x. word_subword (compress_d5_aarch64 x) (0,5)) l`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MAP] THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC COMPRESS_D5_AARCH64_CORRECT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN

  (*** Spell out the output as one 1280-bit word, split into 64 bits ***)

  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
  ASM_SIMP_TAC[EL_MAP; ARITH] THEN
  REPLICATE_TAC 8
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING] THEN
  REWRITE_TAC[VAL_1280_AS_BYTES64] THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Compare each 64-bit word bit by bit ***)

  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_COMPRESS_D5_SUBROUTINE_CORRECT = prove
 (`!r a t (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,160))
            [(word pc,LENGTH mlkem_poly_compress_d5_mc); (a,512); (t,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_compress_d5_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a;t] s /\
                  LENGTH l = 256 /\
                  (!i. i < 256
                       ==> &0 <= ival (EL i l) /\ ival (EL i l) <= &3328) /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,32)) s =
                    num_of_wordlist mlkem_compress_d5_table)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,160)) s =
                    num_of_wordlist (MAP compress_d5 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_COMPRESS_D5_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D5_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_poly_compress_d5" subroutine_signatures)
    MLKEM_POLY_COMPRESS_D5_SUBROUTINE_CORRECT
    MLKEM_POLY_COMPRESS_D5_EXEC;;

let MLKEM_POLY_COMPRESS_D5_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a t pc returnaddress.
           ALL (nonoverlapping (r,160))
               [word pc,LENGTH mlkem_poly_compress_d5_mc; a,512; t,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_poly_compress_d5_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a; t] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a t r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; t,32; r,160] [r,160])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_POLY_COMPRESS_D5_EXEC);;
