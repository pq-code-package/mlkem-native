(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a byte array into polynomial coefficients in 12-bit chunks.  *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_frombytes_aarch64_asm.o";;
 ****)

let mlkem_poly_frombytes_mc = define_assert_from_elf
  "mlkem_poly_frombytes_mc" "aarch64/mlkem/mlkem_poly_frombytes_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x4f00e5f0;       (* arm_MOVI Q16 (word 1085102592571150095) *)
  0xd2800102;       (* arm_MOV X2 (rvalue (word 8)) *)
  0x4cdf4020;       (* arm_LD3 [Q0; Q1; Q2] X1 (Postimmediate_Offset (word 48)) 128 8 *)
  0x4e301c23;       (* arm_AND_VEC Q3 Q1 Q16 128 *)
  0x4e033804;       (* arm_ZIP1 Q4 Q0 Q3 8 128 *)
  0x4e037806;       (* arm_ZIP2 Q6 Q0 Q3 8 128 *)
  0x4e023825;       (* arm_ZIP1 Q5 Q1 Q2 8 128 *)
  0x4e027827;       (* arm_ZIP2 Q7 Q1 Q2 8 128 *)
  0x6f1c04a5;       (* arm_USHR_VEC Q5 Q5 4 16 128 *)
  0x6f1c04e7;       (* arm_USHR_VEC Q7 Q7 4 16 128 *)
  0x4c9f8404;       (* arm_ST2 Q4 Q5 X0 (Postimmediate_Offset (word 32)) 128 16 *)
  0x4c9f8406;       (* arm_ST2 Q6 Q7 X0 (Postimmediate_Offset (word 32)) 128 16 *)
  0xf1000442;       (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  0xb5fffea2;       (* arm_CBNZ X2 (word 2097108) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_FROMBYTES_EXEC = ARM_MK_EXEC_RULE mlkem_poly_frombytes_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_FROMBYTES_MC =
  REWRITE_CONV[mlkem_poly_frombytes_mc] `LENGTH mlkem_poly_frombytes_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_FROMBYTES_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_FROMBYTES_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_FROMBYTES_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_FROMBYTES_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_FROMBYTES_CORE_START = new_definition
  `MLKEM_POLY_FROMBYTES_CORE_START = MLKEM_POLY_FROMBYTES_PREAMBLE_LENGTH`;;

let MLKEM_POLY_FROMBYTES_CORE_END = new_definition
  `MLKEM_POLY_FROMBYTES_CORE_END =
   LENGTH mlkem_poly_frombytes_mc - MLKEM_POLY_FROMBYTES_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_FROMBYTES_MC;
              MLKEM_POLY_FROMBYTES_CORE_START; MLKEM_POLY_FROMBYTES_CORE_END;
              MLKEM_POLY_FROMBYTES_PREAMBLE_LENGTH;
              MLKEM_POLY_FROMBYTES_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;

(* The 384-byte encoding of 256 12-bit words: byte 3 * i + 0 is the low
   8 bits of word 2 * i, byte 3 * i + 1 joins the top 4 bits of word 2 * i
   with the low 4 bits of word 2 * i + 1, and byte 3 * i + 2 is the top
   8 bits of word 2 * i + 1. *)

let NUM_OF_WORDLIST_12_AS_BYTES = prove
 (`!l:(12 word)list.
      LENGTH l = 256
      ==> num_of_wordlist l =
          num_of_wordlist
           (list_of_seq
             (\j. let i = j DIV 3 and r = j MOD 3 in
                  if r = 0 then word_zx(EL (2 * i) l):byte
                  else if r = 2 then word_subword (EL(2 * i + 1) l) (4,8)
                  else word_join (word_subword (EL(2 * i + 1) l) (0,4):nybble)
                                 (word_subword (EL(2 * i) l) (8,4):nybble))
             384)`,
  REPEAT STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
  CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[num_of_wordlist; VAL; DIMINDEX_8; DIMINDEX_12] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ABBREV_TAC `twae = &2:real` THEN REAL_ARITH_TAC);;

(* Build the string of a balanced word_join tree from a list of term
   strings of width w bits, least significant first. *)

let rec mk_join_tree_string w elems =
  match elems with
    [x] -> x
  | _ ->
    let rec pairs l =
      match l with
        lo::hi::rest ->
          Printf.sprintf "(word_join %s %s:(%d)word)" hi lo (2 * w) ::
          pairs rest
      | [] -> []
      | _ -> failwith "mk_join_tree_string" in
    mk_join_tree_string (2 * w) (pairs elems);;

(* LD3 with 8-bit lanes: lane i of the j-th destination register is byte
   3 * i + j of the 384-bit input. *)

let WORD_SUBDEINTERLEAVE_3_8 =
  let mk j =
    let bytes = map (fun i ->
      Printf.sprintf "(word_subword (z:384 word) (%d,8):byte)"
                     (8 * (3 * i + j)))
      (0--15) in
    let rhs = mk_join_tree_string 8 bytes in
    let tm = parse_term (Printf.sprintf
      "(word_subdeinterleave 3 8 (z:384 word) %d:int128) = %s" j rhs) in
    prove(tm,
      GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
      REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[word_subdeinterleave; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV) in
  GEN `z:384 word` (end_itlist CONJ (map mk (0--2)));;

(* An even coefficient x is the 16-bit lane formed by ZIP1/ZIP2 from
   byte 3 * i of the input, the low 8 bits of x, and byte 3 * i + 1 with
   its top 4 bits cleared by AND, the top 4 bits of x. An odd coefficient
   y is the 16-bit lane formed from bytes 3 * i + 1 and 3 * i + 2, shifted
   right by 4 with USHR. *)

let FROMBYTES_EVEN_LANE = prove
 (`!(x:12 word) (y:12 word).
     word_join (word_and (word 15)
                         (word_join (word_subword y (0,4):nybble)
                                    (word_subword x (8,4):nybble):byte))
               (word_zx x:byte):int16 = word_zx x`,
  CONV_TAC WORD_BLAST);;

let FROMBYTES_ODD_LANE = prove
 (`!(x:12 word) (y:12 word).
     word_ushr (word_join (word_subword y (4,8):byte)
                          (word_join (word_subword y (0,4):nybble)
                                     (word_subword x (8,4):nybble):byte)
                :int16) 4 =
     word_zx y`,
  CONV_TAC WORD_BLAST);;

(* Simplify register and memory contents after each step: resolve the LD3
   de-interleaving into bytes, push subwords through joins and masks, and
   fold the 16-bit lanes into the zero-extended 12-bit inputs. Only
   `read c s = ...` assumptions are rewritten: also normalizing the
   nonoverlapping assumptions breaks the simulation of the stores. *)

let FROMBYTES_SIMPLIFY_TAC =
  let is_read_eq tm =
    is_eq tm &&
    (match lhand tm with
       Comb(Comb(Const("read",_),_),_) -> true
     | _ -> false) in
  let conv =
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [WORD_SUBDEINTERLEAVE_3_8] THENC
    TOP_DEPTH_CONV
     (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
    DEPTH_CONV WORD_NUM_RED_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [FROMBYTES_EVEN_LANE; FROMBYTES_ODD_LANE] in
  RULE_ASSUM_TAC(fun th ->
    if is_read_eq (concl th) then CONV_RULE (RAND_CONV conv) th else th);;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_FROMBYTES_CORRECT = prove
 (`!r a (l:(12 word) list) pc.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_frombytes_mc); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_frombytes_mc /\
                  read PC s = word (pc + MLKEM_POLY_FROMBYTES_CORE_START) /\
                  C_ARGUMENTS [r;a] s /\
                  LENGTH l = 256 /\
                  read (memory :> bytes(a,384)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + MLKEM_POLY_FROMBYTES_CORE_END) /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP word_zx l:int16 list))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:(12 word) list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN

  (*** Express the input as bytes and split it into 128-bit chunks ***)

  UNDISCH_TAC
   `read(memory :> bytes(a,384)) s0 = num_of_wordlist(l:(12 word) list)` THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP NUM_OF_WORDLIST_12_AS_BYTES th]) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV
   (ONCE_DEPTH_CONV let_CONV THENC
    LIST_OF_SEQ_CONV THENC NUM_REDUCE_CONV)))) THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Unroll and simulate to the end ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_FROMBYTES_EXEC [n] THEN
    FROMBYTES_SIMPLIFY_TAC) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Split the output into 256-bit chunks and match the stores ***)

  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
  CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MAP] THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN
  ASM_REWRITE_TAC[]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_FROMBYTES_SUBROUTINE_CORRECT = prove
 (`!r a (l:(12 word) list) pc returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_frombytes_mc); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_frombytes_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  LENGTH l = 256 /\
                  read (memory :> bytes(a,384)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP word_zx l:int16 list))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_FROMBYTES_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_FROMBYTES_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_frombytes" subroutine_signatures)
    MLKEM_POLY_FROMBYTES_SUBROUTINE_CORRECT
    MLKEM_POLY_FROMBYTES_EXEC;;

let MLKEM_POLY_FROMBYTES_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512))
               [word pc,LENGTH mlkem_poly_frombytes_mc; a,384]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_poly_frombytes_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,384; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_POLY_FROMBYTES_EXEC);;
