(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 4 bits.                         *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_compress_d4_aarch64_asm.o";;
 ****)

let mlkem_poly_compress_d4_mc = define_assert_from_elf
  "mlkem_poly_compress_d4_mc" "aarch64/mlkem/mlkem_poly_compress_d4_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x52813b03;       (* arm_MOV W3 (rvalue (word 2520)) *)
  0x4e020c78;       (* arm_DUP_GEN Q24 X3 16 128 *)
  0x4f00e519;       (* arm_MOVI Q25 (word 578721382704613384) *)
  0xd2800082;       (* arm_MOV X2 (rvalue (word 4)) *)
  0xacc40420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&128))) *)
  0xad7d0c22;       (* arm_LDP Q2 Q3 X1 (Immediate_Offset (iword (-- &96))) *)
  0xad7e1424;       (* arm_LDP Q4 Q5 X1 (Immediate_Offset (iword (-- &64))) *)
  0xad7f1c26;       (* arm_LDP Q6 Q7 X1 (Immediate_Offset (iword (-- &32))) *)
  0x4e78b400;       (* arm_SQDMULH_VEC Q0 Q0 Q24 16 128 *)
  0x4e78b421;       (* arm_SQDMULH_VEC Q1 Q1 Q24 16 128 *)
  0x4e78b442;       (* arm_SQDMULH_VEC Q2 Q2 Q24 16 128 *)
  0x4e78b463;       (* arm_SQDMULH_VEC Q3 Q3 Q24 16 128 *)
  0x4e78b484;       (* arm_SQDMULH_VEC Q4 Q4 Q24 16 128 *)
  0x4e78b4a5;       (* arm_SQDMULH_VEC Q5 Q5 Q24 16 128 *)
  0x4e78b4c6;       (* arm_SQDMULH_VEC Q6 Q6 Q24 16 128 *)
  0x4e78b4e7;       (* arm_SQDMULH_VEC Q7 Q7 Q24 16 128 *)
  0x4e011810;       (* arm_UZP1 Q16 Q0 Q1 8 *)
  0x4e031851;       (* arm_UZP1 Q17 Q2 Q3 8 *)
  0x4e111a14;       (* arm_UZP1 Q20 Q16 Q17 8 *)
  0x4e115a15;       (* arm_UZP2 Q21 Q16 Q17 8 *)
  0x4e051892;       (* arm_UZP1 Q18 Q4 Q5 8 *)
  0x4e0718d3;       (* arm_UZP1 Q19 Q6 Q7 8 *)
  0x4e131a56;       (* arm_UZP1 Q22 Q18 Q19 8 *)
  0x4e135a57;       (* arm_UZP2 Q23 Q18 Q19 8 *)
  0x4e398694;       (* arm_ADD_VEC Q20 Q20 Q25 8 128 *)
  0x4e3986b5;       (* arm_ADD_VEC Q21 Q21 Q25 8 128 *)
  0x6f0c4695;       (* arm_SRI_VEC Q21 Q20 4 8 128 *)
  0x4e3986d6;       (* arm_ADD_VEC Q22 Q22 Q25 8 128 *)
  0x4e3986f7;       (* arm_ADD_VEC Q23 Q23 Q25 8 128 *)
  0x6f0c46d7;       (* arm_SRI_VEC Q23 Q22 4 8 128 *)
  0x4c9f7015;       (* arm_STR Q21 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f7017;       (* arm_STR Q23 X0 (Postimmediate_Offset (word 16)) *)
  0xf1000442;       (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  0xb5fffc62;       (* arm_CBNZ X2 (word 2097036) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_COMPRESS_D4_EXEC = ARM_MK_EXEC_RULE mlkem_poly_compress_d4_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_COMPRESS_D4_MC =
  REWRITE_CONV[mlkem_poly_compress_d4_mc] `LENGTH mlkem_poly_compress_d4_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_COMPRESS_D4_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D4_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_COMPRESS_D4_CORE_START = new_definition
  `MLKEM_POLY_COMPRESS_D4_CORE_START = MLKEM_POLY_COMPRESS_D4_PREAMBLE_LENGTH`;;

let MLKEM_POLY_COMPRESS_D4_CORE_END = new_definition
  `MLKEM_POLY_COMPRESS_D4_CORE_END =
   LENGTH mlkem_poly_compress_d4_mc - MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_COMPRESS_D4_MC;
               MLKEM_POLY_COMPRESS_D4_CORE_START;
               MLKEM_POLY_COMPRESS_D4_CORE_END;
               MLKEM_POLY_COMPRESS_D4_PREAMBLE_LENGTH;
               MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Per-coefficient formula.                                                  *)
(*                                                                           *)
(* Each coefficient x passes through                                         *)
(*                                                                           *)
(*   sqdmulh x, 2520     (16-bit lanes)                                      *)
(*   uzp1, uzp1/uzp2     (keep the low byte)                                 *)
(*   add 8               (8-bit lanes)                                       *)
(*                                                                           *)
(* and the final sri keeps bits 4..7 of the result. compress_d4_aarch64 is   *)
(* the byte computed by these steps, stated in the form that the symbolic   *)
(* simulation produces, so that SIMD_SIMPLIFY_TAC can fold it.               *)
(* ------------------------------------------------------------------------- *)

let compress_d4_aarch64 = new_definition
 `compress_d4_aarch64 (x:int16) : byte =
  word_add (word_subword
             (iword_saturate((&2 * ival x * &2520) div &65536):int16)
             (0,8):byte)
           (word 8)`;;

(* Bits 4..7 of compress_d4_aarch64 x are compress_d4 x for all x in
 * [0, 3328]; checked for each of the 3329 values. *)
let COMPRESS_D4_AARCH64_CORRECT = PROVE_BY_COEFF_ENUMERATION
  [compress_d4_aarch64; compress_d4]
  `!x:int16. val x < 3329
             ==> word_subword (compress_d4_aarch64 x) (4,4) = compress_d4 x`;;

(* sri d.16b, n.16b, #4 keeps bits 4..7 of d and puts bits 4..7 of n
 * below them. *)
let WORD_SRI_4_JOIN = WORD_BLAST
 `!a b:byte. word_or (word_ushr a 4) (word_and b (word 240)) =
             word_join (word_subword b (4,4):4 word)
                       (word_subword a (4,4):4 word)`;;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D4_CORRECT = prove
 (`!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,128))
            [(word pc,LENGTH mlkem_poly_compress_d4_mc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_compress_d4_mc /\
                  read PC s = word (pc + MLKEM_POLY_COMPRESS_D4_CORE_START) /\
                  C_ARGUMENTS [r;a] s /\
                  LENGTH l = 256 /\
                  (!i. i < 256
                       ==> &0 <= ival (EL i l) /\ ival (EL i l) <= &3328) /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + MLKEM_POLY_COMPRESS_D4_CORE_END) /\
                  read(memory :> bytes(r,128)) s =
                    num_of_wordlist (MAP compress_d4 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
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

  (*** Digitize the input to match the 128-bit loads ***)

  POLY_BYTES128_TAC
   `read(memory :> bytes(a,512)) s0 = num_of_wordlist(l:int16 list)` THEN

  (*** Simulate to the end, folding the per-lane formula ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_COMPRESS_D4_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC [compress_d4_aarch64]) 1 THEN

  (*** Express the stored bytes in terms of compress_d4 ***)

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SRI_4_JOIN]) THEN
  REWRITE_ASSUMS_WITH_EL_BOUND_TAC
   `!i. i < 256 ==> val (EL i (l:int16 list)) < 3329`
   COMPRESS_D4_AARCH64_CORRECT THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Split the output into 128-bit words and match the stores ***)

  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
  ASM_SIMP_TAC[EL_MAP; ARITH] THEN
  REPLICATE_TAC 5
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN
  ASM_REWRITE_TAC[]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_COMPRESS_D4_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,128))
            [(word pc,LENGTH mlkem_poly_compress_d4_mc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_compress_d4_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  LENGTH l = 256 /\
                  (!i. i < 256
                       ==> &0 <= ival (EL i l) /\ ival (EL i l) <= &3328) /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,128)) s =
                    num_of_wordlist (MAP compress_d4 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_COMPRESS_D4_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D4_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_poly_compress_d4" subroutine_signatures)
    MLKEM_POLY_COMPRESS_D4_SUBROUTINE_CORRECT
    MLKEM_POLY_COMPRESS_D4_EXEC;;

let MLKEM_POLY_COMPRESS_D4_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,128))
               [word pc,LENGTH mlkem_poly_compress_d4_mc; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_poly_compress_d4_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,128] [r,128])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_POLY_COMPRESS_D4_EXEC);;
