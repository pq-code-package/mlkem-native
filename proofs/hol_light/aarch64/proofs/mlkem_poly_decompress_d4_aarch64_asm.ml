(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 4 bits.                     *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_common.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_decompress_d4_table.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_decompress_d4_aarch64_asm.o";;
 ****)

let mlkem_poly_decompress_d4_mc = define_assert_from_elf
  "mlkem_poly_decompress_d4_mc" "aarch64/mlkem/mlkem_poly_decompress_d4_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x4c40a051;       (* arm_LDP Q17 Q18 X2 No_Offset *)
  0x4f00e5f3;       (* arm_MOVI Q19 (word 1085102592571150095) *)
  0xd2800103;       (* arm_MOV X3 (rvalue (word 8)) *)
  0x4cdf7020;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 16)) *)
  0x4e331c01;       (* arm_AND_VEC Q1 Q0 Q19 128 *)
  0x6f0c0402;       (* arm_USHR_VEC Q2 Q0 4 8 128 *)
  0x4e023823;       (* arm_ZIP1 Q3 Q1 Q2 8 128 *)
  0x4e027830;       (* arm_ZIP2 Q16 Q1 Q2 8 128 *)
  0x4e030224;       (* arm_TBL Q4 [Q17] Q3 128 *)
  0x4e030245;       (* arm_TBL Q5 [Q18] Q3 128 *)
  0x4e100226;       (* arm_TBL Q6 [Q17] Q16 128 *)
  0x4e100247;       (* arm_TBL Q7 [Q18] Q16 128 *)
  0x4c9f8004;       (* arm_ST2 Q4 Q5 X0 (Postimmediate_Offset (word 32)) 128 8 *)
  0x4c9f8006;       (* arm_ST2 Q6 Q7 X0 (Postimmediate_Offset (word 32)) 128 8 *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0xb5fffe83;       (* arm_CBNZ X3 (word 2097104) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_DECOMPRESS_D4_EXEC = ARM_MK_EXEC_RULE mlkem_poly_decompress_d4_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D4_MC =
  REWRITE_CONV[mlkem_poly_decompress_d4_mc] `LENGTH mlkem_poly_decompress_d4_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_DECOMPRESS_D4_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D4_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_DECOMPRESS_D4_CORE_START = new_definition
  `MLKEM_POLY_DECOMPRESS_D4_CORE_START = MLKEM_POLY_DECOMPRESS_D4_PREAMBLE_LENGTH`;;

let MLKEM_POLY_DECOMPRESS_D4_CORE_END = new_definition
  `MLKEM_POLY_DECOMPRESS_D4_CORE_END =
   LENGTH mlkem_poly_decompress_d4_mc - MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D4_MC;
               MLKEM_POLY_DECOMPRESS_D4_CORE_START;
               MLKEM_POLY_DECOMPRESS_D4_CORE_END;
               MLKEM_POLY_DECOMPRESS_D4_PREAMBLE_LENGTH;
               MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Per-coefficient lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Split the 128-byte input into eight 128-bit words of 32 coefficients,
 * one for each loop iteration and each 16-byte load. *)

let NUM_OF_WORDLIST_SPLIT_4_256 = mk_split_theorem 4 256 32;;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D4 = mk_subword_cases 4 32;;

(* The code looks up each coefficient x twice with TBL: in the low bytes of
 * Decompress_4, the first 16 bytes of mlkem_decompress_d4_table, and in
 * the high bytes, the last 16 bytes. ST2 joins the two bytes into a 16-bit
 * lane. The two 128-bit words below are these halves of the table, as
 * they appear after symbolic simulation. We prove the lookup correct for
 * each of the 16 values of x. *)

let DECOMPRESS_D4_TBL = prove
 (`!x:4 word.
     word_join
      (word_subword (word 0x0c0b0a09080807060504040302010000:int128)
                    (8 * val x,8):byte)
      (word_subword (word 0x316191c1f1215181b0e0104070a0d000:int128)
                    (8 * val x,8):byte):int16 =
     decompress_d4 x`,
  GEN_TAC THEN REWRITE_TAC[decompress_d4] THEN
  MP_TAC(ISPEC `x:4 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(x:4 word)`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]);;

(* The TBL index is the low nibble of an input byte b (AND with 0x0f) for
 * the even coefficient in b, and its high nibble (USHR by 4) for the odd
 * one. *)

let DECOMPRESS_D4_TBL_LO = prove
 (`!b:byte.
     word_join
      (word_subword (word 0x0c0b0a09080807060504040302010000:int128)
                    (8 * val(word_and (word 15) b:byte),8):byte)
      (word_subword (word 0x316191c1f1215181b0e0104070a0d000:int128)
                    (8 * val(word_and (word 15) b:byte),8):byte):int16 =
     decompress_d4 (word_subword b (0,4))`,
  GEN_TAC THEN REWRITE_TAC[GSYM DECOMPRESS_D4_TBL] THEN
  SUBGOAL_THEN
   `val(word_and (word 15) b:byte) = val(word_subword b (0,4):4 word)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN CONV_TAC WORD_BLAST);;

let DECOMPRESS_D4_TBL_HI = prove
 (`!b:byte.
     word_join
      (word_subword (word 0x0c0b0a09080807060504040302010000:int128)
                    (8 * val(word_ushr b 4:byte),8):byte)
      (word_subword (word 0x316191c1f1215181b0e0104070a0d000:int128)
                    (8 * val(word_ushr b 4:byte),8):byte):int16 =
     decompress_d4 (word_subword b (4,4))`,
  GEN_TAC THEN REWRITE_TAC[GSYM DECOMPRESS_D4_TBL] THEN
  SUBGOAL_THEN
   `val(word_ushr b 4:byte) = val(word_subword b (4,4):4 word)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN CONV_TAC WORD_BLAST);;

(* After the rewrites above, an output lane is decompress_d4 applied to a
 * nibble of a byte of an input word; merge the two subword operations. *)

let WORD_SUBWORD_SUBWORD_D4 = prove
 (`!(w:int128) p q.
     q + 4 <= 8
     ==> word_subword (word_subword w (p,8):byte) (q,4):4 word =
         word_subword w (p + q,4)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_4; DIMINDEX_8] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 4 ==> i < MIN 4 4`;
               ARITH_RULE `q + 4 <= 8 /\ i < 4 ==> q + i < MIN 8 8`;
               ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_DECOMPRESS_D4_CORRECT = prove
 (`!r a t (l:(4 word) list) pc.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d4_mc); (a,128); (t,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d4_mc /\
                  read PC s = word (pc + MLKEM_POLY_DECOMPRESS_D4_CORE_START) /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,128)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,32)) s =
                    num_of_wordlist mlkem_decompress_d4_table)
             (\s. read PC s = word(pc + MLKEM_POLY_DECOMPRESS_D4_CORE_END) /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d4 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `t:int64`; `l:(4 word) list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Split the input into eight 128-bit words matching the loads ***)

  UNDISCH_TAC
   `read(memory :> bytes(a,128)) s0 = num_of_wordlist(l:(4 word) list)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NUM_OF_WORDLIST_SPLIT_4_256 th]) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP; o_DEF] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Split the table into its two 128-bit halves ***)

  UNDISCH_TAC
   `read(memory :> bytes(t,32)) s0 = num_of_wordlist mlkem_decompress_d4_table` THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[mlkem_decompress_d4_table; pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Unroll and simulate to the end ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_DECOMPRESS_D4_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC []) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Express each output lane as decompress_d4 of an input coefficient ***)

  MAP_EVERY (fun i -> SUBGOAL_THEN
    (subst [mk_small_numeral (32 * i), `i:num`]
      `LENGTH (SUB_LIST (i,32) (l:(4 word) list)) = 32`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC])
    (0--7) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    check (can (term_match [] `read (memory :> bytes256 r) s = xxx`) o
           concl))) THEN
  REWRITE_TAC[DECOMPRESS_D4_TBL_LO; DECOMPRESS_D4_TBL_HI] THEN
  IMP_REWRITE_TAC[WORD_SUBWORD_SUBWORD_D4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D4 THEN
  UNDISCH_THEN `LENGTH (l:(4 word) list) = 256`
   (fun th -> CONV_TAC(TOP_SWEEP_CONV(EL_SUB_LIST_CONV th)) THEN
              ASSUME_TAC th) THEN
  REPEAT DISCH_TAC THEN

  (*** Spell out the output list and compare 256 bits at a time ***)

  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_SWEEP_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP] THEN
  REPLICATE_TAC 4
   (CONV_TAC(ONCE_REWRITE_CONV[GSYM NUM_OF_PAIR_WORDLIST])) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM BYTES256_WBYTES]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_DECOMPRESS_D4_SUBROUTINE_CORRECT = prove
 (`!r a t (l:(4 word) list) pc returnaddress.
        LENGTH l = 256 /\
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_poly_decompress_d4_mc); (a,128); (t,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_decompress_d4_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a;t] s /\
                  read (memory :> bytes(a,128)) s = num_of_wordlist l /\
                  read (memory :> bytes(t,32)) s =
                    num_of_wordlist mlkem_decompress_d4_table)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,512)) s =
                    num_of_wordlist (MAP decompress_d4 l) /\
                  (!i. i < 256
                       ==> &0 <= ival(EL i (MAP decompress_d4 l)) /\
                           ival(EL i (MAP decompress_d4 l)) < &3329))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_DECOMPRESS_D4_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D4_CORRECT) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP; IVAL_DECOMPRESS_D4_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_poly_decompress_d4" subroutine_signatures)
    MLKEM_POLY_DECOMPRESS_D4_SUBROUTINE_CORRECT
    MLKEM_POLY_DECOMPRESS_D4_EXEC;;

let MLKEM_POLY_DECOMPRESS_D4_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a t (l:(4 word) list) pc returnaddress.
           LENGTH l = 256 /\
           ALL (nonoverlapping (r,512))
               [word pc,LENGTH mlkem_poly_decompress_d4_mc; a,128; t,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_poly_decompress_d4_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a; t] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a t r pc returnaddress /\
                        memaccess_inbounds e2 [a,128; t,32; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_DECOMPRESS_D4_EXEC);;
