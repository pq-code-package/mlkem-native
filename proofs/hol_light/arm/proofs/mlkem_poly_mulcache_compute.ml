(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;
needs "proofs/mlkem_zetas.ml";;

(**** print_literal_from_elf "mlkem/poly_mulcache_compute.o";;
****)


let poly_mulcache_compute_mc = define_assert_from_elf
   "poly_mulcache_compute_mc" "mlkem/mlkem_poly_mulcache_compute.o"
(*** BYTECODE START ***)
[
  0x5281a025;       (* arm_MOV W5 (rvalue (word 3329)) *)
  0x4e020ca6;       (* arm_DUP_GEN Q6 X5 16 128 *)
  0x5289d7e5;       (* arm_MOV W5 (rvalue (word 20159)) *)
  0x4e020ca7;       (* arm_DUP_GEN Q7 X5 16 128 *)
  0xd2800204;       (* arm_MOV X4 (rvalue (word 16)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0022;       (* arm_LDR Q2 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20433;       (* arm_LDR Q19 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc1047d;       (* arm_LDR Q29 X3 (Postimmediate_Offset (word 16)) *)
  0x3cdf0030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc10452;       (* arm_LDR Q18 X2 (Postimmediate_Offset (word 16)) *)
  0x3cc2043a;       (* arm_LDR Q26 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc10459;       (* arm_LDR Q25 X2 (Postimmediate_Offset (word 16)) *)
  0x4e425805;       (* arm_UZP2 Q5 Q0 Q2 16 *)
  0x3cc1047c;       (* arm_LDR Q28 X3 (Postimmediate_Offset (word 16)) *)
  0x3cdf0027;       (* arm_LDR Q7 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20422;       (* arm_LDR Q2 X1 (Postimmediate_Offset (word 32)) *)
  0x4e505a7b;       (* arm_UZP2 Q27 Q19 Q16 16 *)
  0x6e7db4b0;       (* arm_SQRDMULH_VEC Q16 Q5 Q29 16 128 *)
  0x3cc10471;       (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  0x3cc10473;       (* arm_LDR Q19 X3 (Postimmediate_Offset (word 16)) *)
  0x4e729ca5;       (* arm_MUL_VEC Q5 Q5 Q18 16 128 *)
  0x4e475b5d;       (* arm_UZP2 Q29 Q26 Q7 16 *)
  0x4e799f7a;       (* arm_MUL_VEC Q26 Q27 Q25 16 128 *)
  0x6e7cb764;       (* arm_SQRDMULH_VEC Q4 Q27 Q28 16 128 *)
  0x6f464205;       (* arm_MLS_VEC Q5 Q16 (Q6 :> LANE_H 0) 16 128 *)
  0xd341fc84;       (* arm_LSR X4 X4 1 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x3c810405;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
  0x6e71b7b6;       (* arm_SQRDMULH_VEC Q22 Q29 Q17 16 128 *)
  0x3cc1045c;       (* arm_LDR Q28 X2 (Postimmediate_Offset (word 16)) *)
  0x3cdf0038;       (* arm_LDR Q24 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x6f46409a;       (* arm_MLS_VEC Q26 Q4 (Q6 :> LANE_H 0) 16 128 *)
  0x3cdf0030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc10471;       (* arm_LDR Q17 X3 (Postimmediate_Offset (word 16)) *)
  0x4e7c9fa5;       (* arm_MUL_VEC Q5 Q29 Q28 16 128 *)
  0x4e585857;       (* arm_UZP2 Q23 Q2 Q24 16 *)
  0x3cc10452;       (* arm_LDR Q18 X2 (Postimmediate_Offset (word 16)) *)
  0x6f4642c5;       (* arm_MLS_VEC Q5 Q22 (Q6 :> LANE_H 0) 16 128 *)
  0x4e50581d;       (* arm_UZP2 Q29 Q0 Q16 16 *)
  0x6e73b6e4;       (* arm_SQRDMULH_VEC Q4 Q23 Q19 16 128 *)
  0x3cc20422;       (* arm_LDR Q2 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc10473;       (* arm_LDR Q19 X3 (Postimmediate_Offset (word 16)) *)
  0x3c81041a;       (* arm_STR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x4e729efa;       (* arm_MUL_VEC Q26 Q23 Q18 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fffda4;       (* arm_CBNZ X4 (word 2097076) *)
  0x6f46409a;       (* arm_MLS_VEC Q26 Q4 (Q6 :> LANE_H 0) 16 128 *)
  0x3c810405;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
  0x3cc10445;       (* arm_LDR Q5 X2 (Postimmediate_Offset (word 16)) *)
  0x3cdf0024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e71b7b0;       (* arm_SQRDMULH_VEC Q16 Q29 Q17 16 128 *)
  0x3cc10440;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x4e659fbd;       (* arm_MUL_VEC Q29 Q29 Q5 16 128 *)
  0x4e445852;       (* arm_UZP2 Q18 Q2 Q4 16 *)
  0x3c81041a;       (* arm_STR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e73b651;       (* arm_SQRDMULH_VEC Q17 Q18 Q19 16 128 *)
  0x6f46421d;       (* arm_MLS_VEC Q29 Q16 (Q6 :> LANE_H 0) 16 128 *)
  0x4e609e5a;       (* arm_MUL_VEC Q26 Q18 Q0 16 128 *)
  0x6f46423a;       (* arm_MLS_VEC Q26 Q17 (Q6 :> LANE_H 0) 16 128 *)
  0x3c81041d;       (* arm_STR Q29 X0 (Postimmediate_Offset (word 16)) *)
  0x3c81041a;       (* arm_STR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let poly_mulcache_compute_EXEC = ARM_MK_EXEC_RULE poly_mulcache_compute_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_POLY_MULCACHE_COMPUTE_MC =
  REWRITE_CONV[poly_mulcache_compute_mc] `LENGTH poly_mulcache_compute_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_POLY_MULCACHE_COMPUTE_MC];;

(* ------------------------------------------------------------------------- *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------- *)

let have_mulcache_zetas = define
 `have_mulcache_zetas zetas zetas_twisted s <=>
     (!i. i < 128 ==> read(memory :> bytes16(word_add zetas (word (2*i)))) s =
                         iword (EL i mulcache_zetas)) /\
     (!i. i < 128 ==> read(memory :> bytes16(word_add zetas_twisted (word (2*i)))) s =
                         iword (EL i mulcache_zetas_twisted))
 `;;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/native/aarch64/src/arith_native_aarch64.h *)

let poly_mulcache_compute_GOAL = `forall pc src dst zetas zetas_twisted x y returnaddress.
    ALL (nonoverlapping (dst, 256))
        [(word pc, LENGTH poly_mulcache_compute_mc); (src, 512); (zetas, 256); (zetas_twisted, 256)]
    ==>
    ensures arm
      (\s. // Assert that poly_mulcache_compute is loaded at PC
           aligned_bytes_loaded s (word pc) poly_mulcache_compute_mc /\
           read PC s = word pc  /\
           // Remember LR as point-to-stop
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src; zetas; zetas_twisted] s  /\
           // Give name to 16-bit coefficients stored at src to be
           // able to refer to them in the post-condition
           (!i. i < 256 ==> read(memory :> bytes16(word_add src (word (2 * i)))) s = x i) /\
           // Assert that zetas are correct
           have_mulcache_zetas zetas zetas_twisted s
      )
      (\s. // We have reached the LR
           read PC s = returnaddress /\
           // Odd coefficients have been multiplied with respective root of unity
           (!i. i < 128 ==> let z_i = read(memory :> bytes16(word_add dst (word (2 * i)))) s
                            in (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                                abs(ival z_i) <= &3328))
      // Register and memory footprint
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst, 256)])
  `;;

(* ------------------------------------------------------------------------- *)
(* Proof                                                                     *)
(* ------------------------------------------------------------------------- *)

let poly_mulcache_compute_SPEC = prove(poly_mulcache_compute_GOAL,
    CONV_TAC LENGTH_SIMPLIFY_CONV THEN
    REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
      NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst poly_mulcache_compute_EXEC;
      have_mulcache_zetas] THEN
    REPEAT STRIP_TAC THEN

    (* Split quantified assumptions into separate cases *)
    CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
      (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

    (* Initialize symbolic execution *)
    ENSURES_INIT_TAC "s0" THEN

    (* Rewrite memory-read assumptions from 16-bit granularity
     * to 128-bit granularity. *)
    MEMORY_128_FROM_16_TAC "src" 32 THEN
    MEMORY_128_FROM_16_TAC "dst" 16 THEN
    MEMORY_128_FROM_16_TAC "zetas_twisted" 16 THEN
    MEMORY_128_FROM_16_TAC "zetas" 16 THEN
    ASM_REWRITE_TAC [WORD_ADD_0] THEN
    (* Forget original shape of assumption *)
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 src) s = x`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 dst) s = x`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 zetas) s = x`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 zetas_twisted) s = x`] THEN

    (* Symbolic execution
       Note that we simplify eagerly after every step.
       This reduces the proof time *)
    REPEAT STRIP_TAC THEN
    MAP_UNTIL_TARGET_PC (fun n -> ARM_STEPS_TAC poly_mulcache_compute_EXEC [n] THEN
               (SIMD_SIMPLIFY_TAC [barmul])) 1 THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN
    ASM_REWRITE_TAC [] THEN

    (* Reverse restructuring *)
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

    (* Split quantified post-condition into separate cases *)
    CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC [WORD_ADD_0] THEN

    (* Forget all assumptions *)
    POP_ASSUM_LIST (K ALL_TAC) THEN

    (* Split into pairs of congruence and absolute value goals *)
    REPEAT(W(fun (asl,w) ->
    if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

    REWRITE_TAC[mulcache; mulcache_zetas_twisted; mulcache_zetas] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN

    (* Instantiate general congruence and bounds rule for Barrett multiplication
     * so it matches the current goal, and add as new assumption. *)
    W (MP_TAC o CONGBOUND_RULE o rand o rand o rator o rator o lhand o snd) THEN
    ASM_REWRITE_TAC [o_THM] THEN

    MATCH_MP_TAC MONO_AND THEN (CONJ_TAC THENL [
      (* Correctness *)
      REWRITE_TAC [GSYM INT_REM_EQ; o_THM] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC ((GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES])
                THENC (REPEATC (CHANGED_CONV (ONCE_DEPTH_CONV NUM_RED_CONV)))) THEN
      REWRITE_TAC[INT_REM_EQ] THEN
        REWRITE_TAC [REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
        REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
        CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC

      ;

      (* Bounds *)
      REWRITE_TAC [INT_ABS_BOUNDS] THEN
      MATCH_MP_TAC(INT_ARITH
        `l':int <= l /\ u <= u'
         ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
      CONV_TAC INT_REDUCE_CONV])
);;
