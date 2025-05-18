(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "mlkem/poly_mulcache_compute.o";;
****)


let poly_mulcache_compute_mc = define_assert_from_elf
   "poly_mulcache_compute_mc" "mlkem/mlkem_poly_mulcache_compute.o"
   [
       0x5281a025;       (* arm_MOV W5 (rvalue (word 3329)) *)
       0x4e020ca6;       (* arm_DUP_GEN Q6 X5 16 128 *)
       0x5289d7e5;       (* arm_MOV W5 (rvalue (word 20159)) *)
       0x4e020ca7;       (* arm_DUP_GEN Q7 X5 16 128 *)
       0xd2800204;       (* arm_MOV X4 (rvalue (word 16)) *)
       0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
       0x3cc2043b;       (* arm_LDR Q27 X1 (Postimmediate_Offset (word 32)) *)
       0x3cc10457;       (* arm_LDR Q23 X2 (Postimmediate_Offset (word 16)) *)
       0x4e415b7b;       (* arm_UZP2 Q27 Q27 Q1 16 *)
       0x3cc10461;       (* arm_LDR Q1 X3 (Postimmediate_Offset (word 16)) *)
       0x4e779f62;       (* arm_MUL_VEC Q2 Q27 Q23 16 128 *)
       0x6e61b77b;       (* arm_SQRDMULH_VEC Q27 Q27 Q1 16 128 *)
       0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
       0x3dc0043d;       (* arm_LDR Q29 X1 (Immediate_Offset (word 16)) *)
       0x3cc10455;       (* arm_LDR Q21 X2 (Postimmediate_Offset (word 16)) *)
       0x6f464362;       (* arm_MLS_VEC Q2 Q27 (Q6 :> LANE_H 0) 16 128 *)
       0x3cc2043b;       (* arm_LDR Q27 X1 (Postimmediate_Offset (word 32)) *)
       0x3cc10467;       (* arm_LDR Q7 X3 (Postimmediate_Offset (word 16)) *)
       0x4e5d5b7c;       (* arm_UZP2 Q28 Q27 Q29 16 *)
       0x3c810402;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
       0x4e759f82;       (* arm_MUL_VEC Q2 Q28 Q21 16 128 *)
       0x6e67b79b;       (* arm_SQRDMULH_VEC Q27 Q28 Q7 16 128 *)
       0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
       0xb5fffec4;       (* arm_CBNZ X4 (word 2097112) *)
       0x6f464362;       (* arm_MLS_VEC Q2 Q27 (Q6 :> LANE_H 0) 16 128 *)
       0x3c810402;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
       0xd65f03c0        (* arm_RET X30 *)
     ];;

let poly_mulcache_compute_EXEC = ARM_MK_EXEC_RULE poly_mulcache_compute_mc;;

(* ------------------------------------------------------------------------- *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------- *)

let mulcache_zetas = define
   `mulcache_zetas:int list =
     [
       &17;    -- &17;   -- &568;  &568;  &583;   -- &583;  -- &680;  &680;   &1637; -- &1637; &723;
   -- &723;  -- &1041; &1041;  &1100; -- &1100; &1409;  -- &1409; -- &667;  &667;  -- &48;   &48;
   &233;   -- &233;  &756;   -- &756; -- &1173; &1173;  -- &314;  &314;   -- &279; &279;   -- &1626;
   &1626;  &1651;  -- &1651; -- &540; &540;   -- &1540; &1540;  -- &1482; &1482; &952;   -- &952;
   &1461;  -- &1461; -- &642;  &642;  &939;   -- &939;  -- &1021; &1021;  -- &892; &892;   -- &941;
   &941;   &733;   -- &733;  -- &992; &992;   &268;   -- &268;  &641;   -- &641; &1584;  -- &1584;
   -- &1031; &1031;  -- &1292; &1292; -- &109;  &109;   &375;   -- &375;  -- &780; &780;   -- &1239;
   &1239;  &1645;  -- &1645; &1063; -- &1063; &319;   -- &319;  -- &556;  &556;  &757;   -- &757;
   -- &1230; &1230;  &561;   -- &561; -- &863;  &863;   -- &735;  &735;   -- &525; &525;   &1092;
   -- &1092; &403;   -- &403;  &1026; -- &1026; &1143;  -- &1143; -- &1179; &1179; -- &554;  &554;
   &886;   -- &886;  -- &1607; &1607; &1212;  -- &1212; -- &1455; &1455;  &1029; -- &1029; -- &1219;
   &1219;  -- &394;  &394;   &885;  -- &885;  -- &1175; &1175
     ]`;;

let mulcache_zetas_twisted = define
  `mulcache_zetas_twisted: int list =
  [
   &167;    -- &167;  -- &5591;  &5591;   &5739;   -- &5739;  -- &6693;  &6693;   &16113;
   -- &16113; &7117;  -- &7117;  -- &10247; &10247;  &10828;  -- &10828; &13869;  -- &13869;
   -- &6565;  &6565;  -- &472;   &472;    &2293;   -- &2293;  &7441;   -- &7441;  -- &11546;
   &11546;  -- &3091; &3091;   -- &2746;  &2746;   -- &16005; &16005;  &16251;  -- &16251;
   -- &5315;  &5315;  -- &15159; &15159;  -- &14588; &14588;  &9371;   -- &9371;  &14381;
   -- &14381; -- &6319; &6319;   &9243;   -- &9243;  -- &10050; &10050;  -- &8780;  &8780;
   -- &9262;  &9262;  &7215;   -- &7215;  -- &9764;  &9764;   &2638;   -- &2638;  &6309;
   -- &6309;  &15592; -- &15592; -- &10148; &10148;  -- &12717; &12717;  -- &1073;  &1073;
   &3691;   -- &3691; -- &7678;  &7678;   -- &12196; &12196;  &16192;  -- &16192; &10463;
   -- &10463; &3140;  -- &3140;  -- &5473;  &5473;   &7451;   -- &7451;  -- &12107; &12107;
   &5522;   -- &5522; -- &8495;  &8495;   -- &7235;  &7235;   -- &5168;  &5168;   &10749;
   -- &10749; &3967;  -- &3967;  &10099;  -- &10099; &11251;  -- &11251; -- &11605; &11605;
   -- &5453;  &5453;  &8721;   -- &8721;  -- &15818; &15818;  &11930;  -- &11930; -- &14322;
   &14322;  &10129; -- &10129; -- &11999; &11999;  -- &3878;  &3878;   &8711;   -- &8711;
   -- &11566; &11566
  ]`;;

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
                            in (ival z_i == (mulcache (ival o x)) i) (mod &3329)))
      // Register and memory footprint
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst, 256)])
  `;;

(* ------------------------------------------------------------------------- *)
(* Proof                                                                     *)
(* ------------------------------------------------------------------------- *)

let poly_mulcache_compute_SPEC = prove(poly_mulcache_compute_GOAL,
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
    MAP_EVERY (fun n -> ARM_STEPS_TAC poly_mulcache_compute_EXEC [n] THEN
               (SIMD_SIMPLIFY_TAC [barmul]))
              (1--181) THEN
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

    (* Split into one congruence goals per index. *)
    REPEAT CONJ_TAC THEN

    REWRITE_TAC[mulcache; mulcache_zetas_twisted; mulcache_zetas] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN

    (* Instantiate general congruence and bounds rule for Barrett multiplication
     * so it matches the current goal, and add as new assumption. *)
    W (MP_TAC o CONGBOUND_RULE o rand o lhand o rator o snd) THEN
    ASM_REWRITE_TAC [o_THM] THEN

    (* CONGBOUND_RULE gives a correctness and a bounds result -- here, we only
     * need the correctness result since poly_mulcache_compute makes no statement
     * about output coefficient bounds. *)
    MATCH_MP_TAC (TAUT `(x ==> z) ==> (x /\ y ==> z)`) THEN

    REWRITE_TAC [GSYM INT_REM_EQ] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC ((GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES])
              THENC (REPEATC (CHANGED_CONV (ONCE_DEPTH_CONV NUM_RED_CONV)))) THEN

    REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC [REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC
);;
