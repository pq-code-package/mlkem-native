(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
 load_path := "/Users/beckphan/repos/s2n-bignum" :: !load_path;
 load_path := "/Users/beckphan/repos/mlkem-native/proofs/hol_light/arm" :: !load_path;

 needs "arm/proofs/base.ml";;

 needs "proofs/mlkem_specs.ml";;
 needs "proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "mlkem/mlkem_poly_tobytes.o";;
 ****)

let poly_tomont_asm_mc = define_assert_from_elf
  "poly_tomont_asm_mc" "mlkem/mlkem_poly_tobytes.o"
     [
        0xd2800202;       (* arm_MOV X2 (rvalue (word 16)) *)
        0x3cc20426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0038;       (* arm_LDR Q24 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc2043e;       (* arm_LDR Q30 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0036;       (* arm_LDR Q22 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc20425;       (* arm_LDR Q5 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0031;       (* arm_LDR Q17 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc20433;       (* arm_LDR Q19 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0xd342fc42;       (* arm_LSR X2 X2 2 *)
        0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
        0x4e5818d9;       (* arm_UZP1 Q25 Q6 Q24 16 *)
        0x4e5858c6;       (* arm_UZP2 Q6 Q6 Q24 16 *)
        0x0e212b38;       (* arm_XTN Q24 Q25 8 *)
        0x0f088739;       (* arm_SHRN Q25 Q25 8 8 *)
        0x0e2128d2;       (* arm_XTN Q18 Q6 8 *)
        0x0f0c84da;       (* arm_SHRN Q26 Q6 4 8 *)
        0x2f0c5659;       (* arm_SLI_VEC Q25 Q18 4 64 8 *)
        0x0c9f4018;       (* arm_ST3 Q24 Q25 Q26 X0 (Postimmediate_Offset (word 24)) *)
        0x4e561bd9;       (* arm_UZP1 Q25 Q30 Q22 16 *)
        0x4e565bc6;       (* arm_UZP2 Q6 Q30 Q22 16 *)
        0x0e212b38;       (* arm_XTN Q24 Q25 8 *)
        0x0e2128d2;       (* arm_XTN Q18 Q6 8 *)
        0x4e5118be;       (* arm_UZP1 Q30 Q5 Q17 16 *)
        0x4e5158b6;       (* arm_UZP2 Q22 Q5 Q17 16 *)
        0x0e212bc5;       (* arm_XTN Q5 Q30 8 *)
        0x0e212ad1;       (* arm_XTN Q17 Q22 8 *)
        0x4e441a7c;       (* arm_UZP1 Q28 Q19 Q4 16 *)
        0x4e445a73;       (* arm_UZP2 Q19 Q19 Q4 16 *)
        0x0e212b84;       (* arm_XTN Q4 Q28 8 *)
        0x0e212a74;       (* arm_XTN Q20 Q19 8 *)
        0x0f088739;       (* arm_SHRN Q25 Q25 8 8 *)
        0x2f0c5659;       (* arm_SLI_VEC Q25 Q18 4 64 8 *)
        0x0f0c84da;       (* arm_SHRN Q26 Q6 4 8 *)
        0x0c9f4018;       (* arm_ST3 Q24 Q25 Q26 X0 (Postimmediate_Offset (word 24)) *)
        0x0f0887c6;       (* arm_SHRN Q6 Q30 8 8 *)
        0x2f0c5626;       (* arm_SLI_VEC Q6 Q17 4 64 8 *)
        0x0f0c86c7;       (* arm_SHRN Q7 Q22 4 8 *)
        0x0c9f4005;       (* arm_ST3 Q5 Q6 Q7 X0 (Postimmediate_Offset (word 24)) *)
        0x0f088785;       (* arm_SHRN Q5 Q28 8 8 *)
        0x0f0c8666;       (* arm_SHRN Q6 Q19 4 8 *)
        0x2f0c5685;       (* arm_SLI_VEC Q5 Q20 4 64 8 *)
        0x0c9f4004;       (* arm_ST3 Q4 Q5 Q6 X0 (Postimmediate_Offset (word 24)) *)
        0x3cc20426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0038;       (* arm_LDR Q24 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc2043e;       (* arm_LDR Q30 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0036;       (* arm_LDR Q22 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc20425;       (* arm_LDR Q5 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0031;       (* arm_LDR Q17 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc20433;       (* arm_LDR Q19 X1 (Postimmediate_Offset (word 32)) *)
        0x3cdf0024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 18446744073709551600)) *)
        0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
        0xb5fffae2;       (* arm_CBNZ X2 (word 2096988) *)
        0x4e561bd9;       (* arm_UZP1 Q25 Q30 Q22 16 *)
        0x4e565bd2;       (* arm_UZP2 Q18 Q30 Q22 16 *)
        0x4e5818de;       (* arm_UZP1 Q30 Q6 Q24 16 *)
        0x4e5858c6;       (* arm_UZP2 Q6 Q6 Q24 16 *)
        0x4e5118b8;       (* arm_UZP1 Q24 Q5 Q17 16 *)
        0x4e5158b6;       (* arm_UZP2 Q22 Q5 Q17 16 *)
        0x4e441a65;       (* arm_UZP1 Q5 Q19 Q4 16 *)
        0x4e445a71;       (* arm_UZP2 Q17 Q19 Q4 16 *)
        0x0e212b33;       (* arm_XTN Q19 Q25 8 *)
        0x0f088734;       (* arm_SHRN Q20 Q25 8 8 *)
        0x0e212a59;       (* arm_XTN Q25 Q18 8 *)
        0x0f0c8655;       (* arm_SHRN Q21 Q18 4 8 *)
        0x0e212bdc;       (* arm_XTN Q28 Q30 8 *)
        0x0f0887dd;       (* arm_SHRN Q29 Q30 8 8 *)
        0x0e2128d2;       (* arm_XTN Q18 Q6 8 *)
        0x0f0c84de;       (* arm_SHRN Q30 Q6 4 8 *)
        0x0e212b01;       (* arm_XTN Q1 Q24 8 *)
        0x0f088702;       (* arm_SHRN Q2 Q24 8 8 *)
        0x0e212ac6;       (* arm_XTN Q6 Q22 8 *)
        0x0f0c86c3;       (* arm_SHRN Q3 Q22 4 8 *)
        0x0e2128b6;       (* arm_XTN Q22 Q5 8 *)
        0x0f0884b7;       (* arm_SHRN Q23 Q5 8 8 *)
        0x0e212a25;       (* arm_XTN Q5 Q17 8 *)
        0x0f0c8638;       (* arm_SHRN Q24 Q17 4 8 *)
        0x2f0c5734;       (* arm_SLI_VEC Q20 Q25 4 64 8 *)
        0x2f0c565d;       (* arm_SLI_VEC Q29 Q18 4 64 8 *)
        0x0c9f401c;       (* arm_ST3 Q28 Q29 Q30 X0 (Postimmediate_Offset (word 24)) *)
        0x0c9f4013;       (* arm_ST3 Q19 Q20 Q21 X0 (Postimmediate_Offset (word 24)) *)
        0x2f0c54c2;       (* arm_SLI_VEC Q2 Q6 4 64 8 *)
        0x0c9f4001;       (* arm_ST3 Q1 Q2 Q3 X0 (Postimmediate_Offset (word 24)) *)
        0x2f0c54b7;       (* arm_SLI_VEC Q23 Q5 4 64 8 *)
        0x0c9f4016;       (* arm_ST3 Q22 Q23 Q24 X0 (Postimmediate_Offset (word 24)) *)
        0xd65f03c0        (* arm_RET X30 *)
      ];;

 let poly_tobytes_EXEC = ARM_MK_EXEC_RULE poly_tobytes_mc;;

 let poly_tobytes_GOAL = `!dst src x pc.
   ALL (nonoverlapping (dst,384))
     [(word pc, 344); (src, 512)]
   ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) poly_tobytes_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [dst; src] s /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add src (word(2 * i)))) s = x i)
      (\s. read PC s = word(pc + 340) /\
           !i. i < 256
               ==> ival(read(memory :> bytes16
                          (word_add dst (word(2 * i)))) s) = &0 // TODO
      )
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,384)])`;;

  (* ------------------------------------------------------------------------- *)
  (* Proof                                                                     *)
  (* ------------------------------------------------------------------------- *)

 let poly_tobytes_SPEC = prove(poly_tobytes_GOAL,

       REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
        MODIFIABLE_SIMD_REGS;
        NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst poly_tobytes_EXEC] THEN
      REPEAT STRIP_TAC THEN

      (* Split quantified assumptions into separate cases *)
      CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
      CONV_TAC((ONCE_DEPTH_CONV NUM_MULT_CONV) THENC (ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN

      (* Initialize symbolic execution *)
      ENSURES_INIT_TAC "s0" THEN

      (* Rewrite memory-read assumptions from 16-bit granularity
       * to 128-bit granularity. *)
      MEMORY_128_FROM_16_TAC "src" 32 THEN
      ASM_REWRITE_TAC [WORD_ADD_0] THEN
      (* Forget original shape of assumption *)
      DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 src) s = x`] THEN

      (* Symbolic execution
         Note that we simplify eagerly after every step.
         This reduces the proof time *)
      REPEAT STRIP_TAC THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [1] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [2] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [3] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [4] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [5] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [6] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [7] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [8] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [9] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [10] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [11] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [12] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [13] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [14] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [15] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [16] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [17] THEN (SIMD_SIMPLIFY_TAC []) THEN
      ARM_STEPS_TAC poly_tobytes_EXEC [18] THEN (SIMD_SIMPLIFY_TAC []) THEN

      (* Failure at this step *)
      (*  "NONOVERLAPPING_TAC: inapplicable goal: orthogonal_components (bytes (word pc,344)) (wbytes (word_add dst (word 0)))". *)
      ARM_STEPS_TAC poly_tobytes_EXEC [19] THEN (SIMD_SIMPLIFY_TAC []) THEN

      MAP_EVERY (fun n -> ARM_STEPS_TAC poly_tobytes_EXEC [n] THEN
                 (SIMD_SIMPLIFY_TAC [])) (1--805) THEN

      ENSURES_FINAL_STATE_TAC THEN
      REPEAT CONJ_TAC THEN
      ASM_REWRITE_TAC [] THEN

      (* Reverse restructuring *)
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        CONV_RULE (SIMD_SIMPLIFY_CONV []) o
        CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
        check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

      (* Split quantified post-condition into separate cases *)
      CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV
               THENC (TRY_CONV (ONCE_DEPTH_CONV NUM_ADD_CONV))) THEN
      CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC [WORD_ADD_0] THEN

     (* TODO: Finish *)

  );;
