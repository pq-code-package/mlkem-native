(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;
needs "proofs/mlkem_zetas.ml";;

(**** print_literal_from_elf "mlkem/mlkem_ntt.o";;
 ****)

let mlkem_ntt_mc = define_assert_from_elf
 "mlkem_ntt_mc" "mlkem/mlkem_ntt.o"
(*** BYTECODE START ***)
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x5281a025;       (* arm_MOV W5 (rvalue (word 3329)) *)
  0x4e021ca7;       (* arm_INS_GEN Q7 W5 0 16 *)
  0x5289d7e5;       (* arm_MOV W5 (rvalue (word 20159)) *)
  0x4e061ca7;       (* arm_INS_GEN Q7 W5 16 16 *)
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc00005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 0)) *)
  0x3dc0100d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 64)) *)
  0x3dc02003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 128)) *)
  0x3dc03016;       (* arm_LDR Q22 X0 (Immediate_Offset (word 192)) *)
  0x3dc04018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 256)) *)
  0x3dc0700b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 448)) *)
  0x4f408317;       (* arm_MUL_VEC Q23 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc05002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 320)) *)
  0x4f408171;       (* arm_MUL_VEC Q17 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc06013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 384)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4f50d308;       (* arm_SQRDMULH_VEC Q8 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d058;       (* arm_SQRDMULH_VEC Q24 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408042;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d26e;       (* arm_SQRDMULH_VEC Q14 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474117;       (* arm_MLS_VEC Q23 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408268;       (* arm_MUL_VEC Q8 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474302;       (* arm_MLS_VEC Q2 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d178;       (* arm_SQRDMULH_VEC Q24 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x6e7784ab;       (* arm_SUB_VEC Q11 Q5 Q23 16 128 *)
  0x6f4741c8;       (* arm_MLS_VEC Q8 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6285ae;       (* arm_SUB_VEC Q14 Q13 Q2 16 128 *)
  0x4e6285a2;       (* arm_ADD_VEC Q2 Q13 Q2 16 128 *)
  0x4e7784b7;       (* arm_ADD_VEC Q23 Q5 Q23 16 128 *)
  0x6e688473;       (* arm_SUB_VEC Q19 Q3 Q8 16 128 *)
  0x4e688468;       (* arm_ADD_VEC Q8 Q3 Q8 16 128 *)
  0x6f474311;       (* arm_MLS_VEC Q17 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50da78;       (* arm_SQRDMULH_VEC Q24 Q19 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408a73;       (* arm_MUL_VEC Q19 Q19 (Q0 :> LANE_H 4) 16 128 *)
  0x4f70d105;       (* arm_SQRDMULH_VEC Q5 Q8 (Q0 :> LANE_H 3) 16 128 *)
  0x6e7186cd;       (* arm_SUB_VEC Q13 Q22 Q17 16 128 *)
  0x4e7186d1;       (* arm_ADD_VEC Q17 Q22 Q17 16 128 *)
  0x6f474313;       (* arm_MLS_VEC Q19 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d9b8;       (* arm_SQRDMULH_VEC Q24 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x4f4089ad;       (* arm_MUL_VEC Q13 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x4f608108;       (* arm_MUL_VEC Q8 Q8 (Q0 :> LANE_H 2) 16 128 *)
  0x6e738563;       (* arm_SUB_VEC Q3 Q11 Q19 16 128 *)
  0x4e73856b;       (* arm_ADD_VEC Q11 Q11 Q19 16 128 *)
  0x6f47430d;       (* arm_MLS_VEC Q13 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d238;       (* arm_SQRDMULH_VEC Q24 Q17 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608233;       (* arm_MUL_VEC Q19 Q17 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4740a8;       (* arm_MLS_VEC Q8 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d85d1;       (* arm_SUB_VEC Q17 Q14 Q13 16 128 *)
  0x4e6d85ce;       (* arm_ADD_VEC Q14 Q14 Q13 16 128 *)
  0x6f474313;       (* arm_MLS_VEC Q19 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6886f8;       (* arm_SUB_VEC Q24 Q23 Q8 16 128 *)
  0x4e6886e8;       (* arm_ADD_VEC Q8 Q23 Q8 16 128 *)
  0x4f71d1d7;       (* arm_SQRDMULH_VEC Q23 Q14 (Q1 :> LANE_H 3) 16 128 *)
  0x6e738445;       (* arm_SUB_VEC Q5 Q2 Q19 16 128 *)
  0x4e738442;       (* arm_ADD_VEC Q2 Q2 Q19 16 128 *)
  0x4f6181ce;       (* arm_MUL_VEC Q14 Q14 (Q1 :> LANE_H 2) 16 128 *)
  0x4f51d0b3;       (* arm_SQRDMULH_VEC Q19 Q5 (Q1 :> LANE_H 1) 16 128 *)
  0x4f70d84d;       (* arm_SQRDMULH_VEC Q13 Q2 (Q0 :> LANE_H 7) 16 128 *)
  0x4f608842;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 6) 16 128 *)
  0x4f4180a5;       (* arm_MUL_VEC Q5 Q5 (Q1 :> LANE_H 0) 16 128 *)
  0x6f4742ee;       (* arm_MLS_VEC Q14 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51da37;       (* arm_SQRDMULH_VEC Q23 Q17 (Q1 :> LANE_H 5) 16 128 *)
  0x6f4741a2;       (* arm_MLS_VEC Q2 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474265;       (* arm_MLS_VEC Q5 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6e8573;       (* arm_SUB_VEC Q19 Q11 Q14 16 128 *)
  0x4e6e856e;       (* arm_ADD_VEC Q14 Q11 Q14 16 128 *)
  0x6e62850b;       (* arm_SUB_VEC Q11 Q8 Q2 16 128 *)
  0x4f418a31;       (* arm_MUL_VEC Q17 Q17 (Q1 :> LANE_H 4) 16 128 *)
  0x4e628508;       (* arm_ADD_VEC Q8 Q8 Q2 16 128 *)
  0x6e658702;       (* arm_SUB_VEC Q2 Q24 Q5 16 128 *)
  0x4e658718;       (* arm_ADD_VEC Q24 Q24 Q5 16 128 *)
  0x6f4742f1;       (* arm_MLS_VEC Q17 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x3c810408;       (* arm_STR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc00005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 0)) *)
  0x6e718468;       (* arm_SUB_VEC Q8 Q3 Q17 16 128 *)
  0x4e718477;       (* arm_ADD_VEC Q23 Q3 Q17 16 128 *)
  0x3d800c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 48)) *)
  0x3dc0100d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 64)) *)
  0x3d801c18;       (* arm_STR Q24 X0 (Immediate_Offset (word 112)) *)
  0x3dc02003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 128)) *)
  0x3d802c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 176)) *)
  0x3dc03016;       (* arm_LDR Q22 X0 (Immediate_Offset (word 192)) *)
  0x3d803c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 240)) *)
  0x3dc04018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 256)) *)
  0x3d804c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 304)) *)
  0x3dc05002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 320)) *)
  0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
  0x4f408317;       (* arm_MUL_VEC Q23 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x3d806c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 432)) *)
  0x3dc0700b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 448)) *)
  0x3dc06013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 384)) *)
  0x4f408171;       (* arm_MUL_VEC Q17 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4f50d166;       (* arm_SQRDMULH_VEC Q6 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408279;       (* arm_MUL_VEC Q25 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d26c;       (* arm_SQRDMULH_VEC Q12 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40804b;       (* arm_MUL_VEC Q11 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4740d1;       (* arm_MLS_VEC Q17 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d04e;       (* arm_SQRDMULH_VEC Q14 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474199;       (* arm_MLS_VEC Q25 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d31b;       (* arm_SQRDMULH_VEC Q27 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x4e7186c9;       (* arm_ADD_VEC Q9 Q22 Q17 16 128 *)
  0x6f4741cb;       (* arm_MLS_VEC Q11 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e79847a;       (* arm_SUB_VEC Q26 Q3 Q25 16 128 *)
  0x4f70d122;       (* arm_SQRDMULH_VEC Q2 Q9 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608138;       (* arm_MUL_VEC Q24 Q9 (Q0 :> LANE_H 2) 16 128 *)
  0x4f408b53;       (* arm_MUL_VEC Q19 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50db4e;       (* arm_SQRDMULH_VEC Q14 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x6f474377;       (* arm_MLS_VEC Q23 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474058;       (* arm_MLS_VEC Q24 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6b85a6;       (* arm_ADD_VEC Q6 Q13 Q11 16 128 *)
  0x6f4741d3;       (* arm_MLS_VEC Q19 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7784a4;       (* arm_SUB_VEC Q4 Q5 Q23 16 128 *)
  0x4e79846a;       (* arm_ADD_VEC Q10 Q3 Q25 16 128 *)
  0x6e7884c8;       (* arm_SUB_VEC Q8 Q6 Q24 16 128 *)
  0x4e738483;       (* arm_ADD_VEC Q3 Q4 Q19 16 128 *)
  0x6e73849f;       (* arm_SUB_VEC Q31 Q4 Q19 16 128 *)
  0x4f41810e;       (* arm_MUL_VEC Q14 Q8 (Q1 :> LANE_H 0) 16 128 *)
  0x4f70d144;       (* arm_SQRDMULH_VEC Q4 Q10 (Q0 :> LANE_H 3) 16 128 *)
  0x4f60814c;       (* arm_MUL_VEC Q12 Q10 (Q0 :> LANE_H 2) 16 128 *)
  0x4f51d102;       (* arm_SQRDMULH_VEC Q2 Q8 (Q1 :> LANE_H 1) 16 128 *)
  0x6e7186c8;       (* arm_SUB_VEC Q8 Q22 Q17 16 128 *)
  0x4e7784be;       (* arm_ADD_VEC Q30 Q5 Q23 16 128 *)
  0x6f47408c;       (* arm_MLS_VEC Q12 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d904;       (* arm_SQRDMULH_VEC Q4 Q8 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408913;       (* arm_MUL_VEC Q19 Q8 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47404e;       (* arm_MLS_VEC Q14 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6c87db;       (* arm_SUB_VEC Q27 Q30 Q12 16 128 *)
  0x6e6b85b7;       (* arm_SUB_VEC Q23 Q13 Q11 16 128 *)
  0x6f474093;       (* arm_MLS_VEC Q19 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6e8762;       (* arm_SUB_VEC Q2 Q27 Q14 16 128 *)
  0x4e6e8768;       (* arm_ADD_VEC Q8 Q27 Q14 16 128 *)
  0x4e7884ce;       (* arm_ADD_VEC Q14 Q6 Q24 16 128 *)
  0x3d803002;       (* arm_STR Q2 X0 (Immediate_Offset (word 192)) *)
  0x4e7386e2;       (* arm_ADD_VEC Q2 Q23 Q19 16 128 *)
  0x3d802008;       (* arm_STR Q8 X0 (Immediate_Offset (word 128)) *)
  0x6e7386f3;       (* arm_SUB_VEC Q19 Q23 Q19 16 128 *)
  0x4f71d04d;       (* arm_SQRDMULH_VEC Q13 Q2 (Q1 :> LANE_H 3) 16 128 *)
  0x4f618051;       (* arm_MUL_VEC Q17 Q2 (Q1 :> LANE_H 2) 16 128 *)
  0x4e6c87db;       (* arm_ADD_VEC Q27 Q30 Q12 16 128 *)
  0x4f51da78;       (* arm_SQRDMULH_VEC Q24 Q19 (Q1 :> LANE_H 5) 16 128 *)
  0x4f418a73;       (* arm_MUL_VEC Q19 Q19 (Q1 :> LANE_H 4) 16 128 *)
  0x6f4741b1;       (* arm_MLS_VEC Q17 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d9c8;       (* arm_SQRDMULH_VEC Q8 Q14 (Q0 :> LANE_H 7) 16 128 *)
  0x4f6089c2;       (* arm_MUL_VEC Q2 Q14 (Q0 :> LANE_H 6) 16 128 *)
  0x6f474313;       (* arm_MLS_VEC Q19 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4e71847a;       (* arm_ADD_VEC Q26 Q3 Q17 16 128 *)
  0x6e71846e;       (* arm_SUB_VEC Q14 Q3 Q17 16 128 *)
  0x6f474102;       (* arm_MLS_VEC Q2 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80401a;       (* arm_STR Q26 X0 (Immediate_Offset (word 256)) *)
  0x4e7387e8;       (* arm_ADD_VEC Q8 Q31 Q19 16 128 *)
  0x3d80500e;       (* arm_STR Q14 X0 (Immediate_Offset (word 320)) *)
  0x6e7387f8;       (* arm_SUB_VEC Q24 Q31 Q19 16 128 *)
  0x3d806008;       (* arm_STR Q8 X0 (Immediate_Offset (word 384)) *)
  0x4e628772;       (* arm_ADD_VEC Q18 Q27 Q2 16 128 *)
  0x3d807018;       (* arm_STR Q24 X0 (Immediate_Offset (word 448)) *)
  0x6e62876e;       (* arm_SUB_VEC Q14 Q27 Q2 16 128 *)
  0x3c810412;       (* arm_STR Q18 X0 (Postimmediate_Offset (word 16)) *)
  0x3d800c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 48)) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3cc1042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc00c18;       (* arm_LDR Q24 X0 (Immediate_Offset (word 48)) *)
  0x3dc00808;       (* arm_LDR Q8 X0 (Immediate_Offset (word 32)) *)
  0x4f5bd30e;       (* arm_SQRDMULH_VEC Q14 Q24 (Q11 :> LANE_H 1) 16 128 *)
  0x4f4b8302;       (* arm_MUL_VEC Q2 Q24 (Q11 :> LANE_H 0) 16 128 *)
  0x4f5bd109;       (* arm_SQRDMULH_VEC Q9 Q8 (Q11 :> LANE_H 1) 16 128 *)
  0x3dc00418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 16)) *)
  0x6f4741c2;       (* arm_MLS_VEC Q2 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4b810e;       (* arm_MUL_VEC Q14 Q8 (Q11 :> LANE_H 0) 16 128 *)
  0x3dc01046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 64)) *)
  0x6e628708;       (* arm_SUB_VEC Q8 Q24 Q2 16 128 *)
  0x6f47412e;       (* arm_MLS_VEC Q14 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4e628702;       (* arm_ADD_VEC Q2 Q24 Q2 16 128 *)
  0x4f4b891b;       (* arm_MUL_VEC Q27 Q8 (Q11 :> LANE_H 4) 16 128 *)
  0x4f5bd908;       (* arm_SQRDMULH_VEC Q8 Q8 (Q11 :> LANE_H 5) 16 128 *)
  0x4f6b8058;       (* arm_MUL_VEC Q24 Q2 (Q11 :> LANE_H 2) 16 128 *)
  0x4f7bd04b;       (* arm_SQRDMULH_VEC Q11 Q2 (Q11 :> LANE_H 3) 16 128 *)
  0x6f47411b;       (* arm_MLS_VEC Q27 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01445;       (* arm_LDR Q5 X2 (Immediate_Offset (word 80)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x3dc00008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 0)) *)
  0x3dc00451;       (* arm_LDR Q17 X2 (Immediate_Offset (word 16)) *)
  0x6e6e8501;       (* arm_SUB_VEC Q1 Q8 Q14 16 128 *)
  0x6f474178;       (* arm_MLS_VEC Q24 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6e8508;       (* arm_ADD_VEC Q8 Q8 Q14 16 128 *)
  0x6e7b8420;       (* arm_SUB_VEC Q0 Q1 Q27 16 128 *)
  0x4e7b842c;       (* arm_ADD_VEC Q12 Q1 Q27 16 128 *)
  0x6e788513;       (* arm_SUB_VEC Q19 Q8 Q24 16 128 *)
  0x4e788508;       (* arm_ADD_VEC Q8 Q8 Q24 16 128 *)
  0x4e802998;       (* arm_TRN1 Q24 Q12 Q0 32 128 *)
  0x4e80698d;       (* arm_TRN2 Q13 Q12 Q0 32 128 *)
  0x4e932917;       (* arm_TRN1 Q23 Q8 Q19 32 128 *)
  0x3cc60442;       (* arm_LDR Q2 X2 (Postimmediate_Offset (word 96)) *)
  0x4ed86ae9;       (* arm_TRN2 Q9 Q23 Q24 64 128 *)
  0x4e936908;       (* arm_TRN2 Q8 Q8 Q19 32 128 *)
  0x6e71b53a;       (* arm_SQRDMULH_VEC Q26 Q9 Q17 16 128 *)
  0x4ed82af8;       (* arm_TRN1 Q24 Q23 Q24 64 128 *)
  0x4ecd690b;       (* arm_TRN2 Q11 Q8 Q13 64 128 *)
  0x4ecd291d;       (* arm_TRN1 Q29 Q8 Q13 64 128 *)
  0x6e71b577;       (* arm_SQRDMULH_VEC Q23 Q11 Q17 16 128 *)
  0x4e629d6a;       (* arm_MUL_VEC Q10 Q11 Q2 16 128 *)
  0x4e629d20;       (* arm_MUL_VEC Q0 Q9 Q2 16 128 *)
  0x3cdc004b;       (* arm_LDR Q11 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6f4742ea;       (* arm_MLS_VEC Q10 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474340;       (* arm_MLS_VEC Q0 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdd0053;       (* arm_LDR Q19 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e6a87b1;       (* arm_ADD_VEC Q17 Q29 Q10 16 128 *)
  0x6e608717;       (* arm_SUB_VEC Q23 Q24 Q0 16 128 *)
  0x6e6a87be;       (* arm_SUB_VEC Q30 Q29 Q10 16 128 *)
  0x4e6b9e22;       (* arm_MUL_VEC Q2 Q17 Q11 16 128 *)
  0x6e73b62b;       (* arm_SQRDMULH_VEC Q11 Q17 Q19 16 128 *)
  0x4e669fc8;       (* arm_MUL_VEC Q8 Q30 Q6 16 128 *)
  0x3dc01c16;       (* arm_LDR Q22 X0 (Immediate_Offset (word 112)) *)
  0x6f474162;       (* arm_MLS_VEC Q2 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e608718;       (* arm_ADD_VEC Q24 Q24 Q0 16 128 *)
  0x3cc1042f;       (* arm_LDR Q15 X1 (Postimmediate_Offset (word 16)) *)
  0x6e62870e;       (* arm_SUB_VEC Q14 Q24 Q2 16 128 *)
  0x4e628718;       (* arm_ADD_VEC Q24 Q24 Q2 16 128 *)
  0x4f5fd2c1;       (* arm_SQRDMULH_VEC Q1 Q22 (Q15 :> LANE_H 1) 16 128 *)
  0x4f4f82c2;       (* arm_MUL_VEC Q2 Q22 (Q15 :> LANE_H 0) 16 128 *)
  0x4e8e2b00;       (* arm_TRN1 Q0 Q24 Q14 32 128 *)
  0x4e8e6b18;       (* arm_TRN2 Q24 Q24 Q14 32 128 *)
  0x6e65b7d3;       (* arm_SQRDMULH_VEC Q19 Q30 Q5 16 128 *)
  0x6f474022;       (* arm_MLS_VEC Q2 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01810;       (* arm_LDR Q16 X0 (Immediate_Offset (word 96)) *)
  0x6f474268;       (* arm_MLS_VEC Q8 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 64)) *)
  0x4f4f820e;       (* arm_MUL_VEC Q14 Q16 (Q15 :> LANE_H 0) 16 128 *)
  0x6e6886e3;       (* arm_SUB_VEC Q3 Q23 Q8 16 128 *)
  0x4e6886e8;       (* arm_ADD_VEC Q8 Q23 Q8 16 128 *)
  0x3dc01445;       (* arm_LDR Q5 X2 (Immediate_Offset (word 80)) *)
  0x4e836917;       (* arm_TRN2 Q23 Q8 Q3 32 128 *)
  0x4e83291f;       (* arm_TRN1 Q31 Q8 Q3 32 128 *)
  0x4f5fd208;       (* arm_SQRDMULH_VEC Q8 Q16 (Q15 :> LANE_H 1) 16 128 *)
  0x4ed76b19;       (* arm_TRN2 Q25 Q24 Q23 64 128 *)
  0x4ed72b1d;       (* arm_TRN1 Q29 Q24 Q23 64 128 *)
  0x3dc01418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 80)) *)
  0x4edf2810;       (* arm_TRN1 Q16 Q0 Q31 64 128 *)
  0x6f47410e;       (* arm_MLS_VEC Q14 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e62870d;       (* arm_SUB_VEC Q13 Q24 Q2 16 128 *)
  0x4e628718;       (* arm_ADD_VEC Q24 Q24 Q2 16 128 *)
  0x4edf6802;       (* arm_TRN2 Q2 Q0 Q31 64 128 *)
  0x4f5fd9b3;       (* arm_SQRDMULH_VEC Q19 Q13 (Q15 :> LANE_H 5) 16 128 *)
  0x3d800802;       (* arm_STR Q2 X0 (Immediate_Offset (word 32)) *)
  0x4f7fd30b;       (* arm_SQRDMULH_VEC Q11 Q24 (Q15 :> LANE_H 3) 16 128 *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0x4f4f89bb;       (* arm_MUL_VEC Q27 Q13 (Q15 :> LANE_H 4) 16 128 *)
  0x3c9d001d;       (* arm_STR Q29 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4f6f8318;       (* arm_MUL_VEC Q24 Q24 (Q15 :> LANE_H 2) 16 128 *)
  0x3c9f0019;       (* arm_STR Q25 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f47427b;       (* arm_MLS_VEC Q27 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff704;       (* arm_CBNZ X4 (word 2096864) *)
  0x3dc00017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 0)) *)
  0x3cc60451;       (* arm_LDR Q17 X2 (Postimmediate_Offset (word 96)) *)
  0x6e6e86f3;       (* arm_SUB_VEC Q19 Q23 Q14 16 128 *)
  0x6f474178;       (* arm_MLS_VEC Q24 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6e86ee;       (* arm_ADD_VEC Q14 Q23 Q14 16 128 *)
  0x4e7b8668;       (* arm_ADD_VEC Q8 Q19 Q27 16 128 *)
  0x6e7b866d;       (* arm_SUB_VEC Q13 Q19 Q27 16 128 *)
  0x4e7885cc;       (* arm_ADD_VEC Q12 Q14 Q24 16 128 *)
  0x6e7885d8;       (* arm_SUB_VEC Q24 Q14 Q24 16 128 *)
  0x4e8d2900;       (* arm_TRN1 Q0 Q8 Q13 32 128 *)
  0x4e8d6917;       (* arm_TRN2 Q23 Q8 Q13 32 128 *)
  0x4e986993;       (* arm_TRN2 Q19 Q12 Q24 32 128 *)
  0x3cdb005b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4ed76a68;       (* arm_TRN2 Q8 Q19 Q23 64 128 *)
  0x4e982996;       (* arm_TRN1 Q22 Q12 Q24 32 128 *)
  0x4e719d0e;       (* arm_MUL_VEC Q14 Q8 Q17 16 128 *)
  0x6e7bb518;       (* arm_SQRDMULH_VEC Q24 Q8 Q27 16 128 *)
  0x4ec06ac2;       (* arm_TRN2 Q2 Q22 Q0 64 128 *)
  0x4ed72a68;       (* arm_TRN1 Q8 Q19 Q23 64 128 *)
  0x4e719c4b;       (* arm_MUL_VEC Q11 Q2 Q17 16 128 *)
  0x6f47430e;       (* arm_MLS_VEC Q14 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdd005a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6e7bb457;       (* arm_SQRDMULH_VEC Q23 Q2 Q27 16 128 *)
  0x6e6e8518;       (* arm_SUB_VEC Q24 Q8 Q14 16 128 *)
  0x3cdc0042;       (* arm_LDR Q2 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6e65b713;       (* arm_SQRDMULH_VEC Q19 Q24 Q5 16 128 *)
  0x4e6e850e;       (* arm_ADD_VEC Q14 Q8 Q14 16 128 *)
  0x4e669f18;       (* arm_MUL_VEC Q24 Q24 Q6 16 128 *)
  0x6f4742eb;       (* arm_MLS_VEC Q11 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7ab5c8;       (* arm_SQRDMULH_VEC Q8 Q14 Q26 16 128 *)
  0x4e629dc2;       (* arm_MUL_VEC Q2 Q14 Q2 16 128 *)
  0x4ec02ace;       (* arm_TRN1 Q14 Q22 Q0 64 128 *)
  0x6f474278;       (* arm_MLS_VEC Q24 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6b85d7;       (* arm_SUB_VEC Q23 Q14 Q11 16 128 *)
  0x6f474102;       (* arm_MLS_VEC Q2 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6b85ce;       (* arm_ADD_VEC Q14 Q14 Q11 16 128 *)
  0x4e7886e8;       (* arm_ADD_VEC Q8 Q23 Q24 16 128 *)
  0x6e7886f8;       (* arm_SUB_VEC Q24 Q23 Q24 16 128 *)
  0x6e6285d3;       (* arm_SUB_VEC Q19 Q14 Q2 16 128 *)
  0x4e6285cb;       (* arm_ADD_VEC Q11 Q14 Q2 16 128 *)
  0x4e982902;       (* arm_TRN1 Q2 Q8 Q24 32 128 *)
  0x4e98690e;       (* arm_TRN2 Q14 Q8 Q24 32 128 *)
  0x4e936977;       (* arm_TRN2 Q23 Q11 Q19 32 128 *)
  0x4e93296b;       (* arm_TRN1 Q11 Q11 Q19 32 128 *)
  0x4ece6ae8;       (* arm_TRN2 Q8 Q23 Q14 64 128 *)
  0x4ec22978;       (* arm_TRN1 Q24 Q11 Q2 64 128 *)
  0x3d800c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 48)) *)
  0x4ec26968;       (* arm_TRN2 Q8 Q11 Q2 64 128 *)
  0x3c840418;       (* arm_STR Q24 X0 (Postimmediate_Offset (word 64)) *)
  0x4ece2af8;       (* arm_TRN1 Q24 Q23 Q14 64 128 *)
  0x3c9e0008;       (* arm_STR Q8 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9d0018;       (* arm_STR Q24 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_NTT_EXEC = ARM_MK_EXEC_RULE mlkem_ntt_mc;;

let ntt_constants = define
 `ntt_constants z_12345 z_67 s <=>
        (!i. i < 80
             ==> read(memory :> bytes16(word_add z_12345 (word(2 * i)))) s =
                 iword(EL i ntt_zetas_layer12345)) /\
        (!i. i < 384
             ==> read(memory :> bytes16(word_add z_67 (word(2 * i)))) s =
                 iword(EL i ntt_zetas_layer67))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NTT_CORRECT = prove
 (`!a z_12345 z_67 x pc.
      ALL (nonoverlapping (a,512))
          [(word pc,0x504); (z_12345,160); (z_67,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                ntt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x4ec) /\
                ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &23594))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `z_12345:int64`; `z_67:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  REWRITE_TAC[ntt_constants] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  REWRITE_TAC[ntt_zetas_layer12345; ntt_zetas_layer67] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Manually restructure to match the 128-bit loads. It would be nicer
   *** if the simulation machinery did this automatically.
   ***)

  MEMORY_128_FROM_16_TAC "a" 32 THEN
  MEMORY_128_FROM_16_TAC "z_12345" 10 THEN
  MEMORY_128_FROM_16_TAC "z_67" 48 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  REPEAT STRIP_TAC THEN

  (*** Ghost up initial contents of Q7 since it isn't fully initialized ***)

  ABBREV_TAC `v7_init:int128 = read Q7 s0` THEN

  (*** Simulate all the way to the end, in effect unrolling loops ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_NTT_EXEC [n] THEN
             (SIMD_SIMPLIFY_TAC [barmul]))
            (1--904) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Turn the conclusion into an explicit conjunction and split it up ***)

  DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM I_THM] THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s904" THEN
  REPEAT(W(fun (asl,w) ->
     if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  (*** Get congruences and bounds for the result digits and finish ***)

  FIRST_X_ASSUM(MP_TAC o CONV_RULE EXPAND_CASES_CONV) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(fun aboth ->
    W(MP_TAC o GEN_CONGBOUND_RULE (CONJUNCTS aboth) o
      rand o lhand o rator o lhand o snd)) THEN
  (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV FORWARD_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
      MATCH_MP_TAC(INT_ARITH
       `l':int <= l /\ u <= u'
        ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
      CONV_TAC INT_REDUCE_CONV]));;

(*** Subroutine form, somewhat messy elaboration of the usual wrapper ***)

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_NTT_SUBROUTINE_CORRECT = prove
 (`!a z_12345 z_67 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x504); (z_12345,160); (z_67,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                ntt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = returnaddress /\
                ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &23594))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  let TWEAK_CONV =
    REWRITE_CONV[ntt_constants] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[fst MLKEM_NTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_NTT_EXEC
   (REWRITE_RULE[fst MLKEM_NTT_EXEC] (CONV_RULE TWEAK_CONV MLKEM_NTT_CORRECT))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
