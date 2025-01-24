(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem.ml";;

(**** print_literal_from_elf "mlkem/mlkem_intt.o";;
 ****)

let mlkem_intt_mc = define_assert_from_elf
 "mlkem_intt_mc" "mlkem/mlkem_intt.o"
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
  0x52804005;       (* arm_MOV W5 (rvalue (word 512)) *)
  0x4e020cbd;       (* arm_DUP_GEN Q29 X5 16 128 *)
  0x52827605;       (* arm_MOV W5 (rvalue (word 5040)) *)
  0x4e020cbe;       (* arm_DUP_GEN Q30 X5 16 128 *)
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc00068;       (* arm_LDR Q8 X3 (Immediate_Offset (word 0)) *)
  0x3dc00469;       (* arm_LDR Q9 X3 (Immediate_Offset (word 16)) *)
  0x3dc0086a;       (* arm_LDR Q10 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c6b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 48)) *)
  0x6e7eb51b;       (* arm_SQRDMULH_VEC Q27 Q8 Q30 16 128 *)
  0x4e7d9d08;       (* arm_MUL_VEC Q8 Q8 Q29 16 128 *)
  0x6f474368;       (* arm_MLS_VEC Q8 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7eb53b;       (* arm_SQRDMULH_VEC Q27 Q9 Q30 16 128 *)
  0x4e7d9d29;       (* arm_MUL_VEC Q9 Q9 Q29 16 128 *)
  0x6f474369;       (* arm_MLS_VEC Q9 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7eb55b;       (* arm_SQRDMULH_VEC Q27 Q10 Q30 16 128 *)
  0x4e7d9d4a;       (* arm_MUL_VEC Q10 Q10 Q29 16 128 *)
  0x6f47436a;       (* arm_MLS_VEC Q10 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7eb57b;       (* arm_SQRDMULH_VEC Q27 Q11 Q30 16 128 *)
  0x4e7d9d6b;       (* arm_MUL_VEC Q11 Q11 Q29 16 128 *)
  0x6f47436b;       (* arm_MLS_VEC Q11 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3c840468;       (* arm_STR Q8 X3 (Postimmediate_Offset (word 64)) *)
  0x3c9d0069;       (* arm_STR Q9 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e006a;       (* arm_STR Q10 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fffd64;       (* arm_CBNZ X4 (word 2097068) *)
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc0007a;       (* arm_LDR Q26 X3 (Immediate_Offset (word 0)) *)
  0x3dc00468;       (* arm_LDR Q8 X3 (Immediate_Offset (word 16)) *)
  0x3dc00878;       (* arm_LDR Q24 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c70;       (* arm_LDR Q16 X3 (Immediate_Offset (word 48)) *)
  0x3cc60449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 96)) *)
  0x4e902b00;       (* arm_TRN1 Q0 Q24 Q16 32 128 *)
  0x3cdb0046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x3cdc0043;       (* arm_LDR Q3 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x3cdd004f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cde0044;       (* arm_LDR Q4 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdf005c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4e882b4c;       (* arm_TRN1 Q12 Q26 Q8 32 128 *)
  0x4e886b5a;       (* arm_TRN2 Q26 Q26 Q8 32 128 *)
  0x4e906b08;       (* arm_TRN2 Q8 Q24 Q16 32 128 *)
  0x4ec0698b;       (* arm_TRN2 Q11 Q12 Q0 64 128 *)
  0x4ec0298c;       (* arm_TRN1 Q12 Q12 Q0 64 128 *)
  0x4ec86b50;       (* arm_TRN2 Q16 Q26 Q8 64 128 *)
  0x4ec82b5a;       (* arm_TRN1 Q26 Q26 Q8 64 128 *)
  0x6e708568;       (* arm_SUB_VEC Q8 Q11 Q16 16 128 *)
  0x4e70856b;       (* arm_ADD_VEC Q11 Q11 Q16 16 128 *)
  0x6e7a8590;       (* arm_SUB_VEC Q16 Q12 Q26 16 128 *)
  0x4e7a858c;       (* arm_ADD_VEC Q12 Q12 Q26 16 128 *)
  0x6e7cb51a;       (* arm_SQRDMULH_VEC Q26 Q8 Q28 16 128 *)
  0x6e6fb60f;       (* arm_SQRDMULH_VEC Q15 Q16 Q15 16 128 *)
  0x4e639e10;       (* arm_MUL_VEC Q16 Q16 Q3 16 128 *)
  0x4e649d08;       (* arm_MUL_VEC Q8 Q8 Q4 16 128 *)
  0x6e6b8580;       (* arm_SUB_VEC Q0 Q12 Q11 16 128 *)
  0x4e6b858c;       (* arm_ADD_VEC Q12 Q12 Q11 16 128 *)
  0x6f4741f0;       (* arm_MLS_VEC Q16 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474348;       (* arm_MLS_VEC Q8 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e66b41a;       (* arm_SQRDMULH_VEC Q26 Q0 Q6 16 128 *)
  0x4e699c0b;       (* arm_MUL_VEC Q11 Q0 Q9 16 128 *)
  0x3cc1042f;       (* arm_LDR Q15 X1 (Postimmediate_Offset (word 16)) *)
  0x6e688600;       (* arm_SUB_VEC Q0 Q16 Q8 16 128 *)
  0x6f47434b;       (* arm_MLS_VEC Q11 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4e68861a;       (* arm_ADD_VEC Q26 Q16 Q8 16 128 *)
  0x6e66b408;       (* arm_SQRDMULH_VEC Q8 Q0 Q6 16 128 *)
  0x4e699c10;       (* arm_MUL_VEC Q16 Q0 Q9 16 128 *)
  0x4e9a2980;       (* arm_TRN1 Q0 Q12 Q26 32 128 *)
  0x4e9a698c;       (* arm_TRN2 Q12 Q12 Q26 32 128 *)
  0x3dc0107a;       (* arm_LDR Q26 X3 (Immediate_Offset (word 64)) *)
  0x6f474110;       (* arm_MLS_VEC Q16 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01468;       (* arm_LDR Q8 X3 (Immediate_Offset (word 80)) *)
  0x3dc01878;       (* arm_LDR Q24 X3 (Immediate_Offset (word 96)) *)
  0x4e902969;       (* arm_TRN1 Q9 Q11 Q16 32 128 *)
  0x4e90696b;       (* arm_TRN2 Q11 Q11 Q16 32 128 *)
  0x3dc01c70;       (* arm_LDR Q16 X3 (Immediate_Offset (word 112)) *)
  0x4ec96806;       (* arm_TRN2 Q6 Q0 Q9 64 128 *)
  0x4ecb6983;       (* arm_TRN2 Q3 Q12 Q11 64 128 *)
  0x4ec92800;       (* arm_TRN1 Q0 Q0 Q9 64 128 *)
  0x4ecb298c;       (* arm_TRN1 Q12 Q12 Q11 64 128 *)
  0x6e6384cb;       (* arm_SUB_VEC Q11 Q6 Q3 16 128 *)
  0x6e6c8409;       (* arm_SUB_VEC Q9 Q0 Q12 16 128 *)
  0x4e6c840c;       (* arm_ADD_VEC Q12 Q0 Q12 16 128 *)
  0x4f5fd960;       (* arm_SQRDMULH_VEC Q0 Q11 (Q15 :> LANE_H 5) 16 128 *)
  0x4f7fd124;       (* arm_SQRDMULH_VEC Q4 Q9 (Q15 :> LANE_H 3) 16 128 *)
  0x4f6f8129;       (* arm_MUL_VEC Q9 Q9 (Q15 :> LANE_H 2) 16 128 *)
  0x4f4f896b;       (* arm_MUL_VEC Q11 Q11 (Q15 :> LANE_H 4) 16 128 *)
  0x4e6384c6;       (* arm_ADD_VEC Q6 Q6 Q3 16 128 *)
  0x4f57c183;       (* arm_SQDMULH_VEC Q3 Q12 (Q7 :> LANE_H 1) 16 128 *)
  0x6f474089;       (* arm_MLS_VEC Q9 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47400b;       (* arm_MLS_VEC Q11 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c0c0;       (* arm_SQDMULH_VEC Q0 Q6 (Q7 :> LANE_H 1) 16 128 *)
  0x4f152463;       (* arm_SRSHR_VEC Q3 Q3 11 16 128 *)
  0x4f57c124;       (* arm_SQDMULH_VEC Q4 Q9 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c17c;       (* arm_SQDMULH_VEC Q28 Q11 (Q7 :> LANE_H 1) 16 128 *)
  0x6f47406c;       (* arm_MLS_VEC Q12 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152400;       (* arm_SRSHR_VEC Q0 Q0 11 16 128 *)
  0x4f152483;       (* arm_SRSHR_VEC Q3 Q4 11 16 128 *)
  0x4f152784;       (* arm_SRSHR_VEC Q4 Q28 11 16 128 *)
  0x6f474006;       (* arm_MLS_VEC Q6 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474069;       (* arm_MLS_VEC Q9 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47408b;       (* arm_MLS_VEC Q11 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4e902b00;       (* arm_TRN1 Q0 Q24 Q16 32 128 *)
  0x6e668583;       (* arm_SUB_VEC Q3 Q12 Q6 16 128 *)
  0x4e66858c;       (* arm_ADD_VEC Q12 Q12 Q6 16 128 *)
  0x6e6b8526;       (* arm_SUB_VEC Q6 Q9 Q11 16 128 *)
  0x4f5fd064;       (* arm_SQRDMULH_VEC Q4 Q3 (Q15 :> LANE_H 1) 16 128 *)
  0x4f4f8063;       (* arm_MUL_VEC Q3 Q3 (Q15 :> LANE_H 0) 16 128 *)
  0x4f5fd0dc;       (* arm_SQRDMULH_VEC Q28 Q6 (Q15 :> LANE_H 1) 16 128 *)
  0x4f4f80cf;       (* arm_MUL_VEC Q15 Q6 (Q15 :> LANE_H 0) 16 128 *)
  0x4e6b852b;       (* arm_ADD_VEC Q11 Q9 Q11 16 128 *)
  0x6f474083;       (* arm_MLS_VEC Q3 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x3c84046c;       (* arm_STR Q12 X3 (Postimmediate_Offset (word 64)) *)
  0x6f47438f;       (* arm_MLS_VEC Q15 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9d006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cc60449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 96)) *)
  0x3c9e0063;       (* arm_STR Q3 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdb0046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x3c9f006f;       (* arm_STR Q15 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cdc0043;       (* arm_LDR Q3 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x3cdd004f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cde0044;       (* arm_LDR Q4 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdf005c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff584;       (* arm_CBNZ X4 (word 2096816) *)
  0x4e882b4b;       (* arm_TRN1 Q11 Q26 Q8 32 128 *)
  0x4e906b18;       (* arm_TRN2 Q24 Q24 Q16 32 128 *)
  0x4e886b5a;       (* arm_TRN2 Q26 Q26 Q8 32 128 *)
  0x4ec02972;       (* arm_TRN1 Q18 Q11 Q0 64 128 *)
  0x4ec0696b;       (* arm_TRN2 Q11 Q11 Q0 64 128 *)
  0x4ed86b4c;       (* arm_TRN2 Q12 Q26 Q24 64 128 *)
  0x4ed82b48;       (* arm_TRN1 Q8 Q26 Q24 64 128 *)
  0x6e6c857a;       (* arm_SUB_VEC Q26 Q11 Q12 16 128 *)
  0x6e68864d;       (* arm_SUB_VEC Q13 Q18 Q8 16 128 *)
  0x4e688658;       (* arm_ADD_VEC Q24 Q18 Q8 16 128 *)
  0x4e649f50;       (* arm_MUL_VEC Q16 Q26 Q4 16 128 *)
  0x6e6fb5b1;       (* arm_SQRDMULH_VEC Q17 Q13 Q15 16 128 *)
  0x4e639da3;       (* arm_MUL_VEC Q3 Q13 Q3 16 128 *)
  0x6e7cb75a;       (* arm_SQRDMULH_VEC Q26 Q26 Q28 16 128 *)
  0x4e6c856a;       (* arm_ADD_VEC Q10 Q11 Q12 16 128 *)
  0x6f474223;       (* arm_MLS_VEC Q3 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474350;       (* arm_MLS_VEC Q16 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6a871a;       (* arm_SUB_VEC Q26 Q24 Q10 16 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x6e70846c;       (* arm_SUB_VEC Q12 Q3 Q16 16 128 *)
  0x6e66b74f;       (* arm_SQRDMULH_VEC Q15 Q26 Q6 16 128 *)
  0x4e699f4b;       (* arm_MUL_VEC Q11 Q26 Q9 16 128 *)
  0x4e699d88;       (* arm_MUL_VEC Q8 Q12 Q9 16 128 *)
  0x6e66b58c;       (* arm_SQRDMULH_VEC Q12 Q12 Q6 16 128 *)
  0x4e6a8700;       (* arm_ADD_VEC Q0 Q24 Q10 16 128 *)
  0x6f4741eb;       (* arm_MLS_VEC Q11 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e708466;       (* arm_ADD_VEC Q6 Q3 Q16 16 128 *)
  0x6f474188;       (* arm_MLS_VEC Q8 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e86681a;       (* arm_TRN2 Q26 Q0 Q6 32 128 *)
  0x4e88696c;       (* arm_TRN2 Q12 Q11 Q8 32 128 *)
  0x4e882963;       (* arm_TRN1 Q3 Q11 Q8 32 128 *)
  0x4e862811;       (* arm_TRN1 Q17 Q0 Q6 32 128 *)
  0x4ecc2b48;       (* arm_TRN1 Q8 Q26 Q12 64 128 *)
  0x4ecc6b4d;       (* arm_TRN2 Q13 Q26 Q12 64 128 *)
  0x4ec32a2b;       (* arm_TRN1 Q11 Q17 Q3 64 128 *)
  0x4ec36a2f;       (* arm_TRN2 Q15 Q17 Q3 64 128 *)
  0x6e68856c;       (* arm_SUB_VEC Q12 Q11 Q8 16 128 *)
  0x4e6d85f0;       (* arm_ADD_VEC Q16 Q15 Q13 16 128 *)
  0x6e6d85fa;       (* arm_SUB_VEC Q26 Q15 Q13 16 128 *)
  0x4f648180;       (* arm_MUL_VEC Q0 Q12 (Q4 :> LANE_H 2) 16 128 *)
  0x4f74d189;       (* arm_SQRDMULH_VEC Q9 Q12 (Q4 :> LANE_H 3) 16 128 *)
  0x4f448b4d;       (* arm_MUL_VEC Q13 Q26 (Q4 :> LANE_H 4) 16 128 *)
  0x4f54db5a;       (* arm_SQRDMULH_VEC Q26 Q26 (Q4 :> LANE_H 5) 16 128 *)
  0x4e688578;       (* arm_ADD_VEC Q24 Q11 Q8 16 128 *)
  0x6f474120;       (* arm_MLS_VEC Q0 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c20c;       (* arm_SQDMULH_VEC Q12 Q16 (Q7 :> LANE_H 1) 16 128 *)
  0x6f47434d;       (* arm_MLS_VEC Q13 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c30b;       (* arm_SQDMULH_VEC Q11 Q24 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c008;       (* arm_SQDMULH_VEC Q8 Q0 (Q7 :> LANE_H 1) 16 128 *)
  0x4f15258c;       (* arm_SRSHR_VEC Q12 Q12 11 16 128 *)
  0x4f57c1ba;       (* arm_SQDMULH_VEC Q26 Q13 (Q7 :> LANE_H 1) 16 128 *)
  0x4f15256b;       (* arm_SRSHR_VEC Q11 Q11 11 16 128 *)
  0x6f474190;       (* arm_MLS_VEC Q16 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152508;       (* arm_SRSHR_VEC Q8 Q8 11 16 128 *)
  0x4f15275a;       (* arm_SRSHR_VEC Q26 Q26 11 16 128 *)
  0x6f474178;       (* arm_MLS_VEC Q24 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474100;       (* arm_MLS_VEC Q0 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47434d;       (* arm_MLS_VEC Q13 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e70871a;       (* arm_SUB_VEC Q26 Q24 Q16 16 128 *)
  0x4e70870f;       (* arm_ADD_VEC Q15 Q24 Q16 16 128 *)
  0x6e6d840c;       (* arm_SUB_VEC Q12 Q0 Q13 16 128 *)
  0x4f44834b;       (* arm_MUL_VEC Q11 Q26 (Q4 :> LANE_H 0) 16 128 *)
  0x4f54d350;       (* arm_SQRDMULH_VEC Q16 Q26 (Q4 :> LANE_H 1) 16 128 *)
  0x4f44819a;       (* arm_MUL_VEC Q26 Q12 (Q4 :> LANE_H 0) 16 128 *)
  0x4f54d188;       (* arm_SQRDMULH_VEC Q8 Q12 (Q4 :> LANE_H 1) 16 128 *)
  0x4e6d840c;       (* arm_ADD_VEC Q12 Q0 Q13 16 128 *)
  0x6f47420b;       (* arm_MLS_VEC Q11 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x3c84046f;       (* arm_STR Q15 X3 (Postimmediate_Offset (word 64)) *)
  0x6f47411a;       (* arm_MLS_VEC Q26 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9d006c;       (* arm_STR Q12 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f007a;       (* arm_STR Q26 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc02018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 128)) *)
  0x3dc03010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 192)) *)
  0x3dc04009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 256)) *)
  0x3dc05006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 320)) *)
  0x3dc06003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 384)) *)
  0x3dc07004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 448)) *)
  0x4e66853c;       (* arm_ADD_VEC Q28 Q9 Q6 16 128 *)
  0x4e708713;       (* arm_ADD_VEC Q19 Q24 Q16 16 128 *)
  0x4e64846d;       (* arm_ADD_VEC Q13 Q3 Q4 16 128 *)
  0x3dc0000b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 0)) *)
  0x4e6d8797;       (* arm_ADD_VEC Q23 Q28 Q13 16 128 *)
  0x3dc0100f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 64)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x6e6f856c;       (* arm_SUB_VEC Q12 Q11 Q15 16 128 *)
  0x4e6f857a;       (* arm_ADD_VEC Q26 Q11 Q15 16 128 *)
  0x6e708708;       (* arm_SUB_VEC Q8 Q24 Q16 16 128 *)
  0x4f70d98b;       (* arm_SQRDMULH_VEC Q11 Q12 (Q0 :> LANE_H 7) 16 128 *)
  0x4f60898c;       (* arm_MUL_VEC Q12 Q12 (Q0 :> LANE_H 6) 16 128 *)
  0x6e738750;       (* arm_SUB_VEC Q16 Q26 Q19 16 128 *)
  0x4e73875a;       (* arm_ADD_VEC Q26 Q26 Q19 16 128 *)
  0x4f51d10f;       (* arm_SQRDMULH_VEC Q15 Q8 (Q1 :> LANE_H 1) 16 128 *)
  0x4f418108;       (* arm_MUL_VEC Q8 Q8 (Q1 :> LANE_H 0) 16 128 *)
  0x6f47416c;       (* arm_MLS_VEC Q12 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x6e66852b;       (* arm_SUB_VEC Q11 Q9 Q6 16 128 *)
  0x4f70d218;       (* arm_SQRDMULH_VEC Q24 Q16 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608210;       (* arm_MUL_VEC Q16 Q16 (Q0 :> LANE_H 2) 16 128 *)
  0x6e778749;       (* arm_SUB_VEC Q9 Q26 Q23 16 128 *)
  0x4e77875a;       (* arm_ADD_VEC Q26 Q26 Q23 16 128 *)
  0x6f4741e8;       (* arm_MLS_VEC Q8 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d16f;       (* arm_SQRDMULH_VEC Q15 Q11 (Q1 :> LANE_H 3) 16 128 *)
  0x4f61816b;       (* arm_MUL_VEC Q11 Q11 (Q1 :> LANE_H 2) 16 128 *)
  0x6e648466;       (* arm_SUB_VEC Q6 Q3 Q4 16 128 *)
  0x6e688583;       (* arm_SUB_VEC Q3 Q12 Q8 16 128 *)
  0x4e68858c;       (* arm_ADD_VEC Q12 Q12 Q8 16 128 *)
  0x6f4741eb;       (* arm_MLS_VEC Q11 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d8c8;       (* arm_SQRDMULH_VEC Q8 Q6 (Q1 :> LANE_H 5) 16 128 *)
  0x6f474310;       (* arm_MLS_VEC Q16 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4188cf;       (* arm_MUL_VEC Q15 Q6 (Q1 :> LANE_H 4) 16 128 *)
  0x4f70d078;       (* arm_SQRDMULH_VEC Q24 Q3 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608066;       (* arm_MUL_VEC Q6 Q3 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50d123;       (* arm_SQRDMULH_VEC Q3 Q9 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408129;       (* arm_MUL_VEC Q9 Q9 (Q0 :> LANE_H 0) 16 128 *)
  0x3c81041a;       (* arm_STR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6f47410f;       (* arm_MLS_VEC Q15 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474306;       (* arm_MLS_VEC Q6 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d879a;       (* arm_SUB_VEC Q26 Q28 Q13 16 128 *)
  0x6f474069;       (* arm_MLS_VEC Q9 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6f8568;       (* arm_SUB_VEC Q8 Q11 Q15 16 128 *)
  0x4f50db58;       (* arm_SQRDMULH_VEC Q24 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408b5a;       (* arm_MUL_VEC Q26 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x4e6f856b;       (* arm_ADD_VEC Q11 Q11 Q15 16 128 *)
  0x4f50d90f;       (* arm_SQRDMULH_VEC Q15 Q8 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408908;       (* arm_MUL_VEC Q8 Q8 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47431a;       (* arm_MLS_VEC Q26 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6b8598;       (* arm_SUB_VEC Q24 Q12 Q11 16 128 *)
  0x4e6b858c;       (* arm_ADD_VEC Q12 Q12 Q11 16 128 *)
  0x6f4741e8;       (* arm_MLS_VEC Q8 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d30b;       (* arm_SQRDMULH_VEC Q11 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40830f;       (* arm_MUL_VEC Q15 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7a8618;       (* arm_SUB_VEC Q24 Q16 Q26 16 128 *)
  0x4e7a861a;       (* arm_ADD_VEC Q26 Q16 Q26 16 128 *)
  0x6e6884d0;       (* arm_SUB_VEC Q16 Q6 Q8 16 128 *)
  0x6f47416f;       (* arm_MLS_VEC Q15 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d30b;       (* arm_SQRDMULH_VEC Q11 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408318;       (* arm_MUL_VEC Q24 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6884c8;       (* arm_ADD_VEC Q8 Q6 Q8 16 128 *)
  0x4f50d206;       (* arm_SQRDMULH_VEC Q6 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408210;       (* arm_MUL_VEC Q16 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474178;       (* arm_MLS_VEC Q24 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x3d803c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 240)) *)
  0x3dc0000b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 0)) *)
  0x6f4740d0;       (* arm_MLS_VEC Q16 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c0f;       (* arm_STR Q15 X0 (Immediate_Offset (word 304)) *)
  0x3dc0100f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 64)) *)
  0x3d805c18;       (* arm_STR Q24 X0 (Immediate_Offset (word 368)) *)
  0x3dc02018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 128)) *)
  0x3d806c10;       (* arm_STR Q16 X0 (Immediate_Offset (word 432)) *)
  0x3dc03010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 192)) *)
  0x3d800c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 48)) *)
  0x3dc04009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 256)) *)
  0x3dc05006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 320)) *)
  0x3dc06003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 384)) *)
  0x3dc07004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 448)) *)
  0x3d801c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 112)) *)
  0x4e66853c;       (* arm_ADD_VEC Q28 Q9 Q6 16 128 *)
  0x4e64846d;       (* arm_ADD_VEC Q13 Q3 Q4 16 128 *)
  0x3d802c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 176)) *)
  0x4e708713;       (* arm_ADD_VEC Q19 Q24 Q16 16 128 *)
  0x4e6d8797;       (* arm_ADD_VEC Q23 Q28 Q13 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4e6f856a;       (* arm_ADD_VEC Q10 Q11 Q15 16 128 *)
  0x6e6d878c;       (* arm_SUB_VEC Q12 Q28 Q13 16 128 *)
  0x6e6f856b;       (* arm_SUB_VEC Q11 Q11 Q15 16 128 *)
  0x6e738556;       (* arm_SUB_VEC Q22 Q10 Q19 16 128 *)
  0x4f408992;       (* arm_MUL_VEC Q18 Q12 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50d99a;       (* arm_SQRDMULH_VEC Q26 Q12 (Q0 :> LANE_H 5) 16 128 *)
  0x4f70d2cc;       (* arm_SQRDMULH_VEC Q12 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6082cd;       (* arm_MUL_VEC Q13 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x6e70871f;       (* arm_SUB_VEC Q31 Q24 Q16 16 128 *)
  0x4f70d976;       (* arm_SQRDMULH_VEC Q22 Q11 (Q0 :> LANE_H 7) 16 128 *)
  0x6f474352;       (* arm_MLS_VEC Q18 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47418d;       (* arm_MLS_VEC Q13 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d3e2;       (* arm_SQRDMULH_VEC Q2 Q31 (Q1 :> LANE_H 1) 16 128 *)
  0x4f4183e5;       (* arm_MUL_VEC Q5 Q31 (Q1 :> LANE_H 0) 16 128 *)
  0x4f60896f;       (* arm_MUL_VEC Q15 Q11 (Q0 :> LANE_H 6) 16 128 *)
  0x6e7285ac;       (* arm_SUB_VEC Q12 Q13 Q18 16 128 *)
  0x6e648464;       (* arm_SUB_VEC Q4 Q3 Q4 16 128 *)
  0x6f474045;       (* arm_MLS_VEC Q5 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d19a;       (* arm_SQRDMULH_VEC Q26 Q12 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40818c;       (* arm_MUL_VEC Q12 Q12 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4742cf;       (* arm_MLS_VEC Q15 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d888;       (* arm_SQRDMULH_VEC Q8 Q4 (Q1 :> LANE_H 5) 16 128 *)
  0x4f418884;       (* arm_MUL_VEC Q4 Q4 (Q1 :> LANE_H 4) 16 128 *)
  0x6f47434c;       (* arm_MLS_VEC Q12 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6585f5;       (* arm_SUB_VEC Q21 Q15 Q5 16 128 *)
  0x6e66853c;       (* arm_SUB_VEC Q28 Q9 Q6 16 128 *)
  0x6f474104;       (* arm_MLS_VEC Q4 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6082b8;       (* arm_MUL_VEC Q24 Q21 (Q0 :> LANE_H 2) 16 128 *)
  0x4f70d2a8;       (* arm_SQRDMULH_VEC Q8 Q21 (Q0 :> LANE_H 3) 16 128 *)
  0x4f71d386;       (* arm_SQRDMULH_VEC Q6 Q28 (Q1 :> LANE_H 3) 16 128 *)
  0x4e738553;       (* arm_ADD_VEC Q19 Q10 Q19 16 128 *)
  0x4f61839c;       (* arm_MUL_VEC Q28 Q28 (Q1 :> LANE_H 2) 16 128 *)
  0x6f474118;       (* arm_MLS_VEC Q24 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e77866b;       (* arm_SUB_VEC Q11 Q19 Q23 16 128 *)
  0x3d80600c;       (* arm_STR Q12 X0 (Immediate_Offset (word 384)) *)
  0x6f4740dc;       (* arm_MLS_VEC Q28 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d170;       (* arm_SQRDMULH_VEC Q16 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408169;       (* arm_MUL_VEC Q9 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6585e6;       (* arm_ADD_VEC Q6 Q15 Q5 16 128 *)
  0x4e64879a;       (* arm_ADD_VEC Q26 Q28 Q4 16 128 *)
  0x6e64878f;       (* arm_SUB_VEC Q15 Q28 Q4 16 128 *)
  0x6f474209;       (* arm_MLS_VEC Q9 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7a84c3;       (* arm_ADD_VEC Q3 Q6 Q26 16 128 *)
  0x4f4089e8;       (* arm_MUL_VEC Q8 Q15 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50d9ef;       (* arm_SQRDMULH_VEC Q15 Q15 (Q0 :> LANE_H 5) 16 128 *)
  0x3d804009;       (* arm_STR Q9 X0 (Immediate_Offset (word 256)) *)
  0x6e7a84c2;       (* arm_SUB_VEC Q2 Q6 Q26 16 128 *)
  0x3d801003;       (* arm_STR Q3 X0 (Immediate_Offset (word 64)) *)
  0x6f4741e8;       (* arm_MLS_VEC Q8 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d04f;       (* arm_SQRDMULH_VEC Q15 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40804b;       (* arm_MUL_VEC Q11 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7285b0;       (* arm_ADD_VEC Q16 Q13 Q18 16 128 *)
  0x6e68870c;       (* arm_SUB_VEC Q12 Q24 Q8 16 128 *)
  0x4e688708;       (* arm_ADD_VEC Q8 Q24 Q8 16 128 *)
  0x6f4741eb;       (* arm_MLS_VEC Q11 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d19a;       (* arm_SQRDMULH_VEC Q26 Q12 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40818c;       (* arm_MUL_VEC Q12 Q12 (Q0 :> LANE_H 0) 16 128 *)
  0x3d803008;       (* arm_STR Q8 X0 (Immediate_Offset (word 192)) *)
  0x4e77866f;       (* arm_ADD_VEC Q15 Q19 Q23 16 128 *)
  0x3d80500b;       (* arm_STR Q11 X0 (Immediate_Offset (word 320)) *)
  0x6f47434c;       (* arm_MLS_VEC Q12 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x3c81040f;       (* arm_STR Q15 X0 (Postimmediate_Offset (word 16)) *)
  0x3d801c10;       (* arm_STR Q16 X0 (Immediate_Offset (word 112)) *)
  0x3d806c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 432)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_INTT_EXEC = ARM_MK_EXEC_RULE mlkem_intt_mc;;

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

let intt_zetas_layer01234 = define
 `intt_zetas_layer01234:int list =
   [&1583; &15582; -- &821; -- &8081; &1355; &13338; &0; &0; -- &569; -- &5601;
    &450; &4429; &936; &9213; &0; &0; &69; &679; &447; &4400; -- &535;
    -- &5266; &0; &0; &543; &5345; &1235; &12156; -- &1426; -- &14036; &0;
    &0; -- &797; -- &7845; -- &1333; -- &13121; &1089; &10719; &0; &0;
    -- &193; -- &1900; -- &56; -- &551; &283; &2786; &0; &0; &1410; &13879;
    -- &1476; -- &14529; -- &1339; -- &13180; &0; &0; -- &1062; -- &10453;
    &882; &8682; -- &296; -- &2914; &0; &0; &1600; &15749; &40; &394;
    &749; &7373; -- &848; -- &8347; &1432; &14095; -- &630; -- &6201;
    &687; &6762; &0; &0]`;;

let intt_zetas_layer56 = define
 `intt_zetas_layer56:int list =
   [-- &910; -- &910; -- &1227; -- &1227; &219; &219; &855; &855; -- &8957;
    -- &8957; -- &12078; -- &12078; &2156; &2156; &8416; &8416; &1175;
    &1175; &394; &394; -- &1029; -- &1029; -- &1212; -- &1212; &11566;
    &11566; &3878; &3878; -- &10129; -- &10129; -- &11930; -- &11930;
    -- &885; -- &885; &1219; &1219; &1455; &1455; &1607; &1607; -- &8711;
    -- &8711; &11999; &11999; &14322; &14322; &15818; &15818; -- &648;
    -- &648; -- &1481; -- &1481; &712; &712; &682; &682; -- &6378; -- &6378;
    -- &14578; -- &14578; &7008; &7008; &6713; &6713; -- &886; -- &886;
    &1179; &1179; -- &1026; -- &1026; -- &1092; -- &1092; -- &8721;
    -- &8721; &11605; &11605; -- &10099; -- &10099; -- &10749; -- &10749;
    &554; &554; -- &1143; -- &1143; -- &403; -- &403; &525; &525; &5453;
    &5453; -- &11251; -- &11251; -- &3967; -- &3967; &5168; &5168; &927;
    &927; -- &1534; -- &1534; &461; &461; -- &1438; -- &1438; &9125;
    &9125; -- &15099; -- &15099; &4538; &4538; -- &14155; -- &14155; &735;
    &735; -- &561; -- &561; -- &757; -- &757; -- &319; -- &319; &7235;
    &7235; -- &5522; -- &5522; -- &7451; -- &7451; -- &3140; -- &3140;
    &863; &863; &1230; &1230; &556; &556; -- &1063; -- &1063; &8495;
    &8495; &12107; &12107; &5473; &5473; -- &10463; -- &10463; -- &452;
    -- &452; -- &807; -- &807; -- &1435; -- &1435; &1010; &1010; -- &4449;
    -- &4449; -- &7943; -- &7943; -- &14125; -- &14125; &9942; &9942;
    -- &1645; -- &1645; &780; &780; &109; &109; &1031; &1031; -- &16192;
    -- &16192; &7678; &7678; &1073; &1073; &10148; &10148; &1239; &1239;
    -- &375; -- &375; &1292; &1292; -- &1584; -- &1584; &12196; &12196;
    -- &3691; -- &3691; &12717; &12717; -- &15592; -- &15592; &1414; &1414;
    -- &1320; -- &1320; -- &33; -- &33; &464; &464; &13918; &13918;
    -- &12993; -- &12993; -- &325; -- &325; &4567; &4567; -- &641; -- &641;
    &992; &992; &941; &941; &1021; &1021; -- &6309; -- &6309; &9764;
    &9764; &9262; &9262; &10050; &10050; -- &268; -- &268; -- &733;
    -- &733; &892; &892; -- &939; -- &939; -- &2638; -- &2638; -- &7215;
    -- &7215; &8780; &8780; -- &9243; -- &9243; -- &632; -- &632; &816; &816;
    &1352; &1352; -- &650; -- &650; -- &6221; -- &6221; &8032; &8032;
    &13308; &13308; -- &6398; -- &6398; &642; &642; -- &952; -- &952;
    &1540; &1540; -- &1651; -- &1651; &6319; &6319; -- &9371; -- &9371;
    &15159; &15159; -- &16251; -- &16251; -- &1461; -- &1461; &1482;
    &1482; &540; &540; &1626; &1626; -- &14381; -- &14381; &14588; &14588;
    &5315; &5315; &16005; &16005; &1274; &1274; &1052; &1052; &1025;
    &1025; -- &1197; -- &1197; &12540; &12540; &10355; &10355; &10089;
    &10089; -- &11782; -- &11782; &279; &279; &1173; &1173; -- &233;
    -- &233; &667; &667; &2746; &2746; &11546; &11546; -- &2293; -- &2293;
    &6565; &6565; &314; &314; -- &756; -- &756; &48; &48; -- &1409;
    -- &1409; &3091; &3091; -- &7441; -- &7441; &472; &472; -- &13869;
    -- &13869; &1573; &1573; &76; &76; -- &331; -- &331; -- &289; -- &289;
    &15483; &15483; &748; &748; -- &3258; -- &3258; -- &2845; -- &2845;
    -- &1100; -- &1100; -- &723; -- &723; &680; &680; &568; &568; -- &10828;
    -- &10828; -- &7117; -- &7117; &6693; &6693; &5591; &5591; &1041;
    &1041; -- &1637; -- &1637; -- &583; -- &583; -- &17; -- &17; &10247;
    &10247; -- &16113; -- &16113; -- &5739; -- &5739; -- &167; -- &167]`;;

let intt_constants = define
 `intt_constants z_01234 z_56 s <=>
        (!i. i < 80
             ==> read(memory :> bytes16(word_add z_01234 (word(2 * i)))) s =
                 iword(EL i intt_zetas_layer01234)) /\
        (!i. i < 384
             ==> read(memory :> bytes16(word_add z_56 (word(2 * i)))) s =
                 iword(EL i intt_zetas_layer56))`;;

(* ------------------------------------------------------------------------- *)
(* Some convenient proof tools.                                              *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let SIMD_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV[GSYM barred; GSYM barmul];;

let SIMD_SIMPLIFY_TAC =
  let simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV SIMD_SIMPLIFY_CONV) o
    check (simdable o concl)));;

let MEMORY_128_FROM_16_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(16*i) in
      READ_MEMORY_MERGE_CONV 3 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_INTT_CORRECT = prove
 (`!a z_01234 z_56 x pc.
      ALL (nonoverlapping (a,512))
          [(word pc,0x5d0); (z_01234,160); (z_56,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                intt_constants z_01234 z_56 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x5b8) /\
                !i. i < 256
                    ==> let zi =
                         read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &26624)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `z_01234:int64`; `z_56:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  REWRITE_TAC[intt_constants] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  REWRITE_TAC[intt_zetas_layer01234; intt_zetas_layer56] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Manually restructure to match the 128-bit loads. It would be nicer
   *** if the simulation machinery did this automatically.
   ***)

  MEMORY_128_FROM_16_TAC "a" 32 THEN
  MEMORY_128_FROM_16_TAC "z_01234" 10 THEN
  MEMORY_128_FROM_16_TAC "z_56" 48 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  REPEAT STRIP_TAC THEN

  (*** Ghost up initial contents of Q7 since it isn't fully initialized ***)

  ABBREV_TAC `v7_init:int128 = read Q7 s0` THEN

  (*** Simulate all the way to the end, in effect unrolling loops ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_INTT_EXEC [n] THEN SIMD_SIMPLIFY_TAC)
            (1--1181) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE SIMD_SIMPLIFY_CONV o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Turn the conclusion into an explicit conjunction and split it up ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM I_THM] THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1181" THEN
  REPEAT(W(fun (asl,w) ->
     if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  (*** Get congruences and bounds for the result digits and finish ***)

  (W(MP_TAC o CONGBOUND_RULE o rand o lhand o rator o lhand o snd) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV INVERSE_NTT_CONV) THEN
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

let MLKEM_INTT_SUBROUTINE_CORRECT = prove
 (`!a z_01234 z_56 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x5d0); (z_01234,160); (z_56,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                intt_constants z_01234 z_56 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = returnaddress /\
                !i. i < 256
                    ==> let zi =
                         read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &26624)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  let TWEAK_CONV =
    REWRITE_CONV[intt_constants] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[fst MLKEM_INTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_INTT_EXEC
   (REWRITE_RULE[fst MLKEM_INTT_EXEC] (CONV_RULE TWEAK_CONV MLKEM_INTT_CORRECT))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
