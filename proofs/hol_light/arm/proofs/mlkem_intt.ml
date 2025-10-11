(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;
needs "proofs/mlkem_zetas.ml";;

(**** print_literal_from_elf "mlkem/mlkem_intt.o";;
 ****)

let mlkem_intt_mc = define_assert_from_elf
 "mlkem_intt_mc" "mlkem/mlkem_intt.o"
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
  0x3dc0006c;       (* arm_LDR Q12 X3 (Immediate_Offset (word 0)) *)
  0x3dc00475;       (* arm_LDR Q21 X3 (Immediate_Offset (word 16)) *)
  0x3dc00c7e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 48)) *)
  0x3dc0086d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 32)) *)
  0x3dc01063;       (* arm_LDR Q3 X3 (Immediate_Offset (word 64)) *)
  0x3dc0146a;       (* arm_LDR Q10 X3 (Immediate_Offset (word 80)) *)
  0x4e956986;       (* arm_TRN2 Q6 Q12 Q21 32 128 *)
  0x4e952995;       (* arm_TRN1 Q21 Q12 Q21 32 128 *)
  0x4e9e69ac;       (* arm_TRN2 Q12 Q13 Q30 32 128 *)
  0x4e9e29ad;       (* arm_TRN1 Q13 Q13 Q30 32 128 *)
  0x3dc00c49;       (* arm_LDR Q9 X2 (Immediate_Offset (word 48)) *)
  0x3dc0145f;       (* arm_LDR Q31 X2 (Immediate_Offset (word 80)) *)
  0x4ecc28cf;       (* arm_TRN1 Q15 Q6 Q12 64 128 *)
  0x4ecd2aa5;       (* arm_TRN1 Q5 Q21 Q13 64 128 *)
  0x4ecd6ab5;       (* arm_TRN2 Q21 Q21 Q13 64 128 *)
  0x4ecc68d9;       (* arm_TRN2 Q25 Q6 Q12 64 128 *)
  0x3dc0084c;       (* arm_LDR Q12 X2 (Immediate_Offset (word 32)) *)
  0x6e6f84be;       (* arm_SUB_VEC Q30 Q5 Q15 16 128 *)
  0x3dc01054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 64)) *)
  0x4e8a2866;       (* arm_TRN1 Q6 Q3 Q10 32 128 *)
  0x6e69b7c9;       (* arm_SQRDMULH_VEC Q9 Q30 Q9 16 128 *)
  0x6e7986ad;       (* arm_SUB_VEC Q13 Q21 Q25 16 128 *)
  0x6e7fb5bf;       (* arm_SQRDMULH_VEC Q31 Q13 Q31 16 128 *)
  0x4e6f84af;       (* arm_ADD_VEC Q15 Q5 Q15 16 128 *)
  0x4e7986a5;       (* arm_ADD_VEC Q5 Q21 Q25 16 128 *)
  0x3dc01c75;       (* arm_LDR Q21 X3 (Immediate_Offset (word 112)) *)
  0x4e749db6;       (* arm_MUL_VEC Q22 Q13 Q20 16 128 *)
  0x3dc0186d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 96)) *)
  0x4e6c9fd8;       (* arm_MUL_VEC Q24 Q30 Q12 16 128 *)
  0x6e6585ec;       (* arm_SUB_VEC Q12 Q15 Q5 16 128 *)
  0x3dc0045c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 16)) *)
  0x4e8a687e;       (* arm_TRN2 Q30 Q3 Q10 32 128 *)
  0x6f4743f6;       (* arm_MLS_VEC Q22 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9569aa;       (* arm_TRN2 Q10 Q13 Q21 32 128 *)
  0x3cc60453;       (* arm_LDR Q19 X2 (Postimmediate_Offset (word 96)) *)
  0x4e9529a3;       (* arm_TRN1 Q3 Q13 Q21 32 128 *)
  0x6f474138;       (* arm_MLS_VEC Q24 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4eca2bc9;       (* arm_TRN1 Q9 Q30 Q10 64 128 *)
  0x4ec328df;       (* arm_TRN1 Q31 Q6 Q3 64 128 *)
  0x6e7cb59b;       (* arm_SQRDMULH_VEC Q27 Q12 Q28 16 128 *)
  0x3dc0084d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 32)) *)
  0x4e6585f9;       (* arm_ADD_VEC Q25 Q15 Q5 16 128 *)
  0x4e739d81;       (* arm_MUL_VEC Q1 Q12 Q19 16 128 *)
  0x6e6987f5;       (* arm_SUB_VEC Q21 Q31 Q9 16 128 *)
  0x6e768714;       (* arm_SUB_VEC Q20 Q24 Q22 16 128 *)
  0x4e6d9eac;       (* arm_MUL_VEC Q12 Q21 Q13 16 128 *)
  0x4eca6bc5;       (* arm_TRN2 Q5 Q30 Q10 64 128 *)
  0x3dc0144a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 80)) *)
  0x6e7cb68d;       (* arm_SQRDMULH_VEC Q13 Q20 Q28 16 128 *)
  0x4ec368c6;       (* arm_TRN2 Q6 Q6 Q3 64 128 *)
  0x3dc00c4f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 48)) *)
  0x6f474361;       (* arm_MLS_VEC Q1 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6584c3;       (* arm_SUB_VEC Q3 Q6 Q5 16 128 *)
  0x3dc0105e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 64)) *)
  0x4e739e93;       (* arm_MUL_VEC Q19 Q20 Q19 16 128 *)
  0x4e768714;       (* arm_ADD_VEC Q20 Q24 Q22 16 128 *)
  0x6f4741b3;       (* arm_MLS_VEC Q19 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4e942b38;       (* arm_TRN1 Q24 Q25 Q20 32 128 *)
  0x3cc1042d;       (* arm_LDR Q13 X1 (Postimmediate_Offset (word 16)) *)
  0x6e6ab46a;       (* arm_SQRDMULH_VEC Q10 Q3 Q10 16 128 *)
  0x4e946b3b;       (* arm_TRN2 Q27 Q25 Q20 32 128 *)
  0x6e6fb6b5;       (* arm_SQRDMULH_VEC Q21 Q21 Q15 16 128 *)
  0x4e936839;       (* arm_TRN2 Q25 Q1 Q19 32 128 *)
  0x4e932821;       (* arm_TRN1 Q1 Q1 Q19 32 128 *)
  0x4e7e9c7e;       (* arm_MUL_VEC Q30 Q3 Q30 16 128 *)
  0x4ed92b74;       (* arm_TRN1 Q20 Q27 Q25 64 128 *)
  0x4ec12b0f;       (* arm_TRN1 Q15 Q24 Q1 64 128 *)
  0x6f47415e;       (* arm_MLS_VEC Q30 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed96b79;       (* arm_TRN2 Q25 Q27 Q25 64 128 *)
  0x6e7485e3;       (* arm_SUB_VEC Q3 Q15 Q20 16 128 *)
  0x6f4742ac;       (* arm_MLS_VEC Q12 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec16b0a;       (* arm_TRN2 Q10 Q24 Q1 64 128 *)
  0x4f6d8062;       (* arm_MUL_VEC Q2 Q3 (Q13 :> LANE_H 2) 16 128 *)
  0x4e7485f4;       (* arm_ADD_VEC Q20 Q15 Q20 16 128 *)
  0x6e79854f;       (* arm_SUB_VEC Q15 Q10 Q25 16 128 *)
  0x4e798558;       (* arm_ADD_VEC Q24 Q10 Q25 16 128 *)
  0x4f57c295;       (* arm_SQDMULH_VEC Q21 Q20 (Q7 :> LANE_H 1) 16 128 *)
  0x4e7e8593;       (* arm_ADD_VEC Q19 Q12 Q30 16 128 *)
  0x4f57c30a;       (* arm_SQDMULH_VEC Q10 Q24 (Q7 :> LANE_H 1) 16 128 *)
  0x4f7dd063;       (* arm_SQRDMULH_VEC Q3 Q3 (Q13 :> LANE_H 3) 16 128 *)
  0x6e7e859e;       (* arm_SUB_VEC Q30 Q12 Q30 16 128 *)
  0x4f4d89ee;       (* arm_MUL_VEC Q14 Q15 (Q13 :> LANE_H 4) 16 128 *)
  0x4f1526ac;       (* arm_SRSHR_VEC Q12 Q21 11 16 128 *)
  0x4f152555;       (* arm_SRSHR_VEC Q21 Q10 11 16 128 *)
  0x4f5dd9ea;       (* arm_SQRDMULH_VEC Q10 Q15 (Q13 :> LANE_H 5) 16 128 *)
  0x6f474194;       (* arm_MLS_VEC Q20 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742b8;       (* arm_MLS_VEC Q24 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6987fb;       (* arm_ADD_VEC Q27 Q31 Q9 16 128 *)
  0x4e6584d9;       (* arm_ADD_VEC Q25 Q6 Q5 16 128 *)
  0x3dc0045d;       (* arm_LDR Q29 X2 (Immediate_Offset (word 16)) *)
  0x6f474062;       (* arm_MLS_VEC Q2 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6e798770;       (* arm_SUB_VEC Q16 Q27 Q25 16 128 *)
  0x6f47414e;       (* arm_MLS_VEC Q14 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc60456;       (* arm_LDR Q22 X2 (Postimmediate_Offset (word 96)) *)
  0x6e7db611;       (* arm_SQRDMULH_VEC Q17 Q16 Q29 16 128 *)
  0x4e769fc1;       (* arm_MUL_VEC Q1 Q30 Q22 16 128 *)
  0x6e788697;       (* arm_SUB_VEC Q23 Q20 Q24 16 128 *)
  0x4e78868c;       (* arm_ADD_VEC Q12 Q20 Q24 16 128 *)
  0x4f5dd2f2;       (* arm_SQRDMULH_VEC Q18 Q23 (Q13 :> LANE_H 1) 16 128 *)
  0x6e6e8458;       (* arm_SUB_VEC Q24 Q2 Q14 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x4e798764;       (* arm_ADD_VEC Q4 Q27 Q25 16 128 *)
  0x4e769e09;       (* arm_MUL_VEC Q9 Q16 Q22 16 128 *)
  0x4e6e8448;       (* arm_ADD_VEC Q8 Q2 Q14 16 128 *)
  0x4e932894;       (* arm_TRN1 Q20 Q4 Q19 32 128 *)
  0x6e7db7d5;       (* arm_SQRDMULH_VEC Q21 Q30 Q29 16 128 *)
  0x4e93688f;       (* arm_TRN2 Q15 Q4 Q19 32 128 *)
  0x3cc60456;       (* arm_LDR Q22 X2 (Postimmediate_Offset (word 96)) *)
  0x4f5dd304;       (* arm_SQRDMULH_VEC Q4 Q24 (Q13 :> LANE_H 1) 16 128 *)
  0x6f474229;       (* arm_MLS_VEC Q9 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742a1;       (* arm_MLS_VEC Q1 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0207b;       (* arm_LDR Q27 X3 (Immediate_Offset (word 128)) *)
  0x4f4d831a;       (* arm_MUL_VEC Q26 Q24 (Q13 :> LANE_H 0) 16 128 *)
  0x6f47409a;       (* arm_MLS_VEC Q26 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4e81693e;       (* arm_TRN2 Q30 Q9 Q1 32 128 *)
  0x4f4d82e0;       (* arm_MUL_VEC Q0 Q23 (Q13 :> LANE_H 0) 16 128 *)
  0x4e812931;       (* arm_TRN1 Q17 Q9 Q1 32 128 *)
  0x4ede29f8;       (* arm_TRN1 Q24 Q15 Q30 64 128 *)
  0x3cc1042d;       (* arm_LDR Q13 X1 (Postimmediate_Offset (word 16)) *)
  0x6f474240;       (* arm_MLS_VEC Q0 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed12a85;       (* arm_TRN1 Q5 Q20 Q17 64 128 *)
  0x4ede69fd;       (* arm_TRN2 Q29 Q15 Q30 64 128 *)
  0x3d800c7a;       (* arm_STR Q26 X3 (Immediate_Offset (word 48)) *)
  0x4f57c115;       (* arm_SQDMULH_VEC Q21 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x4e7884a4;       (* arm_ADD_VEC Q4 Q5 Q24 16 128 *)
  0x4ed16a97;       (* arm_TRN2 Q23 Q20 Q17 64 128 *)
  0x3dc02c6f;       (* arm_LDR Q15 X3 (Immediate_Offset (word 176)) *)
  0x6e7884b0;       (* arm_SUB_VEC Q16 Q5 Q24 16 128 *)
  0x4f57c086;       (* arm_SQDMULH_VEC Q6 Q4 (Q7 :> LANE_H 1) 16 128 *)
  0x3d800860;       (* arm_STR Q0 X3 (Immediate_Offset (word 32)) *)
  0x3dc02460;       (* arm_LDR Q0 X3 (Immediate_Offset (word 144)) *)
  0x6e7d86f2;       (* arm_SUB_VEC Q18 Q23 Q29 16 128 *)
  0x4f6d8202;       (* arm_MUL_VEC Q2 Q16 (Q13 :> LANE_H 2) 16 128 *)
  0x4e7d86fa;       (* arm_ADD_VEC Q26 Q23 Q29 16 128 *)
  0x3dc0287d;       (* arm_LDR Q29 X3 (Immediate_Offset (word 160)) *)
  0x4f1526b1;       (* arm_SRSHR_VEC Q17 Q21 11 16 128 *)
  0x4f4d8a4e;       (* arm_MUL_VEC Q14 Q18 (Q13 :> LANE_H 4) 16 128 *)
  0x4e806b7e;       (* arm_TRN2 Q30 Q27 Q0 32 128 *)
  0x3cdd0041;       (* arm_LDR Q1 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x4f1524d9;       (* arm_SRSHR_VEC Q25 Q6 11 16 128 *)
  0x4f57c34a;       (* arm_SQDMULH_VEC Q10 Q26 (Q7 :> LANE_H 1) 16 128 *)
  0x4e8f6bb8;       (* arm_TRN2 Q24 Q29 Q15 32 128 *)
  0x3cde0054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e802b6b;       (* arm_TRN1 Q11 Q27 Q0 32 128 *)
  0x4f7dd217;       (* arm_SQRDMULH_VEC Q23 Q16 (Q13 :> LANE_H 3) 16 128 *)
  0x4e8f2ba5;       (* arm_TRN1 Q5 Q29 Q15 32 128 *)
  0x6f474324;       (* arm_MLS_VEC Q4 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x3c84046c;       (* arm_STR Q12 X3 (Postimmediate_Offset (word 64)) *)
  0x4ed82bd0;       (* arm_TRN1 Q16 Q30 Q24 64 128 *)
  0x3cdb005d;       (* arm_LDR Q29 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4f15255c;       (* arm_SRSHR_VEC Q28 Q10 11 16 128 *)
  0x6f474228;       (* arm_MLS_VEC Q8 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed86bc3;       (* arm_TRN2 Q3 Q30 Q24 64 128 *)
  0x4f5dda53;       (* arm_SQRDMULH_VEC Q19 Q18 (Q13 :> LANE_H 5) 16 128 *)
  0x4ec52972;       (* arm_TRN1 Q18 Q11 Q5 64 128 *)
  0x4ec5696b;       (* arm_TRN2 Q11 Q11 Q5 64 128 *)
  0x3cdf005f;       (* arm_LDR Q31 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f47439a;       (* arm_MLS_VEC Q26 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e708658;       (* arm_SUB_VEC Q24 Q18 Q16 16 128 *)
  0x6e63856f;       (* arm_SUB_VEC Q15 Q11 Q3 16 128 *)
  0x3c9d0068;       (* arm_STR Q8 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e70865b;       (* arm_ADD_VEC Q27 Q18 Q16 16 128 *)
  0x6e61b701;       (* arm_SQRDMULH_VEC Q1 Q24 Q1 16 128 *)
  0x4e638579;       (* arm_ADD_VEC Q25 Q11 Q3 16 128 *)
  0x3cdc0049;       (* arm_LDR Q9 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6e7fb5ff;       (* arm_SQRDMULH_VEC Q31 Q15 Q31 16 128 *)
  0x4e7a848c;       (* arm_ADD_VEC Q12 Q4 Q26 16 128 *)
  0x4e749de5;       (* arm_MUL_VEC Q5 Q15 Q20 16 128 *)
  0x4e699f0f;       (* arm_MUL_VEC Q15 Q24 Q9 16 128 *)
  0x6f4743e5;       (* arm_MLS_VEC Q5 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6e798770;       (* arm_SUB_VEC Q16 Q27 Q25 16 128 *)
  0x6e7db611;       (* arm_SQRDMULH_VEC Q17 Q16 Q29 16 128 *)
  0x6f47402f;       (* arm_MLS_VEC Q15 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742e2;       (* arm_MLS_VEC Q2 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a8497;       (* arm_SUB_VEC Q23 Q4 Q26 16 128 *)
  0x6f47426e;       (* arm_MLS_VEC Q14 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6585fe;       (* arm_SUB_VEC Q30 Q15 Q5 16 128 *)
  0x4e6585f3;       (* arm_ADD_VEC Q19 Q15 Q5 16 128 *)
  0x4f5dd2f2;       (* arm_SQRDMULH_VEC Q18 Q23 (Q13 :> LANE_H 1) 16 128 *)
  0x4e769fc1;       (* arm_MUL_VEC Q1 Q30 Q22 16 128 *)
  0x6e6e8458;       (* arm_SUB_VEC Q24 Q2 Q14 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff5e4;       (* arm_CBNZ X4 (word 2096828) *)
  0x6e7db7ca;       (* arm_SQRDMULH_VEC Q10 Q30 Q29 16 128 *)
  0x4e798764;       (* arm_ADD_VEC Q4 Q27 Q25 16 128 *)
  0x4e6e845c;       (* arm_ADD_VEC Q28 Q2 Q14 16 128 *)
  0x3c84046c;       (* arm_STR Q12 X3 (Postimmediate_Offset (word 64)) *)
  0x4e769e02;       (* arm_MUL_VEC Q2 Q16 Q22 16 128 *)
  0x4e932889;       (* arm_TRN1 Q9 Q4 Q19 32 128 *)
  0x4e93688b;       (* arm_TRN2 Q11 Q4 Q19 32 128 *)
  0x3cc10425;       (* arm_LDR Q5 X1 (Postimmediate_Offset (word 16)) *)
  0x6f474222;       (* arm_MLS_VEC Q2 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474141;       (* arm_MLS_VEC Q1 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f5dd308;       (* arm_SQRDMULH_VEC Q8 Q24 (Q13 :> LANE_H 1) 16 128 *)
  0x4f4d8314;       (* arm_MUL_VEC Q20 Q24 (Q13 :> LANE_H 0) 16 128 *)
  0x4e812844;       (* arm_TRN1 Q4 Q2 Q1 32 128 *)
  0x4f57c39a;       (* arm_SQDMULH_VEC Q26 Q28 (Q7 :> LANE_H 1) 16 128 *)
  0x4e81684e;       (* arm_TRN2 Q14 Q2 Q1 32 128 *)
  0x4ec46923;       (* arm_TRN2 Q3 Q9 Q4 64 128 *)
  0x4f4d82fb;       (* arm_MUL_VEC Q27 Q23 (Q13 :> LANE_H 0) 16 128 *)
  0x4ece696a;       (* arm_TRN2 Q10 Q11 Q14 64 128 *)
  0x4ec42938;       (* arm_TRN1 Q24 Q9 Q4 64 128 *)
  0x4e6a8460;       (* arm_ADD_VEC Q0 Q3 Q10 16 128 *)
  0x6f47425b;       (* arm_MLS_VEC Q27 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4ece297e;       (* arm_TRN1 Q30 Q11 Q14 64 128 *)
  0x6e6a8464;       (* arm_SUB_VEC Q4 Q3 Q10 16 128 *)
  0x4f57c001;       (* arm_SQDMULH_VEC Q1 Q0 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7e8719;       (* arm_SUB_VEC Q25 Q24 Q30 16 128 *)
  0x4e7e8718;       (* arm_ADD_VEC Q24 Q24 Q30 16 128 *)
  0x4f45889f;       (* arm_MUL_VEC Q31 Q4 (Q5 :> LANE_H 4) 16 128 *)
  0x4f57c309;       (* arm_SQDMULH_VEC Q9 Q24 (Q7 :> LANE_H 1) 16 128 *)
  0x4f15242b;       (* arm_SRSHR_VEC Q11 Q1 11 16 128 *)
  0x3c9e007b;       (* arm_STR Q27 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x4f152757;       (* arm_SRSHR_VEC Q23 Q26 11 16 128 *)
  0x4f75d331;       (* arm_SQRDMULH_VEC Q17 Q25 (Q5 :> LANE_H 3) 16 128 *)
  0x4f55d89b;       (* arm_SQRDMULH_VEC Q27 Q4 (Q5 :> LANE_H 5) 16 128 *)
  0x4f15252a;       (* arm_SRSHR_VEC Q10 Q9 11 16 128 *)
  0x4f658336;       (* arm_MUL_VEC Q22 Q25 (Q5 :> LANE_H 2) 16 128 *)
  0x6f474236;       (* arm_MLS_VEC Q22 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47437f;       (* arm_MLS_VEC Q31 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474160;       (* arm_MLS_VEC Q0 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474158;       (* arm_MLS_VEC Q24 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7f86ce;       (* arm_SUB_VEC Q14 Q22 Q31 16 128 *)
  0x6f4742fc;       (* arm_MLS_VEC Q28 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7f86d2;       (* arm_ADD_VEC Q18 Q22 Q31 16 128 *)
  0x4f57c246;       (* arm_SQDMULH_VEC Q6 Q18 (Q7 :> LANE_H 1) 16 128 *)
  0x6e60871a;       (* arm_SUB_VEC Q26 Q24 Q0 16 128 *)
  0x4e60871f;       (* arm_ADD_VEC Q31 Q24 Q0 16 128 *)
  0x4f4581cc;       (* arm_MUL_VEC Q12 Q14 (Q5 :> LANE_H 0) 16 128 *)
  0x3c9d007c;       (* arm_STR Q28 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c84047f;       (* arm_STR Q31 X3 (Postimmediate_Offset (word 64)) *)
  0x4f55d35f;       (* arm_SQRDMULH_VEC Q31 Q26 (Q5 :> LANE_H 1) 16 128 *)
  0x4f458351;       (* arm_MUL_VEC Q17 Q26 (Q5 :> LANE_H 0) 16 128 *)
  0x4f55d1d6;       (* arm_SQRDMULH_VEC Q22 Q14 (Q5 :> LANE_H 1) 16 128 *)
  0x6f4743f1;       (* arm_MLS_VEC Q17 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474114;       (* arm_MLS_VEC Q20 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4f1524c8;       (* arm_SRSHR_VEC Q8 Q6 11 16 128 *)
  0x6f4742cc;       (* arm_MLS_VEC Q12 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9e0071;       (* arm_STR Q17 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x6f474112;       (* arm_MLS_VEC Q18 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9b0074;       (* arm_STR Q20 X3 (Immediate_Offset (word 18446744073709551536)) *)
  0x3c9f006c;       (* arm_STR Q12 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9d0072;       (* arm_STR Q18 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0401c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 256)) *)
  0x3dc05009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 320)) *)
  0x3dc0700a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 448)) *)
  0x3dc0601d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 384)) *)
  0x3dc03010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 192)) *)
  0x3dc0201e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 128)) *)
  0x3dc01019;       (* arm_LDR Q25 X0 (Immediate_Offset (word 64)) *)
  0x3dc00014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 0)) *)
  0x4e69878d;       (* arm_ADD_VEC Q13 Q28 Q9 16 128 *)
  0x6e698788;       (* arm_SUB_VEC Q8 Q28 Q9 16 128 *)
  0x4e6a87a5;       (* arm_ADD_VEC Q5 Q29 Q10 16 128 *)
  0x6e6a87a6;       (* arm_SUB_VEC Q6 Q29 Q10 16 128 *)
  0x6e7087df;       (* arm_SUB_VEC Q31 Q30 Q16 16 128 *)
  0x4f71d116;       (* arm_SQRDMULH_VEC Q22 Q8 (Q1 :> LANE_H 3) 16 128 *)
  0x6e798695;       (* arm_SUB_VEC Q21 Q20 Q25 16 128 *)
  0x3dc00413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 16)) *)
  0x4e7087d0;       (* arm_ADD_VEC Q16 Q30 Q16 16 128 *)
  0x4f51d3eb;       (* arm_SQRDMULH_VEC Q11 Q31 (Q1 :> LANE_H 1) 16 128 *)
  0x4e798698;       (* arm_ADD_VEC Q24 Q20 Q25 16 128 *)
  0x3dc02403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 144)) *)
  0x4f70daa4;       (* arm_SQRDMULH_VEC Q4 Q21 (Q0 :> LANE_H 7) 16 128 *)
  0x6e6585aa;       (* arm_SUB_VEC Q10 Q13 Q5 16 128 *)
  0x6e708702;       (* arm_SUB_VEC Q2 Q24 Q16 16 128 *)
  0x3dc0340c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 208)) *)
  0x4e6585ad;       (* arm_ADD_VEC Q13 Q13 Q5 16 128 *)
  0x4f51d8c5;       (* arm_SQRDMULH_VEC Q5 Q6 (Q1 :> LANE_H 5) 16 128 *)
  0x4e70871a;       (* arm_ADD_VEC Q26 Q24 Q16 16 128 *)
  0x3dc01411;       (* arm_LDR Q17 X0 (Immediate_Offset (word 80)) *)
  0x4f608ab9;       (* arm_MUL_VEC Q25 Q21 (Q0 :> LANE_H 6) 16 128 *)
  0x3dc07418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 464)) *)
  0x6e6d875b;       (* arm_SUB_VEC Q27 Q26 Q13 16 128 *)
  0x3dc06414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 400)) *)
  0x4f4183ee;       (* arm_MUL_VEC Q14 Q31 (Q1 :> LANE_H 0) 16 128 *)
  0x4e6c8470;       (* arm_ADD_VEC Q16 Q3 Q12 16 128 *)
  0x4e718672;       (* arm_ADD_VEC Q18 Q19 Q17 16 128 *)
  0x3dc0441e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 272)) *)
  0x4f61811c;       (* arm_MUL_VEC Q28 Q8 (Q1 :> LANE_H 2) 16 128 *)
  0x4e6d8755;       (* arm_ADD_VEC Q21 Q26 Q13 16 128 *)
  0x6e70864f;       (* arm_SUB_VEC Q15 Q18 Q16 16 128 *)
  0x4f4188c8;       (* arm_MUL_VEC Q8 Q6 (Q1 :> LANE_H 4) 16 128 *)
  0x3c810415;       (* arm_STR Q21 X0 (Postimmediate_Offset (word 16)) *)
  0x4e708652;       (* arm_ADD_VEC Q18 Q18 Q16 16 128 *)
  0x6f474099;       (* arm_MLS_VEC Q25 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740a8;       (* arm_MLS_VEC Q8 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742dc;       (* arm_MLS_VEC Q28 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47416e;       (* arm_MLS_VEC Q14 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d949;       (* arm_SQRDMULH_VEC Q9 Q10 (Q0 :> LANE_H 5) 16 128 *)
  0x6e688795;       (* arm_SUB_VEC Q21 Q28 Q8 16 128 *)
  0x4e68879f;       (* arm_ADD_VEC Q31 Q28 Q8 16 128 *)
  0x4f70d050;       (* arm_SQRDMULH_VEC Q16 Q2 (Q0 :> LANE_H 3) 16 128 *)
  0x6e6e872d;       (* arm_SUB_VEC Q13 Q25 Q14 16 128 *)
  0x4e6e8739;       (* arm_ADD_VEC Q25 Q25 Q14 16 128 *)
  0x4f50dab6;       (* arm_SQRDMULH_VEC Q22 Q21 (Q0 :> LANE_H 5) 16 128 *)
  0x4f70d1ba;       (* arm_SQRDMULH_VEC Q26 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x6e7f8725;       (* arm_SUB_VEC Q5 Q25 Q31 16 128 *)
  0x4f40894a;       (* arm_MUL_VEC Q10 Q10 (Q0 :> LANE_H 4) 16 128 *)
  0x4f608042;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 2) 16 128 *)
  0x4f6081a4;       (* arm_MUL_VEC Q4 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x4f408abd;       (* arm_MUL_VEC Q29 Q21 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47412a;       (* arm_MLS_VEC Q10 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474202;       (* arm_MLS_VEC Q2 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742dd;       (* arm_MLS_VEC Q29 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474344;       (* arm_MLS_VEC Q4 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6a8448;       (* arm_ADD_VEC Q8 Q2 Q10 16 128 *)
  0x6e6a8442;       (* arm_SUB_VEC Q2 Q2 Q10 16 128 *)
  0x4f50d37a;       (* arm_SQRDMULH_VEC Q26 Q27 (Q0 :> LANE_H 1) 16 128 *)
  0x3d801c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 112)) *)
  0x4f408368;       (* arm_MUL_VEC Q8 Q27 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7d8490;       (* arm_SUB_VEC Q16 Q4 Q29 16 128 *)
  0x4e7d849c;       (* arm_ADD_VEC Q28 Q4 Q29 16 128 *)
  0x4f50d04a;       (* arm_SQRDMULH_VEC Q10 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d0bb;       (* arm_SQRDMULH_VEC Q27 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474348;       (* arm_MLS_VEC Q8 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d21d;       (* arm_SQRDMULH_VEC Q29 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6e718666;       (* arm_SUB_VEC Q6 Q19 Q17 16 128 *)
  0x3d802c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 176)) *)
  0x3dc05016;       (* arm_LDR Q22 X0 (Immediate_Offset (word 320)) *)
  0x4f408057;       (* arm_MUL_VEC Q23 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x4f70d8cb;       (* arm_SQRDMULH_VEC Q11 Q6 (Q0 :> LANE_H 7) 16 128 *)
  0x3d803c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 240)) *)
  0x4e78868d;       (* arm_ADD_VEC Q13 Q20 Q24 16 128 *)
  0x4f6088da;       (* arm_MUL_VEC Q26 Q6 (Q0 :> LANE_H 6) 16 128 *)
  0x4e7687c4;       (* arm_ADD_VEC Q4 Q30 Q22 16 128 *)
  0x4e7f8726;       (* arm_ADD_VEC Q6 Q25 Q31 16 128 *)
  0x4f40820e;       (* arm_MUL_VEC Q14 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x6e6d849f;       (* arm_SUB_VEC Q31 Q4 Q13 16 128 *)
  0x6f47417a;       (* arm_MLS_VEC Q26 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6d848d;       (* arm_ADD_VEC Q13 Q4 Q13 16 128 *)
  0x3d800c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 48)) *)
  0x6f4743ae;       (* arm_MLS_VEC Q14 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d865c;       (* arm_SUB_VEC Q28 Q18 Q13 16 128 *)
  0x6e7687dd;       (* arm_SUB_VEC Q29 Q30 Q22 16 128 *)
  0x3dc01411;       (* arm_LDR Q17 X0 (Immediate_Offset (word 80)) *)
  0x4f408388;       (* arm_MUL_VEC Q8 Q28 (Q0 :> LANE_H 0) 16 128 *)
  0x6e6c8463;       (* arm_SUB_VEC Q3 Q3 Q12 16 128 *)
  0x4f50d395;       (* arm_SQRDMULH_VEC Q21 Q28 (Q0 :> LANE_H 1) 16 128 *)
  0x3d806c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 432)) *)
  0x6e78868e;       (* arm_SUB_VEC Q14 Q20 Q24 16 128 *)
  0x4f418070;       (* arm_MUL_VEC Q16 Q3 (Q1 :> LANE_H 0) 16 128 *)
  0x4f51d069;       (* arm_SQRDMULH_VEC Q9 Q3 (Q1 :> LANE_H 1) 16 128 *)
  0x4f50dbe4;       (* arm_SQRDMULH_VEC Q4 Q31 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408beb;       (* arm_MUL_VEC Q11 Q31 (Q0 :> LANE_H 4) 16 128 *)
  0x3dc0340c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 208)) *)
  0x3dc02403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 144)) *)
  0x6f474130;       (* arm_MLS_VEC Q16 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d3b3;       (* arm_SQRDMULH_VEC Q19 Q29 (Q1 :> LANE_H 3) 16 128 *)
  0x6f47408b;       (* arm_MLS_VEC Q11 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6e708756;       (* arm_SUB_VEC Q22 Q26 Q16 16 128 *)
  0x4f51d9c6;       (* arm_SQRDMULH_VEC Q6 Q14 (Q1 :> LANE_H 5) 16 128 *)
  0x3dc0441e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 272)) *)
  0x4f6082c4;       (* arm_MUL_VEC Q4 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x4e708759;       (* arm_ADD_VEC Q25 Q26 Q16 16 128 *)
  0x4f70d2dc;       (* arm_SQRDMULH_VEC Q28 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6183b6;       (* arm_MUL_VEC Q22 Q29 (Q1 :> LANE_H 2) 16 128 *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6c8469;       (* arm_ADD_VEC Q9 Q3 Q12 16 128 *)
  0x6f474276;       (* arm_MLS_VEC Q22 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc00413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 16)) *)
  0x4f4189dd;       (* arm_MUL_VEC Q29 Q14 (Q1 :> LANE_H 4) 16 128 *)
  0x4e6d864e;       (* arm_ADD_VEC Q14 Q18 Q13 16 128 *)
  0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
  0x6f4740dd;       (* arm_MLS_VEC Q29 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x3c81040e;       (* arm_STR Q14 X0 (Postimmediate_Offset (word 16)) *)
  0x4e718666;       (* arm_ADD_VEC Q6 Q19 Q17 16 128 *)
  0x4f70d1ed;       (* arm_SQRDMULH_VEC Q13 Q15 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6081f7;       (* arm_MUL_VEC Q23 Q15 (Q0 :> LANE_H 2) 16 128 *)
  0x6e6984cf;       (* arm_SUB_VEC Q15 Q6 Q9 16 128 *)
  0x4e7d86df;       (* arm_ADD_VEC Q31 Q22 Q29 16 128 *)
  0x4f4080b2;       (* arm_MUL_VEC Q18 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4741b7;       (* arm_MLS_VEC Q23 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7d86cd;       (* arm_SUB_VEC Q13 Q22 Q29 16 128 *)
  0x6f4742a8;       (* arm_MLS_VEC Q8 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc07018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 448)) *)
  0x4f50d9b6;       (* arm_SQRDMULH_VEC Q22 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x6e6b86e2;       (* arm_SUB_VEC Q2 Q23 Q11 16 128 *)
  0x4e6b86f0;       (* arm_ADD_VEC Q16 Q23 Q11 16 128 *)
  0x4f4089b7;       (* arm_MUL_VEC Q23 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x6e7f8725;       (* arm_SUB_VEC Q5 Q25 Q31 16 128 *)
  0x6f474384;       (* arm_MLS_VEC Q4 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801c10;       (* arm_STR Q16 X0 (Immediate_Offset (word 112)) *)
  0x6f4742d7;       (* arm_MLS_VEC Q23 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474372;       (* arm_MLS_VEC Q18 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d0bb;       (* arm_SQRDMULH_VEC Q27 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x6e778490;       (* arm_SUB_VEC Q16 Q4 Q23 16 128 *)
  0x4e77849c;       (* arm_ADD_VEC Q28 Q4 Q23 16 128 *)
  0x4f50d04a;       (* arm_SQRDMULH_VEC Q10 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x3d804812;       (* arm_STR Q18 X0 (Immediate_Offset (word 288)) *)
  0x4e6984d2;       (* arm_ADD_VEC Q18 Q6 Q9 16 128 *)
  0x4f50d21d;       (* arm_SQRDMULH_VEC Q29 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc06014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 384)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4f4080a5;       (* arm_MUL_VEC Q5 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7f8739;       (* arm_ADD_VEC Q25 Q25 Q31 16 128 *)
  0x6e6c8475;       (* arm_SUB_VEC Q21 Q3 Q12 16 128 *)
  0x3d802c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 176)) *)
  0x4f408044;       (* arm_MUL_VEC Q4 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x6e718666;       (* arm_SUB_VEC Q6 Q19 Q17 16 128 *)
  0x3d803c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 240)) *)
  0x4e78868c;       (* arm_ADD_VEC Q12 Q20 Q24 16 128 *)
  0x6e788682;       (* arm_SUB_VEC Q2 Q20 Q24 16 128 *)
  0x4f6081e8;       (* arm_MUL_VEC Q8 Q15 (Q0 :> LANE_H 2) 16 128 *)
  0x3d800c19;       (* arm_STR Q25 X0 (Immediate_Offset (word 48)) *)
  0x3dc05017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 320)) *)
  0x4f70d1fc;       (* arm_SQRDMULH_VEC Q28 Q15 (Q0 :> LANE_H 3) 16 128 *)
  0x6f474144;       (* arm_MLS_VEC Q4 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7787d1;       (* arm_ADD_VEC Q17 Q30 Q23 16 128 *)
  0x6f474365;       (* arm_MLS_VEC Q5 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7787c9;       (* arm_SUB_VEC Q9 Q30 Q23 16 128 *)
  0x4e6c862b;       (* arm_ADD_VEC Q11 Q17 Q12 16 128 *)
  0x4f40820d;       (* arm_MUL_VEC Q13 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x6e6c862a;       (* arm_SUB_VEC Q10 Q17 Q12 16 128 *)
  0x3d805c04;       (* arm_STR Q4 X0 (Immediate_Offset (word 368)) *)
  0x6e6b8644;       (* arm_SUB_VEC Q4 Q18 Q11 16 128 *)
  0x6f4743ad;       (* arm_MLS_VEC Q13 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6b8654;       (* arm_ADD_VEC Q20 Q18 Q11 16 128 *)
  0x3d804c05;       (* arm_STR Q5 X0 (Immediate_Offset (word 304)) *)
  0x3c810414;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 16)) *)
  0x4f51d2b2;       (* arm_SQRDMULH_VEC Q18 Q21 (Q1 :> LANE_H 1) 16 128 *)
  0x4f4182b3;       (* arm_MUL_VEC Q19 Q21 (Q1 :> LANE_H 0) 16 128 *)
  0x3d80680d;       (* arm_STR Q13 X0 (Immediate_Offset (word 416)) *)
  0x4f6088d8;       (* arm_MUL_VEC Q24 Q6 (Q0 :> LANE_H 6) 16 128 *)
  0x4f70d8cf;       (* arm_SQRDMULH_VEC Q15 Q6 (Q0 :> LANE_H 7) 16 128 *)
  0x6f474388;       (* arm_MLS_VEC Q8 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f418851;       (* arm_MUL_VEC Q17 Q2 (Q1 :> LANE_H 4) 16 128 *)
  0x4f51d845;       (* arm_SQRDMULH_VEC Q5 Q2 (Q1 :> LANE_H 5) 16 128 *)
  0x4f618136;       (* arm_MUL_VEC Q22 Q9 (Q1 :> LANE_H 2) 16 128 *)
  0x4f71d129;       (* arm_SQRDMULH_VEC Q9 Q9 (Q1 :> LANE_H 3) 16 128 *)
  0x6f4740b1;       (* arm_MLS_VEC Q17 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d955;       (* arm_SQRDMULH_VEC Q21 Q10 (Q0 :> LANE_H 5) 16 128 *)
  0x6f474253;       (* arm_MLS_VEC Q19 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40894b;       (* arm_MUL_VEC Q11 Q10 (Q0 :> LANE_H 4) 16 128 *)
  0x6f4741f8;       (* arm_MLS_VEC Q24 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d09c;       (* arm_SQRDMULH_VEC Q28 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40809b;       (* arm_MUL_VEC Q27 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x6e738712;       (* arm_SUB_VEC Q18 Q24 Q19 16 128 *)
  0x4e73871d;       (* arm_ADD_VEC Q29 Q24 Q19 16 128 *)
  0x6f474136;       (* arm_MLS_VEC Q22 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47439b;       (* arm_MLS_VEC Q27 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742ab;       (* arm_MLS_VEC Q11 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7186cd;       (* arm_ADD_VEC Q13 Q22 Q17 16 128 *)
  0x4f70d254;       (* arm_SQRDMULH_VEC Q20 Q18 (Q0 :> LANE_H 3) 16 128 *)
  0x6e7186da;       (* arm_SUB_VEC Q26 Q22 Q17 16 128 *)
  0x4f60825f;       (* arm_MUL_VEC Q31 Q18 (Q0 :> LANE_H 2) 16 128 *)
  0x6e6d87b7;       (* arm_SUB_VEC Q23 Q29 Q13 16 128 *)
  0x4e6d87bd;       (* arm_ADD_VEC Q29 Q29 Q13 16 128 *)
  0x3d803c1b;       (* arm_STR Q27 X0 (Immediate_Offset (word 240)) *)
  0x4f50db42;       (* arm_SQRDMULH_VEC Q2 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x6e6b850e;       (* arm_SUB_VEC Q14 Q8 Q11 16 128 *)
  0x3d800c1d;       (* arm_STR Q29 X0 (Immediate_Offset (word 48)) *)
  0x4e6b8505;       (* arm_ADD_VEC Q5 Q8 Q11 16 128 *)
  0x6f47429f;       (* arm_MLS_VEC Q31 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801c05;       (* arm_STR Q5 X0 (Immediate_Offset (word 112)) *)
  0x4f4082ef;       (* arm_MUL_VEC Q15 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x4f408b45;       (* arm_MUL_VEC Q5 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x6f474045;       (* arm_MLS_VEC Q5 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d1c8;       (* arm_SQRDMULH_VEC Q8 Q14 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d2f2;       (* arm_SQRDMULH_VEC Q18 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x6e6587eb;       (* arm_SUB_VEC Q11 Q31 Q5 16 128 *)
  0x4f4081dd;       (* arm_MUL_VEC Q29 Q14 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d163;       (* arm_SQRDMULH_VEC Q3 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x4e6587f7;       (* arm_ADD_VEC Q23 Q31 Q5 16 128 *)
  0x6f47424f;       (* arm_MLS_VEC Q15 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x3d802c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 176)) *)
  0x6f47411d;       (* arm_MLS_VEC Q29 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408179;       (* arm_MUL_VEC Q25 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0x3d804c0f;       (* arm_STR Q15 X0 (Immediate_Offset (word 304)) *)
  0x6f474079;       (* arm_MLS_VEC Q25 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3d805c1d;       (* arm_STR Q29 X0 (Immediate_Offset (word 368)) *)
  0x3d806c19;       (* arm_STR Q25 X0 (Immediate_Offset (word 432)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_INTT_EXEC = ARM_MK_EXEC_RULE mlkem_intt_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_INTT_MC =
  REWRITE_CONV[mlkem_intt_mc] `LENGTH mlkem_intt_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_INTT_PREAMBLE_LENGTH = new_definition
  `MLKEM_INTT_PREAMBLE_LENGTH = 20`;;

let MLKEM_INTT_POSTAMBLE_LENGTH = new_definition
  `MLKEM_INTT_POSTAMBLE_LENGTH = 24`;;

let MLKEM_INTT_CORE_START = new_definition
  `MLKEM_INTT_CORE_START = MLKEM_INTT_PREAMBLE_LENGTH`;;

let MLKEM_INTT_CORE_END = new_definition
  `MLKEM_INTT_CORE_END = LENGTH mlkem_intt_mc - MLKEM_INTT_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_INTT_MC;
              MLKEM_INTT_CORE_START; MLKEM_INTT_CORE_END;
              MLKEM_INTT_PREAMBLE_LENGTH; MLKEM_INTT_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

let intt_constants = define
 `intt_constants z_12345 z_67 s <=>
        (!i. i < 80
             ==> read(memory :> bytes16(word_add z_12345 (word(2 * i)))) s =
                 iword(EL i intt_zetas_layer12345)) /\
        (!i. i < 384
             ==> read(memory :> bytes16(word_add z_67 (word(2 * i)))) s =
                 iword(EL i intt_zetas_layer67))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)


let MLKEM_INTT_CORRECT = prove
 (`!a z_12345 z_67 x pc.
      ALL (nonoverlapping (a,512))
          [(word pc,LENGTH mlkem_intt_mc); (z_12345,160); (z_67,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word (pc + MLKEM_INTT_CORE_START) /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                intt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + MLKEM_INTT_CORE_END) /\
                !i. i < 256
                    ==> let zi =
                         read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &26624)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `z_12345:int64`; `z_67:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  REWRITE_TAC[intt_constants] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  REWRITE_TAC[intt_zetas_layer12345; intt_zetas_layer67] THEN
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

  MAP_UNTIL_TARGET_PC (fun n -> ARM_STEPS_TAC MLKEM_INTT_EXEC [n] THEN
            (SIMD_SIMPLIFY_TAC [barred; barmul]))
            1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE (SIMD_SIMPLIFY_CONV []) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Turn the conclusion into an explicit conjunction and split it up ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM I_THM] THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1153" THEN
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

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_INTT_SUBROUTINE_CORRECT = prove
 (`!a z_12345 z_67 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,LENGTH mlkem_intt_mc); (z_12345,160); (z_67,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                intt_constants z_12345 z_67 s /\
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
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  let TWEAK_CONV =
    REWRITE_CONV[intt_constants] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[fst MLKEM_INTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_INTT_EXEC
   (REWRITE_RULE[fst MLKEM_INTT_EXEC] (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_INTT_CORRECT)))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
