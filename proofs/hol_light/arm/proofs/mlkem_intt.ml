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
     0x4e0a1ca7;       (* arm_INS_GEN Q7 W5 32 16 *)
     0x52827605;       (* arm_MOV W5 (rvalue (word 5040)) *)
     0x4e0e1ca7;       (* arm_INS_GEN Q7 W5 48 16 *)
     0xaa0003e3;       (* arm_MOV X3 X0 *)
     0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
     0x3dc0086a;       (* arm_LDR Q10 X3 (Immediate_Offset (word 32)) *)
     0x3dc0006d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 0)) *)
     0x3dc00463;       (* arm_LDR Q3 X3 (Immediate_Offset (word 16)) *)
     0x3dc00c6c;       (* arm_LDR Q12 X3 (Immediate_Offset (word 48)) *)
     0x4e8329a6;       (* arm_TRN1 Q6 Q13 Q3 32 128 *)
     0x4e8369b5;       (* arm_TRN2 Q21 Q13 Q3 32 128 *)
     0x4e8c294d;       (* arm_TRN1 Q13 Q10 Q12 32 128 *)
     0x4e8c694c;       (* arm_TRN2 Q12 Q10 Q12 32 128 *)
     0x3dc01456;       (* arm_LDR Q22 X2 (Immediate_Offset (word 80)) *)
     0x4ecd28c9;       (* arm_TRN1 Q9 Q6 Q13 64 128 *)
     0x4ecc6ab8;       (* arm_TRN2 Q24 Q21 Q12 64 128 *)
     0x4ecc2aa3;       (* arm_TRN1 Q3 Q21 Q12 64 128 *)
     0x4ecd68df;       (* arm_TRN2 Q31 Q6 Q13 64 128 *)
     0x4e638535;       (* arm_ADD_VEC Q21 Q9 Q3 16 128 *)
     0x4e7887e1;       (* arm_ADD_VEC Q1 Q31 Q24 16 128 *)
     0x6e7887fb;       (* arm_SUB_VEC Q27 Q31 Q24 16 128 *)
     0x3dc00851;       (* arm_LDR Q17 X2 (Immediate_Offset (word 32)) *)
     0x3dc01046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 64)) *)
     0x6e63853f;       (* arm_SUB_VEC Q31 Q9 Q3 16 128 *)
     0x3dc00c4c;       (* arm_LDR Q12 X2 (Immediate_Offset (word 48)) *)
     0x4e719fee;       (* arm_MUL_VEC Q14 Q31 Q17 16 128 *)
     0x6e76b763;       (* arm_SQRDMULH_VEC Q3 Q27 Q22 16 128 *)
     0x4e669f6b;       (* arm_MUL_VEC Q11 Q27 Q6 16 128 *)
     0x6e6cb7ed;       (* arm_SQRDMULH_VEC Q13 Q31 Q12 16 128 *)
     0x3dc00454;       (* arm_LDR Q20 X2 (Immediate_Offset (word 16)) *)
     0x6f47406b;       (* arm_MLS_VEC Q11 Q3 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4741ae;       (* arm_MLS_VEC Q14 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x6e6186af;       (* arm_SUB_VEC Q15 Q21 Q1 16 128 *)
     0x3cc6044a;       (* arm_LDR Q10 X2 (Postimmediate_Offset (word 96)) *)
     0x6e6b85c6;       (* arm_SUB_VEC Q6 Q14 Q11 16 128 *)
     0x6e74b5e5;       (* arm_SQRDMULH_VEC Q5 Q15 Q20 16 128 *)
     0x4e6a9df0;       (* arm_MUL_VEC Q16 Q15 Q10 16 128 *)
     0x4e6a9ccf;       (* arm_MUL_VEC Q15 Q6 Q10 16 128 *)
     0x6e74b4cd;       (* arm_SQRDMULH_VEC Q13 Q6 Q20 16 128 *)
     0x4e6186ac;       (* arm_ADD_VEC Q12 Q21 Q1 16 128 *)
     0x4e6b85df;       (* arm_ADD_VEC Q31 Q14 Q11 16 128 *)
     0x6f4740b0;       (* arm_MLS_VEC Q16 Q5 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4741af;       (* arm_MLS_VEC Q15 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x3cc10426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 16)) *)
     0x4e9f2985;       (* arm_TRN1 Q5 Q12 Q31 32 128 *)
     0x4e8f2a0d;       (* arm_TRN1 Q13 Q16 Q15 32 128 *)
     0x4e9f699f;       (* arm_TRN2 Q31 Q12 Q31 32 128 *)
     0x4e8f6a0c;       (* arm_TRN2 Q12 Q16 Q15 32 128 *)
     0x4ecd28a3;       (* arm_TRN1 Q3 Q5 Q13 64 128 *)
     0x4ecd68ad;       (* arm_TRN2 Q13 Q5 Q13 64 128 *)
     0x4ecc2bf5;       (* arm_TRN1 Q21 Q31 Q12 64 128 *)
     0x4ecc6bea;       (* arm_TRN2 Q10 Q31 Q12 64 128 *)
     0x4e75846b;       (* arm_ADD_VEC Q11 Q3 Q21 16 128 *)
     0x4e6a85a8;       (* arm_ADD_VEC Q8 Q13 Q10 16 128 *)
     0x6e6a85ad;       (* arm_SUB_VEC Q13 Q13 Q10 16 128 *)
     0x6e758463;       (* arm_SUB_VEC Q3 Q3 Q21 16 128 *)
     0x4f57c175;       (* arm_SQDMULH_VEC Q21 Q11 (Q7 :> LANE_H 1) 16 128 *)
     0x4f56d9aa;       (* arm_SQRDMULH_VEC Q10 Q13 (Q6 :> LANE_H 5) 16 128 *)
     0x4f66806e;       (* arm_MUL_VEC Q14 Q3 (Q6 :> LANE_H 2) 16 128 *)
     0x4f4689af;       (* arm_MUL_VEC Q15 Q13 (Q6 :> LANE_H 4) 16 128 *)
     0x4f76d06d;       (* arm_SQRDMULH_VEC Q13 Q3 (Q6 :> LANE_H 3) 16 128 *)
     0x4f57c10c;       (* arm_SQDMULH_VEC Q12 Q8 (Q7 :> LANE_H 1) 16 128 *)
     0x4f1526a4;       (* arm_SRSHR_VEC Q4 Q21 11 16 128 *)
     0x6f47414f;       (* arm_MLS_VEC Q15 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4741ae;       (* arm_MLS_VEC Q14 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x6f47408b;       (* arm_MLS_VEC Q11 Q4 (Q7 :> LANE_H 0) 16 128 *)
     0x4f15258c;       (* arm_SRSHR_VEC Q12 Q12 11 16 128 *)
     0x6e6f85d0;       (* arm_SUB_VEC Q16 Q14 Q15 16 128 *)
     0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
     0x4f468211;       (* arm_MUL_VEC Q17 Q16 (Q6 :> LANE_H 0) 16 128 *)
     0x3dc00842;       (* arm_LDR Q2 X2 (Immediate_Offset (word 32)) *)
     0x3dc01461;       (* arm_LDR Q1 X3 (Immediate_Offset (word 80)) *)
     0x4f56d215;       (* arm_SQRDMULH_VEC Q21 Q16 (Q6 :> LANE_H 1) 16 128 *)
     0x6f474188;       (* arm_MLS_VEC Q8 Q12 (Q7 :> LANE_H 0) 16 128 *)
     0x3dc01073;       (* arm_LDR Q19 X3 (Immediate_Offset (word 64)) *)
     0x6f4742b1;       (* arm_MLS_VEC Q17 Q21 (Q7 :> LANE_H 0) 16 128 *)
     0x6e68857b;       (* arm_SUB_VEC Q27 Q11 Q8 16 128 *)
     0x4e812a77;       (* arm_TRN1 Q23 Q19 Q1 32 128 *)
     0x4e816a74;       (* arm_TRN2 Q20 Q19 Q1 32 128 *)
     0x3dc01872;       (* arm_LDR Q18 X3 (Immediate_Offset (word 96)) *)
     0x3dc01c7c;       (* arm_LDR Q28 X3 (Immediate_Offset (word 112)) *)
     0x4e6f85d6;       (* arm_ADD_VEC Q22 Q14 Q15 16 128 *)
     0x3d800c71;       (* arm_STR Q17 X3 (Immediate_Offset (word 48)) *)
     0x4e688563;       (* arm_ADD_VEC Q3 Q11 Q8 16 128 *)
     0x4e9c2a4f;       (* arm_TRN1 Q15 Q18 Q28 32 128 *)
     0x4e9c6a40;       (* arm_TRN2 Q0 Q18 Q28 32 128 *)
     0x4f56d369;       (* arm_SQRDMULH_VEC Q9 Q27 (Q6 :> LANE_H 1) 16 128 *)
     0x4ecf2aeb;       (* arm_TRN1 Q11 Q23 Q15 64 128 *)
     0x4ecf6af1;       (* arm_TRN2 Q17 Q23 Q15 64 128 *)
     0x4ec06a81;       (* arm_TRN2 Q1 Q20 Q0 64 128 *)
     0x4ec02a8e;       (* arm_TRN1 Q14 Q20 Q0 64 128 *)
     0x6e618625;       (* arm_SUB_VEC Q5 Q17 Q1 16 128 *)
     0x6e6e856d;       (* arm_SUB_VEC Q13 Q11 Q14 16 128 *)
     0x3dc01459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 80)) *)
     0x3dc00c58;       (* arm_LDR Q24 X2 (Immediate_Offset (word 48)) *)
     0x3dc01055;       (* arm_LDR Q21 X2 (Immediate_Offset (word 64)) *)
     0x4f468360;       (* arm_MUL_VEC Q0 Q27 (Q6 :> LANE_H 0) 16 128 *)
     0x6e79b4a6;       (* arm_SQRDMULH_VEC Q6 Q5 Q25 16 128 *)
     0x4e759cbc;       (* arm_MUL_VEC Q28 Q5 Q21 16 128 *)
     0x4e618628;       (* arm_ADD_VEC Q8 Q17 Q1 16 128 *)
     0x6e78b5a1;       (* arm_SQRDMULH_VEC Q1 Q13 Q24 16 128 *)
     0x4e629db0;       (* arm_MUL_VEC Q16 Q13 Q2 16 128 *)
     0x6f4740dc;       (* arm_MLS_VEC Q28 Q6 (Q7 :> LANE_H 0) 16 128 *)
     0x3dc00446;       (* arm_LDR Q6 X2 (Immediate_Offset (word 16)) *)
     0x4e6e8578;       (* arm_ADD_VEC Q24 Q11 Q14 16 128 *)
     0x6f474030;       (* arm_MLS_VEC Q16 Q1 (Q7 :> LANE_H 0) 16 128 *)
     0x4f57c2cc;       (* arm_SQDMULH_VEC Q12 Q22 (Q7 :> LANE_H 1) 16 128 *)
     0x3cc6044f;       (* arm_LDR Q15 X2 (Postimmediate_Offset (word 96)) *)
     0x6e7c861f;       (* arm_SUB_VEC Q31 Q16 Q28 16 128 *)
     0x6e68870d;       (* arm_SUB_VEC Q13 Q24 Q8 16 128 *)
     0x4e68871a;       (* arm_ADD_VEC Q26 Q24 Q8 16 128 *)
     0x6e66b7f4;       (* arm_SQRDMULH_VEC Q20 Q31 Q6 16 128 *)
     0x4e6f9da1;       (* arm_MUL_VEC Q1 Q13 Q15 16 128 *)
     0x4e6f9fee;       (* arm_MUL_VEC Q14 Q31 Q15 16 128 *)
     0x6e66b5af;       (* arm_SQRDMULH_VEC Q15 Q13 Q6 16 128 *)
     0x4e7c860d;       (* arm_ADD_VEC Q13 Q16 Q28 16 128 *)
     0x3cc10426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 16)) *)
     0x6f4741e1;       (* arm_MLS_VEC Q1 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x4f152592;       (* arm_SRSHR_VEC Q18 Q12 11 16 128 *)
     0x6f47428e;       (* arm_MLS_VEC Q14 Q20 (Q7 :> LANE_H 0) 16 128 *)
     0x4e8d2b55;       (* arm_TRN1 Q21 Q26 Q13 32 128 *)
     0x4e8d6b4b;       (* arm_TRN2 Q11 Q26 Q13 32 128 *)
     0x6f474256;       (* arm_MLS_VEC Q22 Q18 (Q7 :> LANE_H 0) 16 128 *)
     0x4e8e2831;       (* arm_TRN1 Q17 Q1 Q14 32 128 *)
     0x4e8e682d;       (* arm_TRN2 Q13 Q1 Q14 32 128 *)
     0x6f474120;       (* arm_MLS_VEC Q0 Q9 (Q7 :> LANE_H 0) 16 128 *)
     0x4ed16abf;       (* arm_TRN2 Q31 Q21 Q17 64 128 *)
     0x4ed12ab9;       (* arm_TRN1 Q25 Q21 Q17 64 128 *)
     0x4ecd2962;       (* arm_TRN1 Q2 Q11 Q13 64 128 *)
     0x4ecd6970;       (* arm_TRN2 Q16 Q11 Q13 64 128 *)
     0x4e62872b;       (* arm_ADD_VEC Q11 Q25 Q2 16 128 *)
     0x4e7087e8;       (* arm_ADD_VEC Q8 Q31 Q16 16 128 *)
     0x6e7087e1;       (* arm_SUB_VEC Q1 Q31 Q16 16 128 *)
     0x6e628731;       (* arm_SUB_VEC Q17 Q25 Q2 16 128 *)
     0x4f57c170;       (* arm_SQDMULH_VEC Q16 Q11 (Q7 :> LANE_H 1) 16 128 *)
     0x4f56d825;       (* arm_SQRDMULH_VEC Q5 Q1 (Q6 :> LANE_H 5) 16 128 *)
     0x4f46882f;       (* arm_MUL_VEC Q15 Q1 (Q6 :> LANE_H 4) 16 128 *)
     0x4f66822e;       (* arm_MUL_VEC Q14 Q17 (Q6 :> LANE_H 2) 16 128 *)
     0x4f76d229;       (* arm_SQRDMULH_VEC Q9 Q17 (Q6 :> LANE_H 3) 16 128 *)
     0x4f15261f;       (* arm_SRSHR_VEC Q31 Q16 11 16 128 *)
     0x6f4740af;       (* arm_MLS_VEC Q15 Q5 (Q7 :> LANE_H 0) 16 128 *)
     0x3d800860;       (* arm_STR Q0 X3 (Immediate_Offset (word 32)) *)
     0x6f47412e;       (* arm_MLS_VEC Q14 Q9 (Q7 :> LANE_H 0) 16 128 *)
     0x4f57c113;       (* arm_SQDMULH_VEC Q19 Q8 (Q7 :> LANE_H 1) 16 128 *)
     0x6f4743eb;       (* arm_MLS_VEC Q11 Q31 (Q7 :> LANE_H 0) 16 128 *)
     0x3d800476;       (* arm_STR Q22 X3 (Immediate_Offset (word 16)) *)
     0x6e6f85d0;       (* arm_SUB_VEC Q16 Q14 Q15 16 128 *)
     0x3c840463;       (* arm_STR Q3 X3 (Postimmediate_Offset (word 64)) *)
     0x4f15266c;       (* arm_SRSHR_VEC Q12 Q19 11 16 128 *)
     0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
     0xb5fff5e4;       (* arm_CBNZ X4 (word 2096828) *)
     0x6f474188;       (* arm_MLS_VEC Q8 Q12 (Q7 :> LANE_H 0) 16 128 *)
     0x4e6f85cc;       (* arm_ADD_VEC Q12 Q14 Q15 16 128 *)
     0x4f56d200;       (* arm_SQRDMULH_VEC Q0 Q16 (Q6 :> LANE_H 1) 16 128 *)
     0x4f468210;       (* arm_MUL_VEC Q16 Q16 (Q6 :> LANE_H 0) 16 128 *)
     0x6e68857a;       (* arm_SUB_VEC Q26 Q11 Q8 16 128 *)
     0x4e68856b;       (* arm_ADD_VEC Q11 Q11 Q8 16 128 *)
     0x4f57c197;       (* arm_SQDMULH_VEC Q23 Q12 (Q7 :> LANE_H 1) 16 128 *)
     0x4f56d34e;       (* arm_SQRDMULH_VEC Q14 Q26 (Q6 :> LANE_H 1) 16 128 *)
     0x4f46834f;       (* arm_MUL_VEC Q15 Q26 (Q6 :> LANE_H 0) 16 128 *)
     0x6f474010;       (* arm_MLS_VEC Q16 Q0 (Q7 :> LANE_H 0) 16 128 *)
     0x4f1526f6;       (* arm_SRSHR_VEC Q22 Q23 11 16 128 *)
     0x3c84046b;       (* arm_STR Q11 X3 (Postimmediate_Offset (word 64)) *)
     0x6f4741cf;       (* arm_MLS_VEC Q15 Q14 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4742cc;       (* arm_MLS_VEC Q12 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x3c9f0070;       (* arm_STR Q16 X3 (Immediate_Offset (word 18446744073709551600)) *)
     0x3c9e006f;       (* arm_STR Q15 X3 (Immediate_Offset (word 18446744073709551584)) *)
     0x3c9d006c;       (* arm_STR Q12 X3 (Immediate_Offset (word 18446744073709551568)) *)
     0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
     0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
     0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
     0x3dc0000f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 0)) *)
     0x3dc03009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 192)) *)
     0x3dc0200a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 128)) *)
     0x3dc01019;       (* arm_LDR Q25 X0 (Immediate_Offset (word 64)) *)
     0x6e69855f;       (* arm_SUB_VEC Q31 Q10 Q9 16 128 *)
     0x4e69854c;       (* arm_ADD_VEC Q12 Q10 Q9 16 128 *)
     0x4e7985f5;       (* arm_ADD_VEC Q21 Q15 Q25 16 128 *)
     0x3dc07012;       (* arm_LDR Q18 X0 (Immediate_Offset (word 448)) *)
     0x6e6c86ad;       (* arm_SUB_VEC Q13 Q21 Q12 16 128 *)
     0x3dc0601c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 384)) *)
     0x4f70d1a5;       (* arm_SQRDMULH_VEC Q5 Q13 (Q0 :> LANE_H 3) 16 128 *)
     0x3dc0500a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 320)) *)
     0x6e728786;       (* arm_SUB_VEC Q6 Q28 Q18 16 128 *)
     0x3dc04003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 256)) *)
     0x4f4188d3;       (* arm_MUL_VEC Q19 Q6 (Q1 :> LANE_H 4) 16 128 *)
     0x4f51d8d8;       (* arm_SQRDMULH_VEC Q24 Q6 (Q1 :> LANE_H 5) 16 128 *)
     0x6e7985e9;       (* arm_SUB_VEC Q9 Q15 Q25 16 128 *)
     0x4e6a847b;       (* arm_ADD_VEC Q27 Q3 Q10 16 128 *)
     0x6e6a8474;       (* arm_SUB_VEC Q20 Q3 Q10 16 128 *)
     0x4f608924;       (* arm_MUL_VEC Q4 Q9 (Q0 :> LANE_H 6) 16 128 *)
     0x4f70d939;       (* arm_SQRDMULH_VEC Q25 Q9 (Q0 :> LANE_H 7) 16 128 *)
     0x4e72878a;       (* arm_ADD_VEC Q10 Q28 Q18 16 128 *)
     0x4f71d28f;       (* arm_SQRDMULH_VEC Q15 Q20 (Q1 :> LANE_H 3) 16 128 *)
     0x4e6c86a6;       (* arm_ADD_VEC Q6 Q21 Q12 16 128 *)
     0x4e6a8769;       (* arm_ADD_VEC Q9 Q27 Q10 16 128 *)
     0x4f61828c;       (* arm_MUL_VEC Q12 Q20 (Q1 :> LANE_H 2) 16 128 *)
     0x6e6a876a;       (* arm_SUB_VEC Q10 Q27 Q10 16 128 *)
     0x6f474313;       (* arm_MLS_VEC Q19 Q24 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474324;       (* arm_MLS_VEC Q4 Q25 (Q7 :> LANE_H 0) 16 128 *)
     0x4f6081b0;       (* arm_MUL_VEC Q16 Q13 (Q0 :> LANE_H 2) 16 128 *)
     0x6f4741ec;       (* arm_MLS_VEC Q12 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x4f51d3f5;       (* arm_SQRDMULH_VEC Q21 Q31 (Q1 :> LANE_H 1) 16 128 *)
     0x4f4183ed;       (* arm_MUL_VEC Q13 Q31 (Q1 :> LANE_H 0) 16 128 *)
     0x6e6984db;       (* arm_SUB_VEC Q27 Q6 Q9 16 128 *)
     0x6e738583;       (* arm_SUB_VEC Q3 Q12 Q19 16 128 *)
     0x4e73859f;       (* arm_ADD_VEC Q31 Q12 Q19 16 128 *)
     0x6f4742ad;       (* arm_MLS_VEC Q13 Q21 (Q7 :> LANE_H 0) 16 128 *)
     0x4e6984c2;       (* arm_ADD_VEC Q2 Q6 Q9 16 128 *)
     0x4f40894b;       (* arm_MUL_VEC Q11 Q10 (Q0 :> LANE_H 4) 16 128 *)
     0x4f50d956;       (* arm_SQRDMULH_VEC Q22 Q10 (Q0 :> LANE_H 5) 16 128 *)
     0x4e6d8494;       (* arm_ADD_VEC Q20 Q4 Q13 16 128 *)
     0x6e6d848c;       (* arm_SUB_VEC Q12 Q4 Q13 16 128 *)
     0x3dc0640f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 400)) *)
     0x4e7f8699;       (* arm_ADD_VEC Q25 Q20 Q31 16 128 *)
     0x3dc0540d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 336)) *)
     0x4f678333;       (* arm_MUL_VEC Q19 Q25 (Q7 :> LANE_H 2) 16 128 *)
     0x4f77d33c;       (* arm_SQRDMULH_VEC Q28 Q25 (Q7 :> LANE_H 3) 16 128 *)
     0x3dc01419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 80)) *)
     0x4f70d184;       (* arm_SQRDMULH_VEC Q4 Q12 (Q0 :> LANE_H 3) 16 128 *)
     0x6f474393;       (* arm_MLS_VEC Q19 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x3dc07415;       (* arm_LDR Q21 X0 (Immediate_Offset (word 464)) *)
     0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
     0x6e7f8697;       (* arm_SUB_VEC Q23 Q20 Q31 16 128 *)
     0x3dc00418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 16)) *)
     0x3dc03409;       (* arm_LDR Q9 X0 (Immediate_Offset (word 208)) *)
     0x6e7585ff;       (* arm_SUB_VEC Q31 Q15 Q21 16 128 *)
     0x6e798714;       (* arm_SUB_VEC Q20 Q24 Q25 16 128 *)
     0x3dc0440e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 272)) *)
     0x4f608a88;       (* arm_MUL_VEC Q8 Q20 (Q0 :> LANE_H 6) 16 128 *)
     0x4f418bf1;       (* arm_MUL_VEC Q17 Q31 (Q1 :> LANE_H 4) 16 128 *)
     0x4f51dbfc;       (* arm_SQRDMULH_VEC Q28 Q31 (Q1 :> LANE_H 5) 16 128 *)
     0x4e6d85da;       (* arm_ADD_VEC Q26 Q14 Q13 16 128 *)
     0x6e6d85ca;       (* arm_SUB_VEC Q10 Q14 Q13 16 128 *)
     0x6f4742cb;       (* arm_MLS_VEC Q11 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x4f608192;       (* arm_MUL_VEC Q18 Q12 (Q0 :> LANE_H 2) 16 128 *)
     0x6f4740b0;       (* arm_MLS_VEC Q16 Q5 (Q7 :> LANE_H 0) 16 128 *)
     0x4f71db6c;       (* arm_SQRDMULH_VEC Q12 Q27 (Q1 :> LANE_H 7) 16 128 *)
     0x4f70da8e;       (* arm_SQRDMULH_VEC Q14 Q20 (Q0 :> LANE_H 7) 16 128 *)
     0x6f474092;       (* arm_MLS_VEC Q18 Q4 (Q7 :> LANE_H 0) 16 128 *)
     0x4f77d04d;       (* arm_SQRDMULH_VEC Q13 Q2 (Q7 :> LANE_H 3) 16 128 *)
     0x4e6b8605;       (* arm_ADD_VEC Q5 Q16 Q11 16 128 *)
     0x4f618b64;       (* arm_MUL_VEC Q4 Q27 (Q1 :> LANE_H 6) 16 128 *)
     0x4f678042;       (* arm_MUL_VEC Q2 Q2 (Q7 :> LANE_H 2) 16 128 *)
     0x4f50d874;       (* arm_SQRDMULH_VEC Q20 Q3 (Q0 :> LANE_H 5) 16 128 *)
     0x3dc02416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 144)) *)
     0x4f71d15b;       (* arm_SQRDMULH_VEC Q27 Q10 (Q1 :> LANE_H 3) 16 128 *)
     0x6f474184;       (* arm_MLS_VEC Q4 Q12 (Q7 :> LANE_H 0) 16 128 *)
     0x6e6986cc;       (* arm_SUB_VEC Q12 Q22 Q9 16 128 *)
     0x4e6986df;       (* arm_ADD_VEC Q31 Q22 Q9 16 128 *)
     0x4e7585f5;       (* arm_ADD_VEC Q21 Q15 Q21 16 128 *)
     0x4e798709;       (* arm_ADD_VEC Q9 Q24 Q25 16 128 *)
     0x4f51d18f;       (* arm_SQRDMULH_VEC Q15 Q12 (Q1 :> LANE_H 1) 16 128 *)
     0x4e758759;       (* arm_ADD_VEC Q25 Q26 Q21 16 128 *)
     0x4e7f8536;       (* arm_ADD_VEC Q22 Q9 Q31 16 128 *)
     0x4f618158;       (* arm_MUL_VEC Q24 Q10 (Q1 :> LANE_H 2) 16 128 *)
     0x6e75874a;       (* arm_SUB_VEC Q10 Q26 Q21 16 128 *)
     0x6e7f8529;       (* arm_SUB_VEC Q9 Q9 Q31 16 128 *)
     0x6f474391;       (* arm_MLS_VEC Q17 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x4f618afa;       (* arm_MUL_VEC Q26 Q23 (Q1 :> LANE_H 6) 16 128 *)
     0x6f4741c8;       (* arm_MLS_VEC Q8 Q14 (Q7 :> LANE_H 0) 16 128 *)
     0x4f71dafc;       (* arm_SQRDMULH_VEC Q28 Q23 (Q1 :> LANE_H 7) 16 128 *)
     0x6e6b860e;       (* arm_SUB_VEC Q14 Q16 Q11 16 128 *)
     0x4f608130;       (* arm_MUL_VEC Q16 Q9 (Q0 :> LANE_H 2) 16 128 *)
     0x4f408877;       (* arm_MUL_VEC Q23 Q3 (Q0 :> LANE_H 4) 16 128 *)
     0x3d804004;       (* arm_STR Q4 X0 (Immediate_Offset (word 256)) *)
     0x6f47439a;       (* arm_MLS_VEC Q26 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474378;       (* arm_MLS_VEC Q24 Q27 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474297;       (* arm_MLS_VEC Q23 Q20 (Q7 :> LANE_H 0) 16 128 *)
     0x4f50d1c6;       (* arm_SQRDMULH_VEC Q6 Q14 (Q0 :> LANE_H 1) 16 128 *)
     0x6e7986db;       (* arm_SUB_VEC Q27 Q22 Q25 16 128 *)
     0x3d80501a;       (* arm_STR Q26 X0 (Immediate_Offset (word 320)) *)
     0x6e77865c;       (* arm_SUB_VEC Q28 Q18 Q23 16 128 *)
     0x4e77865a;       (* arm_ADD_VEC Q26 Q18 Q23 16 128 *)
     0x4f4081d7;       (* arm_MUL_VEC Q23 Q14 (Q0 :> LANE_H 0) 16 128 *)
     0x4f50d384;       (* arm_SQRDMULH_VEC Q4 Q28 (Q0 :> LANE_H 1) 16 128 *)
     0x4f40838b;       (* arm_MUL_VEC Q11 Q28 (Q0 :> LANE_H 0) 16 128 *)
     0x6e718703;       (* arm_SUB_VEC Q3 Q24 Q17 16 128 *)
     0x4f418192;       (* arm_MUL_VEC Q18 Q12 (Q1 :> LANE_H 0) 16 128 *)
     0x6f4741a2;       (* arm_MLS_VEC Q2 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x6f47408b;       (* arm_MLS_VEC Q11 Q4 (Q7 :> LANE_H 0) 16 128 *)
     0x3dc07815;       (* arm_LDR Q21 X0 (Immediate_Offset (word 480)) *)
     0x6f4740d7;       (* arm_MLS_VEC Q23 Q6 (Q7 :> LANE_H 0) 16 128 *)
     0x3d80700b;       (* arm_STR Q11 X0 (Immediate_Offset (word 448)) *)
     0x6f4741f2;       (* arm_MLS_VEC Q18 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x3d802005;       (* arm_STR Q5 X0 (Immediate_Offset (word 128)) *)
     0x4e71871f;       (* arm_ADD_VEC Q31 Q24 Q17 16 128 *)
     0x4f70d125;       (* arm_SQRDMULH_VEC Q5 Q9 (Q0 :> LANE_H 3) 16 128 *)
     0x3c810402;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
     0x4e7986c2;       (* arm_ADD_VEC Q2 Q22 Q25 16 128 *)
     0x4e728514;       (* arm_ADD_VEC Q20 Q8 Q18 16 128 *)
     0x6e72850c;       (* arm_SUB_VEC Q12 Q8 Q18 16 128 *)
     0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
     0x4f40894b;       (* arm_MUL_VEC Q11 Q10 (Q0 :> LANE_H 4) 16 128 *)
     0x4f50d956;       (* arm_SQRDMULH_VEC Q22 Q10 (Q0 :> LANE_H 5) 16 128 *)
     0x3d802c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 176)) *)
     0x3dc0640f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 400)) *)
     0x3d800c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 48)) *)
     0x4e7f8689;       (* arm_ADD_VEC Q9 Q20 Q31 16 128 *)
     0x3dc0540d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 336)) *)
     0x4f678133;       (* arm_MUL_VEC Q19 Q9 (Q7 :> LANE_H 2) 16 128 *)
     0x4f77d132;       (* arm_SQRDMULH_VEC Q18 Q9 (Q7 :> LANE_H 3) 16 128 *)
     0x3dc01419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 80)) *)
     0x4f70d184;       (* arm_SQRDMULH_VEC Q4 Q12 (Q0 :> LANE_H 3) 16 128 *)
     0x6f474253;       (* arm_MLS_VEC Q19 Q18 (Q7 :> LANE_H 0) 16 128 *)
     0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
     0xb5fff5a4;       (* arm_CBNZ X4 (word 2096820) *)
     0x6f4742cb;       (* arm_MLS_VEC Q11 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x4e7585f2;       (* arm_ADD_VEC Q18 Q15 Q21 16 128 *)
     0x6e7585f5;       (* arm_SUB_VEC Q21 Q15 Q21 16 128 *)
     0x4f77d049;       (* arm_SQRDMULH_VEC Q9 Q2 (Q7 :> LANE_H 3) 16 128 *)
     0x4f678057;       (* arm_MUL_VEC Q23 Q2 (Q7 :> LANE_H 2) 16 128 *)
     0x6f4740b0;       (* arm_MLS_VEC Q16 Q5 (Q7 :> LANE_H 0) 16 128 *)
     0x6e7f8682;       (* arm_SUB_VEC Q2 Q20 Q31 16 128 *)
     0x4f60818f;       (* arm_MUL_VEC Q15 Q12 (Q0 :> LANE_H 2) 16 128 *)
     0x3d801013;       (* arm_STR Q19 X0 (Immediate_Offset (word 64)) *)
     0x3dc04406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 272)) *)
     0x4f71db6c;       (* arm_SQRDMULH_VEC Q12 Q27 (Q1 :> LANE_H 7) 16 128 *)
     0x4f618b73;       (* arm_MUL_VEC Q19 Q27 (Q1 :> LANE_H 6) 16 128 *)
     0x6e6d84d4;       (* arm_SUB_VEC Q20 Q6 Q13 16 128 *)
     0x4e6d84db;       (* arm_ADD_VEC Q27 Q6 Q13 16 128 *)
     0x6f47408f;       (* arm_MLS_VEC Q15 Q4 (Q7 :> LANE_H 0) 16 128 *)
     0x4e6b8605;       (* arm_ADD_VEC Q5 Q16 Q11 16 128 *)
     0x6e6b8610;       (* arm_SUB_VEC Q16 Q16 Q11 16 128 *)
     0x3dc0040d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 16)) *)
     0x4f408864;       (* arm_MUL_VEC Q4 Q3 (Q0 :> LANE_H 4) 16 128 *)
     0x4f50d87f;       (* arm_SQRDMULH_VEC Q31 Q3 (Q0 :> LANE_H 5) 16 128 *)
     0x4e7985bc;       (* arm_ADD_VEC Q28 Q13 Q25 16 128 *)
     0x6e7985a3;       (* arm_SUB_VEC Q3 Q13 Q25 16 128 *)
     0x6f474137;       (* arm_MLS_VEC Q23 Q9 (Q7 :> LANE_H 0) 16 128 *)
     0x4e72876d;       (* arm_ADD_VEC Q13 Q27 Q18 16 128 *)
     0x6e728766;       (* arm_SUB_VEC Q6 Q27 Q18 16 128 *)
     0x4f51dab6;       (* arm_SQRDMULH_VEC Q22 Q21 (Q1 :> LANE_H 5) 16 128 *)
     0x4f418abb;       (* arm_MUL_VEC Q27 Q21 (Q1 :> LANE_H 4) 16 128 *)
     0x4f71d858;       (* arm_SQRDMULH_VEC Q24 Q2 (Q1 :> LANE_H 7) 16 128 *)
     0x4f61885a;       (* arm_MUL_VEC Q26 Q2 (Q1 :> LANE_H 6) 16 128 *)
     0x6f474193;       (* arm_MLS_VEC Q19 Q12 (Q7 :> LANE_H 0) 16 128 *)
     0x4f618295;       (* arm_MUL_VEC Q21 Q20 (Q1 :> LANE_H 2) 16 128 *)
     0x4f71d28a;       (* arm_SQRDMULH_VEC Q10 Q20 (Q1 :> LANE_H 3) 16 128 *)
     0x3d802005;       (* arm_STR Q5 X0 (Immediate_Offset (word 128)) *)
     0x6f4743e4;       (* arm_MLS_VEC Q4 Q31 (Q7 :> LANE_H 0) 16 128 *)
     0x4f50d202;       (* arm_SQRDMULH_VEC Q2 Q16 (Q0 :> LANE_H 1) 16 128 *)
     0x4f408219;       (* arm_MUL_VEC Q25 Q16 (Q0 :> LANE_H 0) 16 128 *)
     0x6f474155;       (* arm_MLS_VEC Q21 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x6e6485e9;       (* arm_SUB_VEC Q9 Q15 Q4 16 128 *)
     0x4e6485f1;       (* arm_ADD_VEC Q17 Q15 Q4 16 128 *)
     0x4f60887f;       (* arm_MUL_VEC Q31 Q3 (Q0 :> LANE_H 6) 16 128 *)
     0x6f4742db;       (* arm_MLS_VEC Q27 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x4f50d8c8;       (* arm_SQRDMULH_VEC Q8 Q6 (Q0 :> LANE_H 5) 16 128 *)
     0x4f70d86e;       (* arm_SQRDMULH_VEC Q14 Q3 (Q0 :> LANE_H 7) 16 128 *)
     0x4f50d123;       (* arm_SQRDMULH_VEC Q3 Q9 (Q0 :> LANE_H 1) 16 128 *)
     0x6e7b86af;       (* arm_SUB_VEC Q15 Q21 Q27 16 128 *)
     0x4e7b86bb;       (* arm_ADD_VEC Q27 Q21 Q27 16 128 *)
     0x3dc03414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 208)) *)
     0x3dc02405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 144)) *)
     0x4f4088c4;       (* arm_MUL_VEC Q4 Q6 (Q0 :> LANE_H 4) 16 128 *)
     0x4f4089f2;       (* arm_MUL_VEC Q18 Q15 (Q0 :> LANE_H 4) 16 128 *)
     0x4e7484ab;       (* arm_ADD_VEC Q11 Q5 Q20 16 128 *)
     0x6f4741df;       (* arm_MLS_VEC Q31 Q14 (Q7 :> LANE_H 0) 16 128 *)
     0x3c810417;       (* arm_STR Q23 X0 (Postimmediate_Offset (word 16)) *)
     0x4e6b8790;       (* arm_ADD_VEC Q16 Q28 Q11 16 128 *)
     0x6e6b878a;       (* arm_SUB_VEC Q10 Q28 Q11 16 128 *)
     0x6f47431a;       (* arm_MLS_VEC Q26 Q24 (Q7 :> LANE_H 0) 16 128 *)
     0x6e6d861c;       (* arm_SUB_VEC Q28 Q16 Q13 16 128 *)
     0x4e6d8610;       (* arm_ADD_VEC Q16 Q16 Q13 16 128 *)
     0x4f608156;       (* arm_MUL_VEC Q22 Q10 (Q0 :> LANE_H 2) 16 128 *)
     0x3d803c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 240)) *)
     0x6f474104;       (* arm_MLS_VEC Q4 Q8 (Q7 :> LANE_H 0) 16 128 *)
     0x4f678213;       (* arm_MUL_VEC Q19 Q16 (Q7 :> LANE_H 2) 16 128 *)
     0x4f70d14a;       (* arm_SQRDMULH_VEC Q10 Q10 (Q0 :> LANE_H 3) 16 128 *)
     0x4f618b8c;       (* arm_MUL_VEC Q12 Q28 (Q1 :> LANE_H 6) 16 128 *)
     0x4f71db9c;       (* arm_SQRDMULH_VEC Q28 Q28 (Q1 :> LANE_H 7) 16 128 *)
     0x4f50d9ef;       (* arm_SQRDMULH_VEC Q15 Q15 (Q0 :> LANE_H 5) 16 128 *)
     0x6f474156;       (* arm_MLS_VEC Q22 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474059;       (* arm_MLS_VEC Q25 Q2 (Q7 :> LANE_H 0) 16 128 *)
     0x4f408122;       (* arm_MUL_VEC Q2 Q9 (Q0 :> LANE_H 0) 16 128 *)
     0x6f47438c;       (* arm_MLS_VEC Q12 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x4e6486d7;       (* arm_ADD_VEC Q23 Q22 Q4 16 128 *)
     0x4f77d20d;       (* arm_SQRDMULH_VEC Q13 Q16 (Q7 :> LANE_H 3) 16 128 *)
     0x6e7484a6;       (* arm_SUB_VEC Q6 Q5 Q20 16 128 *)
     0x3d802017;       (* arm_STR Q23 X0 (Immediate_Offset (word 128)) *)
     0x6f4741f2;       (* arm_MLS_VEC Q18 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4741b3;       (* arm_MLS_VEC Q19 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x3d802c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 176)) *)
     0x4f4180d0;       (* arm_MUL_VEC Q16 Q6 (Q1 :> LANE_H 0) 16 128 *)
     0x4f51d0ca;       (* arm_SQRDMULH_VEC Q10 Q6 (Q1 :> LANE_H 1) 16 128 *)
     0x3d80400c;       (* arm_STR Q12 X0 (Immediate_Offset (word 256)) *)
     0x6f474062;       (* arm_MLS_VEC Q2 Q3 (Q7 :> LANE_H 0) 16 128 *)
     0x3d805c19;       (* arm_STR Q25 X0 (Immediate_Offset (word 368)) *)
     0x6f474150;       (* arm_MLS_VEC Q16 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x3d804c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 304)) *)
     0x6e6486d8;       (* arm_SUB_VEC Q24 Q22 Q4 16 128 *)
     0x3d806c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 432)) *)
     0x4e7087f5;       (* arm_ADD_VEC Q21 Q31 Q16 16 128 *)
     0x6e7087ee;       (* arm_SUB_VEC Q14 Q31 Q16 16 128 *)
     0x4f408314;       (* arm_MUL_VEC Q20 Q24 (Q0 :> LANE_H 0) 16 128 *)
     0x4e7b86b1;       (* arm_ADD_VEC Q17 Q21 Q27 16 128 *)
     0x6e7b86a9;       (* arm_SUB_VEC Q9 Q21 Q27 16 128 *)
     0x4f70d1d7;       (* arm_SQRDMULH_VEC Q23 Q14 (Q0 :> LANE_H 3) 16 128 *)
     0x4f6081cf;       (* arm_MUL_VEC Q15 Q14 (Q0 :> LANE_H 2) 16 128 *)
     0x4f77d226;       (* arm_SQRDMULH_VEC Q6 Q17 (Q7 :> LANE_H 3) 16 128 *)
     0x4f67822d;       (* arm_MUL_VEC Q13 Q17 (Q7 :> LANE_H 2) 16 128 *)
     0x4f618935;       (* arm_MUL_VEC Q21 Q9 (Q1 :> LANE_H 6) 16 128 *)
     0x6f4742ef;       (* arm_MLS_VEC Q15 Q23 (Q7 :> LANE_H 0) 16 128 *)
     0x4f71d936;       (* arm_SQRDMULH_VEC Q22 Q9 (Q1 :> LANE_H 7) 16 128 *)
     0x6f4740cd;       (* arm_MLS_VEC Q13 Q6 (Q7 :> LANE_H 0) 16 128 *)
     0x4f50d31a;       (* arm_SQRDMULH_VEC Q26 Q24 (Q0 :> LANE_H 1) 16 128 *)
     0x3c810413;       (* arm_STR Q19 X0 (Postimmediate_Offset (word 16)) *)
     0x6f4742d5;       (* arm_MLS_VEC Q21 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x6e7285e3;       (* arm_SUB_VEC Q3 Q15 Q18 16 128 *)
     0x3d800c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 48)) *)
     0x6f474354;       (* arm_MLS_VEC Q20 Q26 (Q7 :> LANE_H 0) 16 128 *)
     0x4f50d068;       (* arm_SQRDMULH_VEC Q8 Q3 (Q0 :> LANE_H 1) 16 128 *)
     0x4f408062;       (* arm_MUL_VEC Q2 Q3 (Q0 :> LANE_H 0) 16 128 *)
     0x3d804c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 304)) *)
     0x4e7285f7;       (* arm_ADD_VEC Q23 Q15 Q18 16 128 *)
     0x3d805c14;       (* arm_STR Q20 X0 (Immediate_Offset (word 368)) *)
     0x6f474102;       (* arm_MLS_VEC Q2 Q8 (Q7 :> LANE_H 0) 16 128 *)
     0x3d802c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 176)) *)
     0x3d806c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 432)) *)
     0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
     0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
     0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
     0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
     0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
     0xd65f03c0        (* arm_RET X30 *)
   ];;

let MLKEM_INTT_EXEC = ARM_MK_EXEC_RULE mlkem_intt_mc;;

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
          [(word pc,0x6d0); (z_12345,160); (z_67,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                intt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x6b8) /\
                !i. i < 256
                    ==> let zi =
                         read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &26624)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
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

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_INTT_EXEC [n] THEN
            (SIMD_SIMPLIFY_TAC [barred; barmul]))
            (1--1001) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1001" THEN
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
 (`!a z_12345 z_67 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x6f8); (z_12345,160); (z_67,768)] /\
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
