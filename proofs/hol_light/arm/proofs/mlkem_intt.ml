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
  0x3dc00070;       (* arm_LDR Q16 X3 (Immediate_Offset (word 0)) *)
  0x3dc00473;       (* arm_LDR Q19 X3 (Immediate_Offset (word 16)) *)
  0x3dc00c75;       (* arm_LDR Q21 X3 (Immediate_Offset (word 48)) *)
  0x3dc01057;       (* arm_LDR Q23 X2 (Immediate_Offset (word 64)) *)
  0x3dc00866;       (* arm_LDR Q6 X3 (Immediate_Offset (word 32)) *)
  0x3dc01463;       (* arm_LDR Q3 X3 (Immediate_Offset (word 80)) *)
  0x3dc0085c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c5a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 48)) *)
  0x6e7eb600;       (* arm_SQRDMULH_VEC Q0 Q16 Q30 16 128 *)
  0x3cc60449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 96)) *)
  0x3dc01c68;       (* arm_LDR Q8 X3 (Immediate_Offset (word 112)) *)
  0x4e7d9e10;       (* arm_MUL_VEC Q16 Q16 Q29 16 128 *)
  0x3dc0186b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 96)) *)
  0x3cdf0054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e7eb678;       (* arm_SQRDMULH_VEC Q24 Q19 Q30 16 128 *)
  0x3cdb0059;       (* arm_LDR Q25 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4e7d9e76;       (* arm_MUL_VEC Q22 Q19 Q29 16 128 *)
  0x6e7eb6b3;       (* arm_SQRDMULH_VEC Q19 Q21 Q30 16 128 *)
  0x4e7d9ea1;       (* arm_MUL_VEC Q1 Q21 Q29 16 128 *)
  0x3dc01075;       (* arm_LDR Q21 X3 (Immediate_Offset (word 64)) *)
  0x4e7d9cc4;       (* arm_MUL_VEC Q4 Q6 Q29 16 128 *)
  0x6e7eb4cd;       (* arm_SQRDMULH_VEC Q13 Q6 Q30 16 128 *)
  0x6f474010;       (* arm_MLS_VEC Q16 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474316;       (* arm_MLS_VEC Q22 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741a4;       (* arm_MLS_VEC Q4 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474261;       (* arm_MLS_VEC Q1 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4e962a18;       (* arm_TRN1 Q24 Q16 Q22 32 128 *)
  0x6e7eb562;       (* arm_SQRDMULH_VEC Q2 Q11 Q30 16 128 *)
  0x4e966a0f;       (* arm_TRN2 Q15 Q16 Q22 32 128 *)
  0x4e7d9d72;       (* arm_MUL_VEC Q18 Q11 Q29 16 128 *)
  0x4e816896;       (* arm_TRN2 Q22 Q4 Q1 32 128 *)
  0x4e812885;       (* arm_TRN1 Q5 Q4 Q1 32 128 *)
  0x6e7eb50d;       (* arm_SQRDMULH_VEC Q13 Q8 Q30 16 128 *)
  0x4ed669fb;       (* arm_TRN2 Q27 Q15 Q22 64 128 *)
  0x6f474052;       (* arm_MLS_VEC Q18 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec56b0a;       (* arm_TRN2 Q10 Q24 Q5 64 128 *)
  0x4ed629ee;       (* arm_TRN1 Q14 Q15 Q22 64 128 *)
  0x6e7b8553;       (* arm_SUB_VEC Q19 Q10 Q27 16 128 *)
  0x6e7eb476;       (* arm_SQRDMULH_VEC Q22 Q3 Q30 16 128 *)
  0x4ec52b0c;       (* arm_TRN1 Q12 Q24 Q5 64 128 *)
  0x6e74b666;       (* arm_SQRDMULH_VEC Q6 Q19 Q20 16 128 *)
  0x4e7b8540;       (* arm_ADD_VEC Q0 Q10 Q27 16 128 *)
  0x6e6e859f;       (* arm_SUB_VEC Q31 Q12 Q14 16 128 *)
  0x4e779e70;       (* arm_MUL_VEC Q16 Q19 Q23 16 128 *)
  0x4e6e8581;       (* arm_ADD_VEC Q1 Q12 Q14 16 128 *)
  0x6e7ab7e5;       (* arm_SQRDMULH_VEC Q5 Q31 Q26 16 128 *)
  0x6e608424;       (* arm_SUB_VEC Q4 Q1 Q0 16 128 *)
  0x4e7c9ff8;       (* arm_MUL_VEC Q24 Q31 Q28 16 128 *)
  0x4e7d9d17;       (* arm_MUL_VEC Q23 Q8 Q29 16 128 *)
  0x6f4740b8;       (* arm_MLS_VEC Q24 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6e79b49c;       (* arm_SQRDMULH_VEC Q28 Q4 Q25 16 128 *)
  0x6f4740d0;       (* arm_MLS_VEC Q16 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4e699c91;       (* arm_MUL_VEC Q17 Q4 Q9 16 128 *)
  0x6e7eb6a4;       (* arm_SQRDMULH_VEC Q4 Q21 Q30 16 128 *)
  0x6e70871a;       (* arm_SUB_VEC Q26 Q24 Q16 16 128 *)
  0x6f474391;       (* arm_MLS_VEC Q17 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e79b746;       (* arm_SQRDMULH_VEC Q6 Q26 Q25 16 128 *)
  0x4e699f48;       (* arm_MUL_VEC Q8 Q26 Q9 16 128 *)
  0x6f4741b7;       (* arm_MLS_VEC Q23 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740c8;       (* arm_MLS_VEC Q8 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x3dc01054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 64)) *)
  0x3dc02c7c;       (* arm_LDR Q28 X3 (Immediate_Offset (word 176)) *)
  0x4e972a46;       (* arm_TRN1 Q6 Q18 Q23 32 128 *)
  0x4e7d9ea2;       (* arm_MUL_VEC Q2 Q21 Q29 16 128 *)
  0x4e976a45;       (* arm_TRN2 Q5 Q18 Q23 32 128 *)
  0x3cc1042c;       (* arm_LDR Q12 X1 (Postimmediate_Offset (word 16)) *)
  0x6f474082;       (* arm_MLS_VEC Q2 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4e70870d;       (* arm_ADD_VEC Q13 Q24 Q16 16 128 *)
  0x3dc0085b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 32)) *)
  0x4e882a33;       (* arm_TRN1 Q19 Q17 Q8 32 128 *)
  0x4e608424;       (* arm_ADD_VEC Q4 Q1 Q0 16 128 *)
  0x4e7d9f97;       (* arm_MUL_VEC Q23 Q28 Q29 16 128 *)
  0x3dc00c4f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 48)) *)
  0x4e886a29;       (* arm_TRN2 Q9 Q17 Q8 32 128 *)
  0x6e7eb791;       (* arm_SQRDMULH_VEC Q17 Q28 Q30 16 128 *)
  0x3dc02879;       (* arm_LDR Q25 X3 (Immediate_Offset (word 160)) *)
  0x4e8d6895;       (* arm_TRN2 Q21 Q4 Q13 32 128 *)
  0x4e8d2881;       (* arm_TRN1 Q1 Q4 Q13 32 128 *)
  0x4e7d9c7c;       (* arm_MUL_VEC Q28 Q3 Q29 16 128 *)
  0x4ec96ab8;       (* arm_TRN2 Q24 Q21 Q9 64 128 *)
  0x6f4742dc;       (* arm_MLS_VEC Q28 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed3682e;       (* arm_TRN2 Q14 Q1 Q19 64 128 *)
  0x6f474237;       (* arm_MLS_VEC Q23 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7885ca;       (* arm_ADD_VEC Q10 Q14 Q24 16 128 *)
  0x6e7885d0;       (* arm_SUB_VEC Q16 Q14 Q24 16 128 *)
  0x4e7d9f32;       (* arm_MUL_VEC Q18 Q25 Q29 16 128 *)
  0x4e9c2844;       (* arm_TRN1 Q4 Q2 Q28 32 128 *)
  0x4e9c6851;       (* arm_TRN2 Q17 Q2 Q28 32 128 *)
  0x6e7eb73f;       (* arm_SQRDMULH_VEC Q31 Q25 Q30 16 128 *)
  0x4ec66899;       (* arm_TRN2 Q25 Q4 Q6 64 128 *)
  0x3dc02463;       (* arm_LDR Q3 X3 (Immediate_Offset (word 144)) *)
  0x4ec6289c;       (* arm_TRN1 Q28 Q4 Q6 64 128 *)
  0x4f5cda0d;       (* arm_SQRDMULH_VEC Q13 Q16 (Q12 :> LANE_H 5) 16 128 *)
  0x4ec56a20;       (* arm_TRN2 Q0 Q17 Q5 64 128 *)
  0x4ec52a22;       (* arm_TRN1 Q2 Q17 Q5 64 128 *)
  0x4f57c156;       (* arm_SQDMULH_VEC Q22 Q10 (Q7 :> LANE_H 1) 16 128 *)
  0x4ec92ab8;       (* arm_TRN1 Q24 Q21 Q9 64 128 *)
  0x4ed32825;       (* arm_TRN1 Q5 Q1 Q19 64 128 *)
  0x4f4c8a09;       (* arm_MUL_VEC Q9 Q16 (Q12 :> LANE_H 4) 16 128 *)
  0x6f4743f2;       (* arm_MLS_VEC Q18 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6e62879f;       (* arm_SUB_VEC Q31 Q28 Q2 16 128 *)
  0x6f4741a9;       (* arm_MLS_VEC Q9 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7884ad;       (* arm_SUB_VEC Q13 Q5 Q24 16 128 *)
  0x4f1526da;       (* arm_SRSHR_VEC Q26 Q22 11 16 128 *)
  0x4f6c81b3;       (* arm_MUL_VEC Q19 Q13 (Q12 :> LANE_H 2) 16 128 *)
  0x6e608736;       (* arm_SUB_VEC Q22 Q25 Q0 16 128 *)
  0x4e608720;       (* arm_ADD_VEC Q0 Q25 Q0 16 128 *)
  0x4f7cd1b5;       (* arm_SQRDMULH_VEC Q21 Q13 (Q12 :> LANE_H 3) 16 128 *)
  0x4e7884ae;       (* arm_ADD_VEC Q14 Q5 Q24 16 128 *)
  0x6e6fb7e6;       (* arm_SQRDMULH_VEC Q6 Q31 Q15 16 128 *)
  0x4e749ed0;       (* arm_MUL_VEC Q16 Q22 Q20 16 128 *)
  0x6f4742b3;       (* arm_MLS_VEC Q19 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc02075;       (* arm_LDR Q21 X3 (Immediate_Offset (word 128)) *)
  0x4e7b9ff8;       (* arm_MUL_VEC Q24 Q31 Q27 16 128 *)
  0x4f57c1c4;       (* arm_SQDMULH_VEC Q4 Q14 (Q7 :> LANE_H 1) 16 128 *)
  0x6e698661;       (* arm_SUB_VEC Q1 Q19 Q9 16 128 *)
  0x6f4740d8;       (* arm_MLS_VEC Q24 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4e698668;       (* arm_ADD_VEC Q8 Q19 Q9 16 128 *)
  0x3dc01446;       (* arm_LDR Q6 X2 (Immediate_Offset (word 80)) *)
  0x6f47434a;       (* arm_MLS_VEC Q10 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f15248d;       (* arm_SRSHR_VEC Q13 Q4 11 16 128 *)
  0x4f57c113;       (* arm_SQDMULH_VEC Q19 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7eb6a4;       (* arm_SQRDMULH_VEC Q4 Q21 Q30 16 128 *)
  0x6f4741ae;       (* arm_MLS_VEC Q14 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f15267f;       (* arm_SRSHR_VEC Q31 Q19 11 16 128 *)
  0x4f5cd03b;       (* arm_SQRDMULH_VEC Q27 Q1 (Q12 :> LANE_H 1) 16 128 *)
  0x4f4c802b;       (* arm_MUL_VEC Q11 Q1 (Q12 :> LANE_H 0) 16 128 *)
  0x4e628781;       (* arm_ADD_VEC Q1 Q28 Q2 16 128 *)
  0x6e6a85d1;       (* arm_SUB_VEC Q17 Q14 Q10 16 128 *)
  0x3dc0045c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 16)) *)
  0x6e60842d;       (* arm_SUB_VEC Q13 Q1 Q0 16 128 *)
  0x6e66b6d3;       (* arm_SQRDMULH_VEC Q19 Q22 Q6 16 128 *)
  0x3cc60442;       (* arm_LDR Q2 X2 (Postimmediate_Offset (word 96)) *)
  0x6f47436b;       (* arm_MLS_VEC Q11 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4f5cd23b;       (* arm_SQRDMULH_VEC Q27 Q17 (Q12 :> LANE_H 1) 16 128 *)
  0x4f4c823a;       (* arm_MUL_VEC Q26 Q17 (Q12 :> LANE_H 0) 16 128 *)
  0x3d800c6b;       (* arm_STR Q11 X3 (Immediate_Offset (word 48)) *)
  0x6e7cb5ac;       (* arm_SQRDMULH_VEC Q12 Q13 Q28 16 128 *)
  0x6f474270;       (* arm_MLS_VEC Q16 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743e8;       (* arm_MLS_VEC Q8 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6a85cb;       (* arm_ADD_VEC Q11 Q14 Q10 16 128 *)
  0x6f47437a;       (* arm_MLS_VEC Q26 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e708719;       (* arm_SUB_VEC Q25 Q24 Q16 16 128 *)
  0x4e629db1;       (* arm_MUL_VEC Q17 Q13 Q2 16 128 *)
  0x3c84046b;       (* arm_STR Q11 X3 (Postimmediate_Offset (word 64)) *)
  0x3c9d0068;       (* arm_STR Q8 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x6e7cb72a;       (* arm_SQRDMULH_VEC Q10 Q25 Q28 16 128 *)
  0x6f474191;       (* arm_MLS_VEC Q17 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e629f28;       (* arm_MUL_VEC Q8 Q25 Q2 16 128 *)
  0x6e7eb476;       (* arm_SQRDMULH_VEC Q22 Q3 Q30 16 128 *)
  0x3c9e007a;       (* arm_STR Q26 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x6f474148;       (* arm_MLS_VEC Q8 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff464;       (* arm_CBNZ X4 (word 2096780) *)
  0x4e708719;       (* arm_ADD_VEC Q25 Q24 Q16 16 128 *)
  0x4e882a2c;       (* arm_TRN1 Q12 Q17 Q8 32 128 *)
  0x4e7d9c70;       (* arm_MUL_VEC Q16 Q3 Q29 16 128 *)
  0x4e60842d;       (* arm_ADD_VEC Q13 Q1 Q0 16 128 *)
  0x4e976a54;       (* arm_TRN2 Q20 Q18 Q23 32 128 *)
  0x3dc0084f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 32)) *)
  0x4e886a23;       (* arm_TRN2 Q3 Q17 Q8 32 128 *)
  0x4e9929ba;       (* arm_TRN1 Q26 Q13 Q25 32 128 *)
  0x4e9969ad;       (* arm_TRN2 Q13 Q13 Q25 32 128 *)
  0x4e7d9ebb;       (* arm_MUL_VEC Q27 Q21 Q29 16 128 *)
  0x3cc10420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 16)) *)
  0x4ecc6b4a;       (* arm_TRN2 Q10 Q26 Q12 64 128 *)
  0x4ec369a5;       (* arm_TRN2 Q5 Q13 Q3 64 128 *)
  0x6f47409b;       (* arm_MLS_VEC Q27 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4e972a53;       (* arm_TRN1 Q19 Q18 Q23 32 128 *)
  0x6e658555;       (* arm_SUB_VEC Q21 Q10 Q5 16 128 *)
  0x6f4742d0;       (* arm_MLS_VEC Q16 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc00c42;       (* arm_LDR Q2 X2 (Immediate_Offset (word 48)) *)
  0x4ecc2b51;       (* arm_TRN1 Q17 Q26 Q12 64 128 *)
  0x4f408aa6;       (* arm_MUL_VEC Q6 Q21 (Q0 :> LANE_H 4) 16 128 *)
  0x4ec329ad;       (* arm_TRN1 Q13 Q13 Q3 64 128 *)
  0x4e65854a;       (* arm_ADD_VEC Q10 Q10 Q5 16 128 *)
  0x3dc01049;       (* arm_LDR Q9 X2 (Immediate_Offset (word 64)) *)
  0x4f50dab6;       (* arm_SQRDMULH_VEC Q22 Q21 (Q0 :> LANE_H 5) 16 128 *)
  0x4e6d8632;       (* arm_ADD_VEC Q18 Q17 Q13 16 128 *)
  0x4e902b7f;       (* arm_TRN1 Q31 Q27 Q16 32 128 *)
  0x6e6d862d;       (* arm_SUB_VEC Q13 Q17 Q13 16 128 *)
  0x4f57c24c;       (* arm_SQDMULH_VEC Q12 Q18 (Q7 :> LANE_H 1) 16 128 *)
  0x4e906b68;       (* arm_TRN2 Q8 Q27 Q16 32 128 *)
  0x4ed32bee;       (* arm_TRN1 Q14 Q31 Q19 64 128 *)
  0x4f70d1b9;       (* arm_SQRDMULH_VEC Q25 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x4ed42903;       (* arm_TRN1 Q3 Q8 Q20 64 128 *)
  0x4f6081a1;       (* arm_MUL_VEC Q1 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x4ed36be4;       (* arm_TRN2 Q4 Q31 Q19 64 128 *)
  0x6e6385cd;       (* arm_SUB_VEC Q13 Q14 Q3 16 128 *)
  0x4f57c15a;       (* arm_SQDMULH_VEC Q26 Q10 (Q7 :> LANE_H 1) 16 128 *)
  0x4ed46908;       (* arm_TRN2 Q8 Q8 Q20 64 128 *)
  0x3dc01445;       (* arm_LDR Q5 X2 (Immediate_Offset (word 80)) *)
  0x6e62b5bf;       (* arm_SQRDMULH_VEC Q31 Q13 Q2 16 128 *)
  0x6e688493;       (* arm_SUB_VEC Q19 Q4 Q8 16 128 *)
  0x4e6f9db5;       (* arm_MUL_VEC Q21 Q13 Q15 16 128 *)
  0x6e65b665;       (* arm_SQRDMULH_VEC Q5 Q19 Q5 16 128 *)
  0x4e699e6d;       (* arm_MUL_VEC Q13 Q19 Q9 16 128 *)
  0x6f4743f5;       (* arm_MLS_VEC Q21 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6385c9;       (* arm_ADD_VEC Q9 Q14 Q3 16 128 *)
  0x4f152743;       (* arm_SRSHR_VEC Q3 Q26 11 16 128 *)
  0x6f4740ad;       (* arm_MLS_VEC Q13 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742c6;       (* arm_MLS_VEC Q6 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e68848e;       (* arm_ADD_VEC Q14 Q4 Q8 16 128 *)
  0x3cc60445;       (* arm_LDR Q5 X2 (Postimmediate_Offset (word 96)) *)
  0x6f47406a;       (* arm_MLS_VEC Q10 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdb0044;       (* arm_LDR Q4 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x6e6d86a3;       (* arm_SUB_VEC Q3 Q21 Q13 16 128 *)
  0x6f474321;       (* arm_MLS_VEC Q1 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x4f15259a;       (* arm_SRSHR_VEC Q26 Q12 11 16 128 *)
  0x6e6e8528;       (* arm_SUB_VEC Q8 Q9 Q14 16 128 *)
  0x4e659c79;       (* arm_MUL_VEC Q25 Q3 Q5 16 128 *)
  0x6e64b51f;       (* arm_SQRDMULH_VEC Q31 Q8 Q4 16 128 *)
  0x4e6d86bb;       (* arm_ADD_VEC Q27 Q21 Q13 16 128 *)
  0x6e64b46b;       (* arm_SQRDMULH_VEC Q11 Q3 Q4 16 128 *)
  0x6f474352;       (* arm_MLS_VEC Q18 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e66842f;       (* arm_SUB_VEC Q15 Q1 Q6 16 128 *)
  0x4f50d1f6;       (* arm_SQRDMULH_VEC Q22 Q15 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474179;       (* arm_MLS_VEC Q25 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e659d1a;       (* arm_MUL_VEC Q26 Q8 Q5 16 128 *)
  0x4e668422;       (* arm_ADD_VEC Q2 Q1 Q6 16 128 *)
  0x6f4743fa;       (* arm_MLS_VEC Q26 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6e8534;       (* arm_ADD_VEC Q20 Q9 Q14 16 128 *)
  0x6e6a8645;       (* arm_SUB_VEC Q5 Q18 Q10 16 128 *)
  0x4e9b6a84;       (* arm_TRN2 Q4 Q20 Q27 32 128 *)
  0x4f4081e6;       (* arm_MUL_VEC Q6 Q15 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6a864e;       (* arm_ADD_VEC Q14 Q18 Q10 16 128 *)
  0x4e9b2a83;       (* arm_TRN1 Q3 Q20 Q27 32 128 *)
  0x4f50d0a9;       (* arm_SQRDMULH_VEC Q9 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4e992b5f;       (* arm_TRN1 Q31 Q26 Q25 32 128 *)
  0x4f57c04c;       (* arm_SQDMULH_VEC Q12 Q2 (Q7 :> LANE_H 1) 16 128 *)
  0x4e996b5b;       (* arm_TRN2 Q27 Q26 Q25 32 128 *)
  0x4edf6868;       (* arm_TRN2 Q8 Q3 Q31 64 128 *)
  0x4edb688a;       (* arm_TRN2 Q10 Q4 Q27 64 128 *)
  0x6f4742c6;       (* arm_MLS_VEC Q6 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4edb288b;       (* arm_TRN1 Q11 Q4 Q27 64 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x4e6a850d;       (* arm_ADD_VEC Q13 Q8 Q10 16 128 *)
  0x4f4080a1;       (* arm_MUL_VEC Q1 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x4edf2875;       (* arm_TRN1 Q21 Q3 Q31 64 128 *)
  0x4f57c1b4;       (* arm_SQDMULH_VEC Q20 Q13 (Q7 :> LANE_H 1) 16 128 *)
  0x6e6a8505;       (* arm_SUB_VEC Q5 Q8 Q10 16 128 *)
  0x4e6b86b9;       (* arm_ADD_VEC Q25 Q21 Q11 16 128 *)
  0x4f4488bf;       (* arm_MUL_VEC Q31 Q5 (Q4 :> LANE_H 4) 16 128 *)
  0x6e6b86aa;       (* arm_SUB_VEC Q10 Q21 Q11 16 128 *)
  0x4f57c33b;       (* arm_SQDMULH_VEC Q27 Q25 (Q7 :> LANE_H 1) 16 128 *)
  0x4f54d8a8;       (* arm_SQRDMULH_VEC Q8 Q5 (Q4 :> LANE_H 5) 16 128 *)
  0x4f64814b;       (* arm_MUL_VEC Q11 Q10 (Q4 :> LANE_H 2) 16 128 *)
  0x4f152680;       (* arm_SRSHR_VEC Q0 Q20 11 16 128 *)
  0x4f152765;       (* arm_SRSHR_VEC Q5 Q27 11 16 128 *)
  0x4f74d15a;       (* arm_SQRDMULH_VEC Q26 Q10 (Q4 :> LANE_H 3) 16 128 *)
  0x6f47400d;       (* arm_MLS_VEC Q13 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740b9;       (* arm_MLS_VEC Q25 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47434b;       (* arm_MLS_VEC Q11 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f15259b;       (* arm_SRSHR_VEC Q27 Q12 11 16 128 *)
  0x6f47411f;       (* arm_MLS_VEC Q31 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d8720;       (* arm_SUB_VEC Q0 Q25 Q13 16 128 *)
  0x6f474121;       (* arm_MLS_VEC Q1 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f54d01a;       (* arm_SQRDMULH_VEC Q26 Q0 (Q4 :> LANE_H 1) 16 128 *)
  0x6e7f8568;       (* arm_SUB_VEC Q8 Q11 Q31 16 128 *)
  0x4e7f856c;       (* arm_ADD_VEC Q12 Q11 Q31 16 128 *)
  0x4f448014;       (* arm_MUL_VEC Q20 Q0 (Q4 :> LANE_H 0) 16 128 *)
  0x4f57c18b;       (* arm_SQDMULH_VEC Q11 Q12 (Q7 :> LANE_H 1) 16 128 *)
  0x4f54d11f;       (* arm_SQRDMULH_VEC Q31 Q8 (Q4 :> LANE_H 1) 16 128 *)
  0x6f474354;       (* arm_MLS_VEC Q20 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800c66;       (* arm_STR Q6 X3 (Immediate_Offset (word 48)) *)
  0x4e6d8726;       (* arm_ADD_VEC Q6 Q25 Q13 16 128 *)
  0x4f15256d;       (* arm_SRSHR_VEC Q13 Q11 11 16 128 *)
  0x4f448104;       (* arm_MUL_VEC Q4 Q8 (Q4 :> LANE_H 0) 16 128 *)
  0x6f4743e4;       (* arm_MLS_VEC Q4 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801874;       (* arm_STR Q20 X3 (Immediate_Offset (word 96)) *)
  0x6f4741ac;       (* arm_MLS_VEC Q12 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474362;       (* arm_MLS_VEC Q2 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3c84046e;       (* arm_STR Q14 X3 (Postimmediate_Offset (word 64)) *)
  0x3d80046c;       (* arm_STR Q12 X3 (Immediate_Offset (word 16)) *)
  0x3c840466;       (* arm_STR Q6 X3 (Postimmediate_Offset (word 64)) *)
  0x3c9a0061;       (* arm_STR Q1 X3 (Immediate_Offset (word 18446744073709551520)) *)
  0x3c990062;       (* arm_STR Q2 X3 (Immediate_Offset (word 18446744073709551504)) *)
  0x3c9f0064;       (* arm_STR Q4 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0301d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 192)) *)
  0x3dc02004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 128)) *)
  0x3dc0101c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 64)) *)
  0x3dc00010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 0)) *)
  0x3dc0400d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 256)) *)
  0x3dc0700c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 448)) *)
  0x3dc05012;       (* arm_LDR Q18 X0 (Immediate_Offset (word 320)) *)
  0x3dc06009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 384)) *)
  0x6e7d8495;       (* arm_SUB_VEC Q21 Q4 Q29 16 128 *)
  0x4e7d849e;       (* arm_ADD_VEC Q30 Q4 Q29 16 128 *)
  0x6e7c861a;       (* arm_SUB_VEC Q26 Q16 Q28 16 128 *)
  0x4e7c860e;       (* arm_ADD_VEC Q14 Q16 Q28 16 128 *)
  0x3dc00419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 16)) *)
  0x4f51d2a8;       (* arm_SQRDMULH_VEC Q8 Q21 (Q1 :> LANE_H 1) 16 128 *)
  0x4e7285b8;       (* arm_ADD_VEC Q24 Q13 Q18 16 128 *)
  0x3dc01411;       (* arm_LDR Q17 X0 (Immediate_Offset (word 80)) *)
  0x6e7285a4;       (* arm_SUB_VEC Q4 Q13 Q18 16 128 *)
  0x4f70db56;       (* arm_SQRDMULH_VEC Q22 Q26 (Q0 :> LANE_H 7) 16 128 *)
  0x4e6c8533;       (* arm_ADD_VEC Q19 Q9 Q12 16 128 *)
  0x3dc02405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 144)) *)
  0x6e6c852d;       (* arm_SUB_VEC Q13 Q9 Q12 16 128 *)
  0x4f4182ac;       (* arm_MUL_VEC Q12 Q21 (Q1 :> LANE_H 0) 16 128 *)
  0x6e7e85dd;       (* arm_SUB_VEC Q29 Q14 Q30 16 128 *)
  0x3dc0341b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 208)) *)
  0x4f608b50;       (* arm_MUL_VEC Q16 Q26 (Q0 :> LANE_H 6) 16 128 *)
  0x6e738712;       (* arm_SUB_VEC Q18 Q24 Q19 16 128 *)
  0x3dc04406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 272)) *)
  0x3dc05415;       (* arm_LDR Q21 X0 (Immediate_Offset (word 336)) *)
  0x4e73871a;       (* arm_ADD_VEC Q26 Q24 Q19 16 128 *)
  0x4f50da57;       (* arm_SQRDMULH_VEC Q23 Q18 (Q0 :> LANE_H 5) 16 128 *)
  0x4e7e85c3;       (* arm_ADD_VEC Q3 Q14 Q30 16 128 *)
  0x3dc06413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 400)) *)
  0x4f70d3bc;       (* arm_SQRDMULH_VEC Q28 Q29 (Q0 :> LANE_H 3) 16 128 *)
  0x4e71872a;       (* arm_ADD_VEC Q10 Q25 Q17 16 128 *)
  0x4e7b84bf;       (* arm_ADD_VEC Q31 Q5 Q27 16 128 *)
  0x3dc07418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 464)) *)
  0x4f408a4e;       (* arm_MUL_VEC Q14 Q18 (Q0 :> LANE_H 4) 16 128 *)
  0x6e7a846f;       (* arm_SUB_VEC Q15 Q3 Q26 16 128 *)
  0x6e7f855e;       (* arm_SUB_VEC Q30 Q10 Q31 16 128 *)
  0x4f6083bd;       (* arm_MUL_VEC Q29 Q29 (Q0 :> LANE_H 2) 16 128 *)
  0x6e7584c2;       (* arm_SUB_VEC Q2 Q6 Q21 16 128 *)
  0x4e7a847a;       (* arm_ADD_VEC Q26 Q3 Q26 16 128 *)
  0x6f47439d;       (* arm_MLS_VEC Q29 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e788669;       (* arm_SUB_VEC Q9 Q19 Q24 16 128 *)
  0x6e71872b;       (* arm_SUB_VEC Q11 Q25 Q17 16 128 *)
  0x3c81041a;       (* arm_STR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6f4742d0;       (* arm_MLS_VEC Q16 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47410c;       (* arm_MLS_VEC Q12 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742ee;       (* arm_MLS_VEC Q14 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d9ba;       (* arm_SQRDMULH_VEC Q26 Q13 (Q1 :> LANE_H 5) 16 128 *)
  0x6e6c8619;       (* arm_SUB_VEC Q25 Q16 Q12 16 128 *)
  0x4e6c8614;       (* arm_ADD_VEC Q20 Q16 Q12 16 128 *)
  0x4f618092;       (* arm_MUL_VEC Q18 Q4 (Q1 :> LANE_H 2) 16 128 *)
  0x6e6e87b6;       (* arm_SUB_VEC Q22 Q29 Q14 16 128 *)
  0x4f71d084;       (* arm_SQRDMULH_VEC Q4 Q4 (Q1 :> LANE_H 3) 16 128 *)
  0x4e6e87ac;       (* arm_ADD_VEC Q12 Q29 Q14 16 128 *)
  0x3d801c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 112)) *)
  0x4f70d323;       (* arm_SQRDMULH_VEC Q3 Q25 (Q0 :> LANE_H 3) 16 128 *)
  0x4f50d2cc;       (* arm_SQRDMULH_VEC Q12 Q22 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4189bd;       (* arm_MUL_VEC Q29 Q13 (Q1 :> LANE_H 4) 16 128 *)
  0x4f4082d7;       (* arm_MUL_VEC Q23 Q22 (Q0 :> LANE_H 0) 16 128 *)
  0x4f60832e;       (* arm_MUL_VEC Q14 Q25 (Q0 :> LANE_H 2) 16 128 *)
  0x6f47435d;       (* arm_MLS_VEC Q29 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474197;       (* arm_MLS_VEC Q23 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6083d0;       (* arm_MUL_VEC Q16 Q30 (Q0 :> LANE_H 2) 16 128 *)
  0x6f47406e;       (* arm_MLS_VEC Q14 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d1f6;       (* arm_SQRDMULH_VEC Q22 Q15 (Q0 :> LANE_H 1) 16 128 *)
  0x4f70d3de;       (* arm_SQRDMULH_VEC Q30 Q30 (Q0 :> LANE_H 3) 16 128 *)
  0x4f4081e8;       (* arm_MUL_VEC Q8 Q15 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474092;       (* arm_MLS_VEC Q18 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d04c;       (* arm_SQRDMULH_VEC Q12 Q2 (Q1 :> LANE_H 3) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6e7d8643;       (* arm_SUB_VEC Q3 Q18 Q29 16 128 *)
  0x4f70d97c;       (* arm_SQRDMULH_VEC Q28 Q11 (Q0 :> LANE_H 7) 16 128 *)
  0x4e7d864d;       (* arm_ADD_VEC Q13 Q18 Q29 16 128 *)
  0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
  0x3dc0140f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 80)) *)
  0x4f41893d;       (* arm_MUL_VEC Q29 Q9 (Q1 :> LANE_H 4) 16 128 *)
  0x4e7f854a;       (* arm_ADD_VEC Q10 Q10 Q31 16 128 *)
  0x6f4742c8;       (* arm_MLS_VEC Q8 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d8691;       (* arm_SUB_VEC Q17 Q20 Q13 16 128 *)
  0x4e78867f;       (* arm_ADD_VEC Q31 Q19 Q24 16 128 *)
  0x4f618052;       (* arm_MUL_VEC Q18 Q2 (Q1 :> LANE_H 2) 16 128 *)
  0x3dc07418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 464)) *)
  0x6e7b84a5;       (* arm_SUB_VEC Q5 Q5 Q27 16 128 *)
  0x6f4743d0;       (* arm_MLS_VEC Q16 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x3d803c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 240)) *)
  0x4e7584c8;       (* arm_ADD_VEC Q8 Q6 Q21 16 128 *)
  0x4e6d8686;       (* arm_ADD_VEC Q6 Q20 Q13 16 128 *)
  0x4f51d92d;       (* arm_SQRDMULH_VEC Q13 Q9 (Q1 :> LANE_H 5) 16 128 *)
  0x3dc00404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 16)) *)
  0x6e7f8514;       (* arm_SUB_VEC Q20 Q8 Q31 16 128 *)
  0x4f4180ba;       (* arm_MUL_VEC Q26 Q5 (Q1 :> LANE_H 0) 16 128 *)
  0x3dc06413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 400)) *)
  0x4e7f851f;       (* arm_ADD_VEC Q31 Q8 Q31 16 128 *)
  0x3dc05415;       (* arm_LDR Q21 X0 (Immediate_Offset (word 336)) *)
  0x4f50da96;       (* arm_SQRDMULH_VEC Q22 Q20 (Q0 :> LANE_H 5) 16 128 *)
  0x3d800c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 48)) *)
  0x4e7f8559;       (* arm_ADD_VEC Q25 Q10 Q31 16 128 *)
  0x3dc04406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 272)) *)
  0x4f408a97;       (* arm_MUL_VEC Q23 Q20 (Q0 :> LANE_H 4) 16 128 *)
  0x3c810419;       (* arm_STR Q25 X0 (Postimmediate_Offset (word 16)) *)
  0x6f474192;       (* arm_MLS_VEC Q18 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7584c2;       (* arm_SUB_VEC Q2 Q6 Q21 16 128 *)
  0x6f4742d7;       (* arm_MLS_VEC Q23 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f608968;       (* arm_MUL_VEC Q8 Q11 (Q0 :> LANE_H 6) 16 128 *)
  0x6f474388;       (* arm_MLS_VEC Q8 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4e778616;       (* arm_ADD_VEC Q22 Q16 Q23 16 128 *)
  0x6e77860b;       (* arm_SUB_VEC Q11 Q16 Q23 16 128 *)
  0x4f50d870;       (* arm_SQRDMULH_VEC Q16 Q3 (Q0 :> LANE_H 5) 16 128 *)
  0x3d801c16;       (* arm_STR Q22 X0 (Immediate_Offset (word 112)) *)
  0x4f51d0bb;       (* arm_SQRDMULH_VEC Q27 Q5 (Q1 :> LANE_H 1) 16 128 *)
  0x6f4741bd;       (* arm_MLS_VEC Q29 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408877;       (* arm_MUL_VEC Q23 Q3 (Q0 :> LANE_H 4) 16 128 *)
  0x3dc02005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 128)) *)
  0x6e7f855c;       (* arm_SUB_VEC Q28 Q10 Q31 16 128 *)
  0x6f47437a;       (* arm_MLS_VEC Q26 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d396;       (* arm_SQRDMULH_VEC Q22 Q28 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc0301b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 192)) *)
  0x6f474217;       (* arm_MLS_VEC Q23 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a850a;       (* arm_SUB_VEC Q10 Q8 Q26 16 128 *)
  0x4e7a8514;       (* arm_ADD_VEC Q20 Q8 Q26 16 128 *)
  0x4f40823a;       (* arm_MUL_VEC Q26 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x4f70d149;       (* arm_SQRDMULH_VEC Q9 Q10 (Q0 :> LANE_H 3) 16 128 *)
  0x4e7b84bf;       (* arm_ADD_VEC Q31 Q5 Q27 16 128 *)
  0x4f50d23e;       (* arm_SQRDMULH_VEC Q30 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x6e7785d0;       (* arm_SUB_VEC Q16 Q14 Q23 16 128 *)
  0x4e7785d1;       (* arm_ADD_VEC Q17 Q14 Q23 16 128 *)
  0x4f60814e;       (* arm_MUL_VEC Q14 Q10 (Q0 :> LANE_H 2) 16 128 *)
  0x3d802811;       (* arm_STR Q17 X0 (Immediate_Offset (word 160)) *)
  0x6f47412e;       (* arm_MLS_VEC Q14 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d209;       (* arm_SQRDMULH_VEC Q9 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d16a;       (* arm_SQRDMULH_VEC Q10 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4743da;       (* arm_MLS_VEC Q26 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d04c;       (* arm_SQRDMULH_VEC Q12 Q2 (Q1 :> LANE_H 3) 16 128 *)
  0x4f408177;       (* arm_MUL_VEC Q23 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0x6e6f848b;       (* arm_SUB_VEC Q11 Q4 Q15 16 128 *)
  0x3d80481a;       (* arm_STR Q26 X0 (Immediate_Offset (word 288)) *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6f848a;       (* arm_ADD_VEC Q10 Q4 Q15 16 128 *)
  0x4f40821a;       (* arm_MUL_VEC Q26 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7f855e;       (* arm_SUB_VEC Q30 Q10 Q31 16 128 *)
  0x4f6083d0;       (* arm_MUL_VEC Q16 Q30 (Q0 :> LANE_H 2) 16 128 *)
  0x6f47413a;       (* arm_MLS_VEC Q26 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6e788669;       (* arm_SUB_VEC Q9 Q19 Q24 16 128 *)
  0x4f408388;       (* arm_MUL_VEC Q8 Q28 (Q0 :> LANE_H 0) 16 128 *)
  0x4f70d3de;       (* arm_SQRDMULH_VEC Q30 Q30 (Q0 :> LANE_H 3) 16 128 *)
  0x3d80681a;       (* arm_STR Q26 X0 (Immediate_Offset (word 416)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6f4743d0;       (* arm_MLS_VEC Q16 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4e78866f;       (* arm_ADD_VEC Q15 Q19 Q24 16 128 *)
  0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
  0x4e7584cd;       (* arm_ADD_VEC Q13 Q6 Q21 16 128 *)
  0x4f70d979;       (* arm_SQRDMULH_VEC Q25 Q11 (Q0 :> LANE_H 7) 16 128 *)
  0x4e7f8543;       (* arm_ADD_VEC Q3 Q10 Q31 16 128 *)
  0x6e6f85b5;       (* arm_SUB_VEC Q21 Q13 Q15 16 128 *)
  0x4f608978;       (* arm_MUL_VEC Q24 Q11 (Q0 :> LANE_H 6) 16 128 *)
  0x6e7b84b1;       (* arm_SUB_VEC Q17 Q5 Q27 16 128 *)
  0x6e7d865c;       (* arm_SUB_VEC Q28 Q18 Q29 16 128 *)
  0x4f418933;       (* arm_MUL_VEC Q19 Q9 (Q1 :> LANE_H 4) 16 128 *)
  0x4e6f85b7;       (* arm_ADD_VEC Q23 Q13 Q15 16 128 *)
  0x4e7d865b;       (* arm_ADD_VEC Q27 Q18 Q29 16 128 *)
  0x4f618046;       (* arm_MUL_VEC Q6 Q2 (Q1 :> LANE_H 2) 16 128 *)
  0x6f474186;       (* arm_MLS_VEC Q6 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474338;       (* arm_MLS_VEC Q24 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742c8;       (* arm_MLS_VEC Q8 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50dabf;       (* arm_SQRDMULH_VEC Q31 Q21 (Q0 :> LANE_H 5) 16 128 *)
  0x4e778476;       (* arm_ADD_VEC Q22 Q3 Q23 16 128 *)
  0x4f51d224;       (* arm_SQRDMULH_VEC Q4 Q17 (Q1 :> LANE_H 1) 16 128 *)
  0x3d803c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 240)) *)
  0x3c810416;       (* arm_STR Q22 X0 (Postimmediate_Offset (word 16)) *)
  0x4f418228;       (* arm_MUL_VEC Q8 Q17 (Q1 :> LANE_H 0) 16 128 *)
  0x4f51d93a;       (* arm_SQRDMULH_VEC Q26 Q9 (Q1 :> LANE_H 5) 16 128 *)
  0x6f474088;       (* arm_MLS_VEC Q8 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7b8684;       (* arm_SUB_VEC Q4 Q20 Q27 16 128 *)
  0x6e77846a;       (* arm_SUB_VEC Q10 Q3 Q23 16 128 *)
  0x4f50d09e;       (* arm_SQRDMULH_VEC Q30 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d14b;       (* arm_SQRDMULH_VEC Q11 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x6e68870f;       (* arm_SUB_VEC Q15 Q24 Q8 16 128 *)
  0x6f474353;       (* arm_MLS_VEC Q19 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50db9a;       (* arm_SQRDMULH_VEC Q26 Q28 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408092;       (* arm_MUL_VEC Q18 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7384cc;       (* arm_ADD_VEC Q12 Q6 Q19 16 128 *)
  0x6e7384c3;       (* arm_SUB_VEC Q3 Q6 Q19 16 128 *)
  0x6f4743d2;       (* arm_MLS_VEC Q18 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408abe;       (* arm_MUL_VEC Q30 Q21 (Q0 :> LANE_H 4) 16 128 *)
  0x6f4743fe;       (* arm_MLS_VEC Q30 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804812;       (* arm_STR Q18 X0 (Immediate_Offset (word 288)) *)
  0x4f408b95;       (* arm_MUL_VEC Q21 Q28 (Q0 :> LANE_H 4) 16 128 *)
  0x4f70d1e2;       (* arm_SQRDMULH_VEC Q2 Q15 (Q0 :> LANE_H 3) 16 128 *)
  0x4e7e8613;       (* arm_ADD_VEC Q19 Q16 Q30 16 128 *)
  0x6f474355;       (* arm_MLS_VEC Q21 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7e8605;       (* arm_SUB_VEC Q5 Q16 Q30 16 128 *)
  0x4f408157;       (* arm_MUL_VEC Q23 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d0aa;       (* arm_SQRDMULH_VEC Q10 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4e7b8690;       (* arm_ADD_VEC Q16 Q20 Q27 16 128 *)
  0x4e688714;       (* arm_ADD_VEC Q20 Q24 Q8 16 128 *)
  0x4f4080a6;       (* arm_MUL_VEC Q6 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7585c5;       (* arm_SUB_VEC Q5 Q14 Q21 16 128 *)
  0x3d800810;       (* arm_STR Q16 X0 (Immediate_Offset (word 32)) *)
  0x6e6c869a;       (* arm_SUB_VEC Q26 Q20 Q12 16 128 *)
  0x4e6c8688;       (* arm_ADD_VEC Q8 Q20 Q12 16 128 *)
  0x4f50d86c;       (* arm_SQRDMULH_VEC Q12 Q3 (Q0 :> LANE_H 5) 16 128 *)
  0x3d801c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 112)) *)
  0x3d800c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 48)) *)
  0x4f50d0a9;       (* arm_SQRDMULH_VEC Q9 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4e7585c4;       (* arm_ADD_VEC Q4 Q14 Q21 16 128 *)
  0x6f474146;       (* arm_MLS_VEC Q6 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3d802804;       (* arm_STR Q4 X0 (Immediate_Offset (word 160)) *)
  0x4f40886a;       (* arm_MUL_VEC Q10 Q3 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47418a;       (* arm_MLS_VEC Q10 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x3d805c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 368)) *)
  0x4f6081e6;       (* arm_MUL_VEC Q6 Q15 (Q0 :> LANE_H 2) 16 128 *)
  0x6f474046;       (* arm_MLS_VEC Q6 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d34e;       (* arm_SQRDMULH_VEC Q14 Q26 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474177;       (* arm_MLS_VEC Q23 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6a84cd;       (* arm_SUB_VEC Q13 Q6 Q10 16 128 *)
  0x4f40834f;       (* arm_MUL_VEC Q15 Q26 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6a84df;       (* arm_ADD_VEC Q31 Q6 Q10 16 128 *)
  0x6f4741cf;       (* arm_MLS_VEC Q15 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x3d802c1f;       (* arm_STR Q31 X0 (Immediate_Offset (word 176)) *)
  0x4f50d1a8;       (* arm_SQRDMULH_VEC Q8 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x3d803c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 240)) *)
  0x4f4081ab;       (* arm_MUL_VEC Q11 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x4f4080b5;       (* arm_MUL_VEC Q21 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x3d804c0f;       (* arm_STR Q15 X0 (Immediate_Offset (word 304)) *)
  0x6f47410b;       (* arm_MLS_VEC Q11 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474135;       (* arm_MLS_VEC Q21 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x3d806c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 432)) *)
  0x3d806815;       (* arm_STR Q21 X0 (Immediate_Offset (word 416)) *)
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
