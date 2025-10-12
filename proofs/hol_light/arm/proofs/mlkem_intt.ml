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
  0x3dc0086d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c68;       (* arm_LDR Q8 X3 (Immediate_Offset (word 48)) *)
  0x3dc00066;       (* arm_LDR Q6 X3 (Immediate_Offset (word 0)) *)
  0x3dc00470;       (* arm_LDR Q16 X3 (Immediate_Offset (word 16)) *)
  0x3dc01464;       (* arm_LDR Q4 X3 (Immediate_Offset (word 80)) *)
  0x3dc0106b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 64)) *)
  0x3dc01c63;       (* arm_LDR Q3 X3 (Immediate_Offset (word 112)) *)
  0x4e8829b7;       (* arm_TRN1 Q23 Q13 Q8 32 128 *)
  0x3dc01860;       (* arm_LDR Q0 X3 (Immediate_Offset (word 96)) *)
  0x4e9068d3;       (* arm_TRN2 Q19 Q6 Q16 32 128 *)
  0x4e8869b5;       (* arm_TRN2 Q21 Q13 Q8 32 128 *)
  0x4e9028c6;       (* arm_TRN1 Q6 Q6 Q16 32 128 *)
  0x3dc00858;       (* arm_LDR Q24 X2 (Immediate_Offset (word 32)) *)
  0x4ed52a6a;       (* arm_TRN1 Q10 Q19 Q21 64 128 *)
  0x3cc60450;       (* arm_LDR Q16 X2 (Postimmediate_Offset (word 96)) *)
  0x4ed728c5;       (* arm_TRN1 Q5 Q6 Q23 64 128 *)
  0x4e83281c;       (* arm_TRN1 Q28 Q0 Q3 32 128 *)
  0x4ed768d2;       (* arm_TRN2 Q18 Q6 Q23 64 128 *)
  0x4e7d9d5f;       (* arm_MUL_VEC Q31 Q10 Q29 16 128 *)
  0x4e83680d;       (* arm_TRN2 Q13 Q0 Q3 32 128 *)
  0x3cdb004e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x6e7eb65a;       (* arm_SQRDMULH_VEC Q26 Q18 Q30 16 128 *)
  0x3cde0054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e7d9e51;       (* arm_MUL_VEC Q17 Q18 Q29 16 128 *)
  0x4ed56a72;       (* arm_TRN2 Q18 Q19 Q21 64 128 *)
  0x4e7d9e49;       (* arm_MUL_VEC Q9 Q18 Q29 16 128 *)
  0x4e84296c;       (* arm_TRN1 Q12 Q11 Q4 32 128 *)
  0x6e7eb656;       (* arm_SQRDMULH_VEC Q22 Q18 Q30 16 128 *)
  0x6e7eb543;       (* arm_SQRDMULH_VEC Q3 Q10 Q30 16 128 *)
  0x6e7eb4b9;       (* arm_SQRDMULH_VEC Q25 Q5 Q30 16 128 *)
  0x6f4742c9;       (* arm_MLS_VEC Q9 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474351;       (* arm_MLS_VEC Q17 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4e84697a;       (* arm_TRN2 Q26 Q11 Q4 32 128 *)
  0x4e7d9ca8;       (* arm_MUL_VEC Q8 Q5 Q29 16 128 *)
  0x4ecd2b4a;       (* arm_TRN1 Q10 Q26 Q13 64 128 *)
  0x3cdf004b;       (* arm_LDR Q11 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f47407f;       (* arm_MLS_VEC Q31 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4edc2986;       (* arm_TRN1 Q6 Q12 Q28 64 128 *)
  0x4ecd6b43;       (* arm_TRN2 Q3 Q26 Q13 64 128 *)
  0x3cdd0044;       (* arm_LDR Q4 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f474328;       (* arm_MLS_VEC Q8 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6e698633;       (* arm_SUB_VEC Q19 Q17 Q9 16 128 *)
  0x4edc698d;       (* arm_TRN2 Q13 Q12 Q28 64 128 *)
  0x6e7eb461;       (* arm_SQRDMULH_VEC Q1 Q3 Q30 16 128 *)
  0x4e698629;       (* arm_ADD_VEC Q9 Q17 Q9 16 128 *)
  0x4e749e72;       (* arm_MUL_VEC Q18 Q19 Q20 16 128 *)
  0x4e7f851c;       (* arm_ADD_VEC Q28 Q8 Q31 16 128 *)
  0x6e6bb674;       (* arm_SQRDMULH_VEC Q20 Q19 Q11 16 128 *)
  0x6e69878c;       (* arm_SUB_VEC Q12 Q28 Q9 16 128 *)
  0x6e7f8517;       (* arm_SUB_VEC Q23 Q8 Q31 16 128 *)
  0x6e7eb5ab;       (* arm_SQRDMULH_VEC Q11 Q13 Q30 16 128 *)
  0x6e64b6e5;       (* arm_SQRDMULH_VEC Q5 Q23 Q4 16 128 *)
  0x4e789ee0;       (* arm_MUL_VEC Q0 Q23 Q24 16 128 *)
  0x4e7d9da2;       (* arm_MUL_VEC Q2 Q13 Q29 16 128 *)
  0x6f4740a0;       (* arm_MLS_VEC Q0 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x4e698798;       (* arm_ADD_VEC Q24 Q28 Q9 16 128 *)
  0x6f474292;       (* arm_MLS_VEC Q18 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7eb4cf;       (* arm_SQRDMULH_VEC Q15 Q6 Q30 16 128 *)
  0x6e6eb599;       (* arm_SQRDMULH_VEC Q25 Q12 Q14 16 128 *)
  0x4e709d95;       (* arm_MUL_VEC Q21 Q12 Q16 16 128 *)
  0x6e728417;       (* arm_SUB_VEC Q23 Q0 Q18 16 128 *)
  0x6e6eb6e8;       (* arm_SQRDMULH_VEC Q8 Q23 Q14 16 128 *)
  0x4e709ef7;       (* arm_MUL_VEC Q23 Q23 Q16 16 128 *)
  0x6f474335;       (* arm_MLS_VEC Q21 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474117;       (* arm_MLS_VEC Q23 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7d9c6e;       (* arm_MUL_VEC Q14 Q3 Q29 16 128 *)
  0x4e728403;       (* arm_ADD_VEC Q3 Q0 Q18 16 128 *)
  0x4e836b04;       (* arm_TRN2 Q4 Q24 Q3 32 128 *)
  0x6f47402e;       (* arm_MLS_VEC Q14 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4e832b09;       (* arm_TRN1 Q9 Q24 Q3 32 128 *)
  0x4e976aac;       (* arm_TRN2 Q12 Q21 Q23 32 128 *)
  0x6f474162;       (* arm_MLS_VEC Q2 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e972abc;       (* arm_TRN1 Q28 Q21 Q23 32 128 *)
  0x3cc1042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 16)) *)
  0x4e7d9d5f;       (* arm_MUL_VEC Q31 Q10 Q29 16 128 *)
  0x4ecc2899;       (* arm_TRN1 Q25 Q4 Q12 64 128 *)
  0x4edc2934;       (* arm_TRN1 Q20 Q9 Q28 64 128 *)
  0x3dc01457;       (* arm_LDR Q23 X2 (Immediate_Offset (word 80)) *)
  0x4ecc688d;       (* arm_TRN2 Q13 Q4 Q12 64 128 *)
  0x6e7eb555;       (* arm_SQRDMULH_VEC Q21 Q10 Q30 16 128 *)
  0x4edc6924;       (* arm_TRN2 Q4 Q9 Q28 64 128 *)
  0x3dc01049;       (* arm_LDR Q9 X2 (Immediate_Offset (word 64)) *)
  0x4e7d9cdb;       (* arm_MUL_VEC Q27 Q6 Q29 16 128 *)
  0x4e79869a;       (* arm_ADD_VEC Q26 Q20 Q25 16 128 *)
  0x6e6e8443;       (* arm_SUB_VEC Q3 Q2 Q14 16 128 *)
  0x4f57c34c;       (* arm_SQDMULH_VEC Q12 Q26 (Q7 :> LANE_H 1) 16 128 *)
  0x4e6d8485;       (* arm_ADD_VEC Q5 Q4 Q13 16 128 *)
  0x6e6d8488;       (* arm_SUB_VEC Q8 Q4 Q13 16 128 *)
  0x4e6e844a;       (* arm_ADD_VEC Q10 Q2 Q14 16 128 *)
  0x4f57c0a6;       (* arm_SQDMULH_VEC Q6 Q5 (Q7 :> LANE_H 1) 16 128 *)
  0x3dc00442;       (* arm_LDR Q2 X2 (Immediate_Offset (word 16)) *)
  0x6f4741fb;       (* arm_MLS_VEC Q27 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0084f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 32)) *)
  0x4f15258c;       (* arm_SRSHR_VEC Q12 Q12 11 16 128 *)
  0x6f4742bf;       (* arm_MLS_VEC Q31 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4f1524c6;       (* arm_SRSHR_VEC Q6 Q6 11 16 128 *)
  0x6e77b477;       (* arm_SQRDMULH_VEC Q23 Q3 Q23 16 128 *)
  0x6f47419a;       (* arm_MLS_VEC Q26 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7f8775;       (* arm_ADD_VEC Q21 Q27 Q31 16 128 *)
  0x6f4740c5;       (* arm_MLS_VEC Q5 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7f8766;       (* arm_SUB_VEC Q6 Q27 Q31 16 128 *)
  0x6e6a86ae;       (* arm_SUB_VEC Q14 Q21 Q10 16 128 *)
  0x3cc6045b;       (* arm_LDR Q27 X2 (Postimmediate_Offset (word 96)) *)
  0x4e699c63;       (* arm_MUL_VEC Q3 Q3 Q9 16 128 *)
  0x6f4742e3;       (* arm_MLS_VEC Q3 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdd004d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6e65874c;       (* arm_SUB_VEC Q12 Q26 Q5 16 128 *)
  0x4e658745;       (* arm_ADD_VEC Q5 Q26 Q5 16 128 *)
  0x4f5bd91f;       (* arm_SQRDMULH_VEC Q31 Q8 (Q11 :> LANE_H 5) 16 128 *)
  0x4f5bd193;       (* arm_SQRDMULH_VEC Q19 Q12 (Q11 :> LANE_H 1) 16 128 *)
  0x4f4b8198;       (* arm_MUL_VEC Q24 Q12 (Q11 :> LANE_H 0) 16 128 *)
  0x6e6db4cd;       (* arm_SQRDMULH_VEC Q13 Q6 Q13 16 128 *)
  0x6f474278;       (* arm_MLS_VEC Q24 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x4e6a86b0;       (* arm_ADD_VEC Q16 Q21 Q10 16 128 *)
  0x4e6f9cd2;       (* arm_MUL_VEC Q18 Q6 Q15 16 128 *)
  0x6e798693;       (* arm_SUB_VEC Q19 Q20 Q25 16 128 *)
  0x3dc02875;       (* arm_LDR Q21 X3 (Immediate_Offset (word 160)) *)
  0x3c840465;       (* arm_STR Q5 X3 (Postimmediate_Offset (word 64)) *)
  0x6f4741b2;       (* arm_MLS_VEC Q18 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e62b5cf;       (* arm_SQRDMULH_VEC Q15 Q14 Q2 16 128 *)
  0x3dc0146a;       (* arm_LDR Q10 X3 (Immediate_Offset (word 80)) *)
  0x3dc0106c;       (* arm_LDR Q12 X3 (Immediate_Offset (word 64)) *)
  0x3c9e0078;       (* arm_STR Q24 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x4f4b8905;       (* arm_MUL_VEC Q5 Q8 (Q11 :> LANE_H 4) 16 128 *)
  0x6e638640;       (* arm_SUB_VEC Q0 Q18 Q3 16 128 *)
  0x3dc01c78;       (* arm_LDR Q24 X3 (Immediate_Offset (word 112)) *)
  0x6f4743e5;       (* arm_MLS_VEC Q5 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0145a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 80)) *)
  0x4e8a6981;       (* arm_TRN2 Q1 Q12 Q10 32 128 *)
  0x4e638646;       (* arm_ADD_VEC Q6 Q18 Q3 16 128 *)
  0x6e62b414;       (* arm_SQRDMULH_VEC Q20 Q0 Q2 16 128 *)
  0x4e8a298d;       (* arm_TRN1 Q13 Q12 Q10 32 128 *)
  0x4e862a12;       (* arm_TRN1 Q18 Q16 Q6 32 128 *)
  0x4e7b9c16;       (* arm_MUL_VEC Q22 Q0 Q27 16 128 *)
  0x4e982ab1;       (* arm_TRN1 Q17 Q21 Q24 32 128 *)
  0x4f7bd260;       (* arm_SQRDMULH_VEC Q0 Q19 (Q11 :> LANE_H 3) 16 128 *)
  0x4ed129b9;       (* arm_TRN1 Q25 Q13 Q17 64 128 *)
  0x6f474296;       (* arm_MLS_VEC Q22 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4e986ab5;       (* arm_TRN2 Q21 Q21 Q24 32 128 *)
  0x4e7d9f38;       (* arm_MUL_VEC Q24 Q25 Q29 16 128 *)
  0x4ed169bc;       (* arm_TRN2 Q28 Q13 Q17 64 128 *)
  0x6e7eb724;       (* arm_SQRDMULH_VEC Q4 Q25 Q30 16 128 *)
  0x4ed56823;       (* arm_TRN2 Q3 Q1 Q21 64 128 *)
  0x4e7d9f91;       (* arm_MUL_VEC Q17 Q28 Q29 16 128 *)
  0x6e7eb79f;       (* arm_SQRDMULH_VEC Q31 Q28 Q30 16 128 *)
  0x3dc00442;       (* arm_LDR Q2 X2 (Immediate_Offset (word 16)) *)
  0x6f474098;       (* arm_MLS_VEC Q24 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6b8264;       (* arm_MUL_VEC Q4 Q19 (Q11 :> LANE_H 2) 16 128 *)
  0x3dc01053;       (* arm_LDR Q19 X2 (Immediate_Offset (word 64)) *)
  0x6f474004;       (* arm_MLS_VEC Q4 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7b9dc0;       (* arm_MUL_VEC Q0 Q14 Q27 16 128 *)
  0x6f4741e0;       (* arm_MLS_VEC Q0 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6e658488;       (* arm_SUB_VEC Q8 Q4 Q5 16 128 *)
  0x4e7d9c6c;       (* arm_MUL_VEC Q12 Q3 Q29 16 128 *)
  0x4f4b8117;       (* arm_MUL_VEC Q23 Q8 (Q11 :> LANE_H 0) 16 128 *)
  0x4e866a1c;       (* arm_TRN2 Q28 Q16 Q6 32 128 *)
  0x4f5bd10a;       (* arm_SQRDMULH_VEC Q10 Q8 (Q11 :> LANE_H 1) 16 128 *)
  0x4e962809;       (* arm_TRN1 Q9 Q0 Q22 32 128 *)
  0x4e966816;       (* arm_TRN2 Q22 Q0 Q22 32 128 *)
  0x3cc1042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 16)) *)
  0x6f4743f1;       (* arm_MLS_VEC Q17 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec92a54;       (* arm_TRN1 Q20 Q18 Q9 64 128 *)
  0x4ec96a4e;       (* arm_TRN2 Q14 Q18 Q9 64 128 *)
  0x3dc0084f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 32)) *)
  0x4ed52826;       (* arm_TRN1 Q6 Q1 Q21 64 128 *)
  0x6e7eb469;       (* arm_SQRDMULH_VEC Q9 Q3 Q30 16 128 *)
  0x4ed62b99;       (* arm_TRN1 Q25 Q28 Q22 64 128 *)
  0x4ed66b90;       (* arm_TRN2 Q16 Q28 Q22 64 128 *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e798681;       (* arm_ADD_VEC Q1 Q20 Q25 16 128 *)
  0x6e7eb4d5;       (* arm_SQRDMULH_VEC Q21 Q6 Q30 16 128 *)
  0x4e7085c8;       (* arm_ADD_VEC Q8 Q14 Q16 16 128 *)
  0x3cc6045b;       (* arm_LDR Q27 X2 (Postimmediate_Offset (word 96)) *)
  0x4f57c11c;       (* arm_SQDMULH_VEC Q28 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x6f47412c;       (* arm_MLS_VEC Q12 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c03f;       (* arm_SQDMULH_VEC Q31 Q1 (Q7 :> LANE_H 1) 16 128 *)
  0x4e7d9cc0;       (* arm_MUL_VEC Q0 Q6 Q29 16 128 *)
  0x6e6c862a;       (* arm_SUB_VEC Q10 Q17 Q12 16 128 *)
  0x6f4742a0;       (* arm_MLS_VEC Q0 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152795;       (* arm_SRSHR_VEC Q21 Q28 11 16 128 *)
  0x4f1527ed;       (* arm_SRSHR_VEC Q13 Q31 11 16 128 *)
  0x6e7ab556;       (* arm_SQRDMULH_VEC Q22 Q10 Q26 16 128 *)
  0x6f4742a8;       (* arm_MLS_VEC Q8 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741a1;       (* arm_MLS_VEC Q1 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4e608715;       (* arm_ADD_VEC Q21 Q24 Q0 16 128 *)
  0x3c9f0077;       (* arm_STR Q23 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e608706;       (* arm_SUB_VEC Q6 Q24 Q0 16 128 *)
  0x4e739d43;       (* arm_MUL_VEC Q3 Q10 Q19 16 128 *)
  0x4e658480;       (* arm_ADD_VEC Q0 Q4 Q5 16 128 *)
  0x4f57c00d;       (* arm_SQDMULH_VEC Q13 Q0 (Q7 :> LANE_H 1) 16 128 *)
  0x3cdd004a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e688425;       (* arm_ADD_VEC Q5 Q1 Q8 16 128 *)
  0x6f4742c3;       (* arm_MLS_VEC Q3 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6e688428;       (* arm_SUB_VEC Q8 Q1 Q8 16 128 *)
  0x4f4b8118;       (* arm_MUL_VEC Q24 Q8 (Q11 :> LANE_H 0) 16 128 *)
  0x4f5bd108;       (* arm_SQRDMULH_VEC Q8 Q8 (Q11 :> LANE_H 1) 16 128 *)
  0x4f1525a1;       (* arm_SRSHR_VEC Q1 Q13 11 16 128 *)
  0x6e6ab4cd;       (* arm_SQRDMULH_VEC Q13 Q6 Q10 16 128 *)
  0x6f474020;       (* arm_MLS_VEC Q0 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6c862a;       (* arm_ADD_VEC Q10 Q17 Q12 16 128 *)
  0x6f474118;       (* arm_MLS_VEC Q24 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7085c8;       (* arm_SUB_VEC Q8 Q14 Q16 16 128 *)
  0x4f5bd91f;       (* arm_SQRDMULH_VEC Q31 Q8 (Q11 :> LANE_H 5) 16 128 *)
  0x6e6a86ae;       (* arm_SUB_VEC Q14 Q21 Q10 16 128 *)
  0x3c9d0060;       (* arm_STR Q0 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff464;       (* arm_CBNZ X4 (word 2096780) *)
  0x4e6f9ccf;       (* arm_MUL_VEC Q15 Q6 Q15 16 128 *)
  0x6e798696;       (* arm_SUB_VEC Q22 Q20 Q25 16 128 *)
  0x4e6a86a4;       (* arm_ADD_VEC Q4 Q21 Q10 16 128 *)
  0x3d800878;       (* arm_STR Q24 X3 (Immediate_Offset (word 32)) *)
  0x6f4741af;       (* arm_MLS_VEC Q15 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3c840465;       (* arm_STR Q5 X3 (Postimmediate_Offset (word 64)) *)
  0x3cc10429;       (* arm_LDR Q9 X1 (Postimmediate_Offset (word 16)) *)
  0x6e62b5dc;       (* arm_SQRDMULH_VEC Q28 Q14 Q2 16 128 *)
  0x4e7b9dd0;       (* arm_MUL_VEC Q16 Q14 Q27 16 128 *)
  0x6e6385f2;       (* arm_SUB_VEC Q18 Q15 Q3 16 128 *)
  0x4e6385ef;       (* arm_ADD_VEC Q15 Q15 Q3 16 128 *)
  0x6e62b640;       (* arm_SQRDMULH_VEC Q0 Q18 Q2 16 128 *)
  0x4e8f6898;       (* arm_TRN2 Q24 Q4 Q15 32 128 *)
  0x4e8f2882;       (* arm_TRN1 Q2 Q4 Q15 32 128 *)
  0x4e7b9e52;       (* arm_MUL_VEC Q18 Q18 Q27 16 128 *)
  0x6f474390;       (* arm_MLS_VEC Q16 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474012;       (* arm_MLS_VEC Q18 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4b8917;       (* arm_MUL_VEC Q23 Q8 (Q11 :> LANE_H 4) 16 128 *)
  0x4f7bd2cc;       (* arm_SQRDMULH_VEC Q12 Q22 (Q11 :> LANE_H 3) 16 128 *)
  0x4e922a11;       (* arm_TRN1 Q17 Q16 Q18 32 128 *)
  0x4e926a04;       (* arm_TRN2 Q4 Q16 Q18 32 128 *)
  0x6f4743f7;       (* arm_MLS_VEC Q23 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed16843;       (* arm_TRN2 Q3 Q2 Q17 64 128 *)
  0x4ec46b06;       (* arm_TRN2 Q6 Q24 Q4 64 128 *)
  0x4f6b82da;       (* arm_MUL_VEC Q26 Q22 (Q11 :> LANE_H 2) 16 128 *)
  0x4ed1285c;       (* arm_TRN1 Q28 Q2 Q17 64 128 *)
  0x6f47419a;       (* arm_MLS_VEC Q26 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e668479;       (* arm_ADD_VEC Q25 Q3 Q6 16 128 *)
  0x6e668472;       (* arm_SUB_VEC Q18 Q3 Q6 16 128 *)
  0x4ec42b18;       (* arm_TRN1 Q24 Q24 Q4 64 128 *)
  0x4f57c321;       (* arm_SQDMULH_VEC Q1 Q25 (Q7 :> LANE_H 1) 16 128 *)
  0x6e78879b;       (* arm_SUB_VEC Q27 Q28 Q24 16 128 *)
  0x4f59da42;       (* arm_SQRDMULH_VEC Q2 Q18 (Q9 :> LANE_H 5) 16 128 *)
  0x4e78879c;       (* arm_ADD_VEC Q28 Q28 Q24 16 128 *)
  0x4f698378;       (* arm_MUL_VEC Q24 Q27 (Q9 :> LANE_H 2) 16 128 *)
  0x4f57c38c;       (* arm_SQDMULH_VEC Q12 Q28 (Q7 :> LANE_H 1) 16 128 *)
  0x4f498a54;       (* arm_MUL_VEC Q20 Q18 (Q9 :> LANE_H 4) 16 128 *)
  0x6f474054;       (* arm_MLS_VEC Q20 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152421;       (* arm_SRSHR_VEC Q1 Q1 11 16 128 *)
  0x4f79d373;       (* arm_SQRDMULH_VEC Q19 Q27 (Q9 :> LANE_H 3) 16 128 *)
  0x4f15258f;       (* arm_SRSHR_VEC Q15 Q12 11 16 128 *)
  0x6f474039;       (* arm_MLS_VEC Q25 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4e778748;       (* arm_ADD_VEC Q8 Q26 Q23 16 128 *)
  0x6e778744;       (* arm_SUB_VEC Q4 Q26 Q23 16 128 *)
  0x6f4741fc;       (* arm_MLS_VEC Q28 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474278;       (* arm_MLS_VEC Q24 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4b8082;       (* arm_MUL_VEC Q2 Q4 (Q11 :> LANE_H 0) 16 128 *)
  0x6e798793;       (* arm_SUB_VEC Q19 Q28 Q25 16 128 *)
  0x4f5bd08f;       (* arm_SQRDMULH_VEC Q15 Q4 (Q11 :> LANE_H 1) 16 128 *)
  0x4e798799;       (* arm_ADD_VEC Q25 Q28 Q25 16 128 *)
  0x6e74870a;       (* arm_SUB_VEC Q10 Q24 Q20 16 128 *)
  0x3c840479;       (* arm_STR Q25 X3 (Postimmediate_Offset (word 64)) *)
  0x4f59d276;       (* arm_SQRDMULH_VEC Q22 Q19 (Q9 :> LANE_H 1) 16 128 *)
  0x4e74871c;       (* arm_ADD_VEC Q28 Q24 Q20 16 128 *)
  0x4f59d159;       (* arm_SQRDMULH_VEC Q25 Q10 (Q9 :> LANE_H 1) 16 128 *)
  0x4f49827b;       (* arm_MUL_VEC Q27 Q19 (Q9 :> LANE_H 0) 16 128 *)
  0x4f49815a;       (* arm_MUL_VEC Q26 Q10 (Q9 :> LANE_H 0) 16 128 *)
  0x4f57c394;       (* arm_SQDMULH_VEC Q20 Q28 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c110;       (* arm_SQDMULH_VEC Q16 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x6f47433a;       (* arm_MLS_VEC Q26 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741e2;       (* arm_MLS_VEC Q2 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f15268f;       (* arm_SRSHR_VEC Q15 Q20 11 16 128 *)
  0x4f152601;       (* arm_SRSHR_VEC Q1 Q16 11 16 128 *)
  0x6f4742db;       (* arm_MLS_VEC Q27 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741fc;       (* arm_MLS_VEC Q28 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474028;       (* arm_MLS_VEC Q8 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9e007b;       (* arm_STR Q27 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9b0062;       (* arm_STR Q2 X3 (Immediate_Offset (word 18446744073709551536)) *)
  0x3c9d007c;       (* arm_STR Q28 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9f007a;       (* arm_STR Q26 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c990068;       (* arm_STR Q8 X3 (Immediate_Offset (word 18446744073709551504)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0001a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 0)) *)
  0x3dc0100d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 64)) *)
  0x3dc0301c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 192)) *)
  0x3dc05002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 320)) *)
  0x3dc02006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 128)) *)
  0x3dc04009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 256)) *)
  0x3dc0701d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 448)) *)
  0x3dc06017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 384)) *)
  0x6e6d8751;       (* arm_SUB_VEC Q17 Q26 Q13 16 128 *)
  0x4e6d8744;       (* arm_ADD_VEC Q4 Q26 Q13 16 128 *)
  0x3dc03419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 208)) *)
  0x3dc01418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 80)) *)
  0x4e7c84c5;       (* arm_ADD_VEC Q5 Q6 Q28 16 128 *)
  0x4f608a33;       (* arm_MUL_VEC Q19 Q17 (Q0 :> LANE_H 6) 16 128 *)
  0x6e7c84ca;       (* arm_SUB_VEC Q10 Q6 Q28 16 128 *)
  0x3dc0541e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 336)) *)
  0x4f70da2c;       (* arm_SQRDMULH_VEC Q12 Q17 (Q0 :> LANE_H 7) 16 128 *)
  0x4e628531;       (* arm_ADD_VEC Q17 Q9 Q2 16 128 *)
  0x6e62853c;       (* arm_SUB_VEC Q28 Q9 Q2 16 128 *)
  0x3dc02402;       (* arm_LDR Q2 X0 (Immediate_Offset (word 144)) *)
  0x6e7d86fa;       (* arm_SUB_VEC Q26 Q23 Q29 16 128 *)
  0x4f51d15f;       (* arm_SQRDMULH_VEC Q31 Q10 (Q1 :> LANE_H 1) 16 128 *)
  0x4e7d86f6;       (* arm_ADD_VEC Q22 Q23 Q29 16 128 *)
  0x3dc04403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 272)) *)
  0x4f71d389;       (* arm_SQRDMULH_VEC Q9 Q28 (Q1 :> LANE_H 3) 16 128 *)
  0x6e658494;       (* arm_SUB_VEC Q20 Q4 Q5 16 128 *)
  0x6e76863b;       (* arm_SUB_VEC Q27 Q17 Q22 16 128 *)
  0x3dc0041d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 16)) *)
  0x4e658490;       (* arm_ADD_VEC Q16 Q4 Q5 16 128 *)
  0x4f51db44;       (* arm_SQRDMULH_VEC Q4 Q26 (Q1 :> LANE_H 5) 16 128 *)
  0x4e768626;       (* arm_ADD_VEC Q6 Q17 Q22 16 128 *)
  0x3dc07416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 464)) *)
  0x4f618388;       (* arm_MUL_VEC Q8 Q28 (Q1 :> LANE_H 2) 16 128 *)
  0x6e798455;       (* arm_SUB_VEC Q21 Q2 Q25 16 128 *)
  0x6e668605;       (* arm_SUB_VEC Q5 Q16 Q6 16 128 *)
  0x4f418b51;       (* arm_MUL_VEC Q17 Q26 (Q1 :> LANE_H 4) 16 128 *)
  0x4f41815a;       (* arm_MUL_VEC Q26 Q10 (Q1 :> LANE_H 0) 16 128 *)
  0x6f4743fa;       (* arm_MLS_VEC Q26 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474091;       (* arm_MLS_VEC Q17 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474193;       (* arm_MLS_VEC Q19 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474128;       (* arm_MLS_VEC Q8 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50db6a;       (* arm_SQRDMULH_VEC Q10 Q27 (Q0 :> LANE_H 5) 16 128 *)
  0x6e7a866c;       (* arm_SUB_VEC Q12 Q19 Q26 16 128 *)
  0x4e7a8669;       (* arm_ADD_VEC Q9 Q19 Q26 16 128 *)
  0x4f70d29a;       (* arm_SQRDMULH_VEC Q26 Q20 (Q0 :> LANE_H 3) 16 128 *)
  0x6e71850b;       (* arm_SUB_VEC Q11 Q8 Q17 16 128 *)
  0x4e71850e;       (* arm_ADD_VEC Q14 Q8 Q17 16 128 *)
  0x4f70d18d;       (* arm_SQRDMULH_VEC Q13 Q12 (Q0 :> LANE_H 3) 16 128 *)
  0x4e6e8537;       (* arm_ADD_VEC Q23 Q9 Q14 16 128 *)
  0x4f50d97c;       (* arm_SQRDMULH_VEC Q28 Q11 (Q0 :> LANE_H 5) 16 128 *)
  0x6e6e8533;       (* arm_SUB_VEC Q19 Q9 Q14 16 128 *)
  0x4f408b71;       (* arm_MUL_VEC Q17 Q27 (Q0 :> LANE_H 4) 16 128 *)
  0x3d801017;       (* arm_STR Q23 X0 (Immediate_Offset (word 64)) *)
  0x4f60828e;       (* arm_MUL_VEC Q14 Q20 (Q0 :> LANE_H 2) 16 128 *)
  0x4f408968;       (* arm_MUL_VEC Q8 Q11 (Q0 :> LANE_H 4) 16 128 *)
  0x4f608184;       (* arm_MUL_VEC Q4 Q12 (Q0 :> LANE_H 2) 16 128 *)
  0x6f47434e;       (* arm_MLS_VEC Q14 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474151;       (* arm_MLS_VEC Q17 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474388;       (* arm_MLS_VEC Q8 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741a4;       (* arm_MLS_VEC Q4 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7185ca;       (* arm_SUB_VEC Q10 Q14 Q17 16 128 *)
  0x4e7185d4;       (* arm_ADD_VEC Q20 Q14 Q17 16 128 *)
  0x4f50d0bc;       (* arm_SQRDMULH_VEC Q28 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4080b2;       (* arm_MUL_VEC Q18 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x3d802014;       (* arm_STR Q20 X0 (Immediate_Offset (word 128)) *)
  0x6e68848d;       (* arm_SUB_VEC Q13 Q4 Q8 16 128 *)
  0x4f408157;       (* arm_MUL_VEC Q23 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x4f408271;       (* arm_MUL_VEC Q17 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d1a9;       (* arm_SQRDMULH_VEC Q9 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474392;       (* arm_MLS_VEC Q18 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d14a;       (* arm_SQRDMULH_VEC Q10 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6e7e846c;       (* arm_SUB_VEC Q12 Q3 Q30 16 128 *)
  0x4f4182ab;       (* arm_MUL_VEC Q11 Q21 (Q1 :> LANE_H 0) 16 128 *)
  0x4e68849c;       (* arm_ADD_VEC Q28 Q4 Q8 16 128 *)
  0x3dc06414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 400)) *)
  0x4e66861b;       (* arm_ADD_VEC Q27 Q16 Q6 16 128 *)
  0x4f71d188;       (* arm_SQRDMULH_VEC Q8 Q12 (Q1 :> LANE_H 3) 16 128 *)
  0x4e7887b0;       (* arm_ADD_VEC Q16 Q29 Q24 16 128 *)
  0x3d80301c;       (* arm_STR Q28 X0 (Immediate_Offset (word 192)) *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3c81041b;       (* arm_STR Q27 X0 (Postimmediate_Offset (word 16)) *)
  0x4e76868f;       (* arm_ADD_VEC Q15 Q20 Q22 16 128 *)
  0x3d803c12;       (* arm_STR Q18 X0 (Immediate_Offset (word 240)) *)
  0x4f4081ae;       (* arm_MUL_VEC Q14 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x4e798442;       (* arm_ADD_VEC Q2 Q2 Q25 16 128 *)
  0x6e76869a;       (* arm_SUB_VEC Q26 Q20 Q22 16 128 *)
  0x4f618184;       (* arm_MUL_VEC Q4 Q12 (Q1 :> LANE_H 2) 16 128 *)
  0x6e628605;       (* arm_SUB_VEC Q5 Q16 Q2 16 128 *)
  0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
  0x4e7e8474;       (* arm_ADD_VEC Q20 Q3 Q30 16 128 *)
  0x4f51db5b;       (* arm_SQRDMULH_VEC Q27 Q26 (Q1 :> LANE_H 5) 16 128 *)
  0x4e628610;       (* arm_ADD_VEC Q16 Q16 Q2 16 128 *)
  0x4f418b52;       (* arm_MUL_VEC Q18 Q26 (Q1 :> LANE_H 4) 16 128 *)
  0x6e6f869f;       (* arm_SUB_VEC Q31 Q20 Q15 16 128 *)
  0x6f474104;       (* arm_MLS_VEC Q4 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7887bc;       (* arm_SUB_VEC Q28 Q29 Q24 16 128 *)
  0x6f474372;       (* arm_MLS_VEC Q18 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc07416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 464)) *)
  0x4f608b9a;       (* arm_MUL_VEC Q26 Q28 (Q0 :> LANE_H 6) 16 128 *)
  0x4f6080a2;       (* arm_MUL_VEC Q2 Q5 (Q0 :> LANE_H 2) 16 128 *)
  0x6e72848c;       (* arm_SUB_VEC Q12 Q4 Q18 16 128 *)
  0x4f70db98;       (* arm_SQRDMULH_VEC Q24 Q28 (Q0 :> LANE_H 7) 16 128 *)
  0x6f47412e;       (* arm_MLS_VEC Q14 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d98a;       (* arm_SQRDMULH_VEC Q10 Q12 (Q0 :> LANE_H 5) 16 128 *)
  0x6f47431a;       (* arm_MLS_VEC Q26 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 80)) *)
  0x4f408988;       (* arm_MUL_VEC Q8 Q12 (Q0 :> LANE_H 4) 16 128 *)
  0x3d806c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 432)) *)
  0x4e72849c;       (* arm_ADD_VEC Q28 Q4 Q18 16 128 *)
  0x4f70d0a5;       (* arm_SQRDMULH_VEC Q5 Q5 (Q0 :> LANE_H 3) 16 128 *)
  0x4e6f8686;       (* arm_ADD_VEC Q6 Q20 Q15 16 128 *)
  0x4f50d263;       (* arm_SQRDMULH_VEC Q3 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x6e66860d;       (* arm_SUB_VEC Q13 Q16 Q6 16 128 *)
  0x4f51d2ac;       (* arm_SQRDMULH_VEC Q12 Q21 (Q1 :> LANE_H 1) 16 128 *)
  0x4f50d1b5;       (* arm_SQRDMULH_VEC Q21 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50dbfb;       (* arm_SQRDMULH_VEC Q27 Q31 (Q0 :> LANE_H 5) 16 128 *)
  0x3dc03419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 208)) *)
  0x6f47418b;       (* arm_MLS_VEC Q11 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408bf7;       (* arm_MUL_VEC Q23 Q31 (Q0 :> LANE_H 4) 16 128 *)
  0x4f4081b2;       (* arm_MUL_VEC Q18 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6b875e;       (* arm_ADD_VEC Q30 Q26 Q11 16 128 *)
  0x6e6b874d;       (* arm_SUB_VEC Q13 Q26 Q11 16 128 *)
  0x6f474377;       (* arm_MLS_VEC Q23 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7c87cc;       (* arm_ADD_VEC Q12 Q30 Q28 16 128 *)
  0x6e7c87d3;       (* arm_SUB_VEC Q19 Q30 Q28 16 128 *)
  0x6f4740a2;       (* arm_MLS_VEC Q2 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80100c;       (* arm_STR Q12 X0 (Immediate_Offset (word 64)) *)
  0x4f70d1ba;       (* arm_SQRDMULH_VEC Q26 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x6f474148;       (* arm_MLS_VEC Q8 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0541e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 336)) *)
  0x6e778454;       (* arm_SUB_VEC Q20 Q2 Q23 16 128 *)
  0x4f6081a4;       (* arm_MUL_VEC Q4 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x4e77844d;       (* arm_ADD_VEC Q13 Q2 Q23 16 128 *)
  0x6f474344;       (* arm_MLS_VEC Q4 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc02402;       (* arm_LDR Q2 X0 (Immediate_Offset (word 144)) *)
  0x4f408297;       (* arm_MUL_VEC Q23 Q20 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc0041d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 16)) *)
  0x4f50d28a;       (* arm_SQRDMULH_VEC Q10 Q20 (Q0 :> LANE_H 1) 16 128 *)
  0x3d80200d;       (* arm_STR Q13 X0 (Immediate_Offset (word 128)) *)
  0x6e68848d;       (* arm_SUB_VEC Q13 Q4 Q8 16 128 *)
  0x6f474071;       (* arm_MLS_VEC Q17 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc04403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 272)) *)
  0x6f4742b2;       (* arm_MLS_VEC Q18 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6e798455;       (* arm_SUB_VEC Q21 Q2 Q25 16 128 *)
  0x4f50d1a9;       (* arm_SQRDMULH_VEC Q9 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x3d804c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 304)) *)
  0x4f408271;       (* arm_MUL_VEC Q17 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0640b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 400)) *)
  0x3d804012;       (* arm_STR Q18 X0 (Immediate_Offset (word 256)) *)
  0x4e7e847b;       (* arm_ADD_VEC Q27 Q3 Q30 16 128 *)
  0x4f4081ad;       (* arm_MUL_VEC Q13 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7887a5;       (* arm_SUB_VEC Q5 Q29 Q24 16 128 *)
  0x4e66860e;       (* arm_ADD_VEC Q14 Q16 Q6 16 128 *)
  0x6f47412d;       (* arm_MLS_VEC Q13 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4e76856a;       (* arm_ADD_VEC Q10 Q11 Q22 16 128 *)
  0x3d806017;       (* arm_STR Q23 X0 (Immediate_Offset (word 384)) *)
  0x6e768574;       (* arm_SUB_VEC Q20 Q11 Q22 16 128 *)
  0x6e6a8777;       (* arm_SUB_VEC Q23 Q27 Q10 16 128 *)
  0x4f51d2b0;       (* arm_SQRDMULH_VEC Q16 Q21 (Q1 :> LANE_H 1) 16 128 *)
  0x4f50daff;       (* arm_SQRDMULH_VEC Q31 Q23 (Q0 :> LANE_H 5) 16 128 *)
  0x3d80700d;       (* arm_STR Q13 X0 (Immediate_Offset (word 448)) *)
  0x4e68848d;       (* arm_ADD_VEC Q13 Q4 Q8 16 128 *)
  0x4f4182b2;       (* arm_MUL_VEC Q18 Q21 (Q1 :> LANE_H 0) 16 128 *)
  0x3d80300d;       (* arm_STR Q13 X0 (Immediate_Offset (word 192)) *)
  0x4f50d26d;       (* arm_SQRDMULH_VEC Q13 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x4f51da9c;       (* arm_SQRDMULH_VEC Q28 Q20 (Q1 :> LANE_H 5) 16 128 *)
  0x3c81040e;       (* arm_STR Q14 X0 (Postimmediate_Offset (word 16)) *)
  0x4f418a84;       (* arm_MUL_VEC Q4 Q20 (Q1 :> LANE_H 4) 16 128 *)
  0x6f4741b1;       (* arm_MLS_VEC Q17 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7e846d;       (* arm_SUB_VEC Q13 Q3 Q30 16 128 *)
  0x4f71d1a8;       (* arm_SQRDMULH_VEC Q8 Q13 (Q1 :> LANE_H 3) 16 128 *)
  0x4f6181ac;       (* arm_MUL_VEC Q12 Q13 (Q1 :> LANE_H 2) 16 128 *)
  0x6f474384;       (* arm_MLS_VEC Q4 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47410c;       (* arm_MLS_VEC Q12 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474212;       (* arm_MLS_VEC Q18 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 304)) *)
  0x4f70d8af;       (* arm_SQRDMULH_VEC Q15 Q5 (Q0 :> LANE_H 7) 16 128 *)
  0x4e6a876b;       (* arm_ADD_VEC Q11 Q27 Q10 16 128 *)
  0x4f6088b0;       (* arm_MUL_VEC Q16 Q5 (Q0 :> LANE_H 6) 16 128 *)
  0x6e648588;       (* arm_SUB_VEC Q8 Q12 Q4 16 128 *)
  0x4f50d91c;       (* arm_SQRDMULH_VEC Q28 Q8 (Q0 :> LANE_H 5) 16 128 *)
  0x4e79844d;       (* arm_ADD_VEC Q13 Q2 Q25 16 128 *)
  0x6f4741f0;       (* arm_MLS_VEC Q16 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e64859a;       (* arm_ADD_VEC Q26 Q12 Q4 16 128 *)
  0x4f408908;       (* arm_MUL_VEC Q8 Q8 (Q0 :> LANE_H 4) 16 128 *)
  0x4e7887a4;       (* arm_ADD_VEC Q4 Q29 Q24 16 128 *)
  0x6f474388;       (* arm_MLS_VEC Q8 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d8494;       (* arm_SUB_VEC Q20 Q4 Q13 16 128 *)
  0x4e6d848e;       (* arm_ADD_VEC Q14 Q4 Q13 16 128 *)
  0x4e72860c;       (* arm_ADD_VEC Q12 Q16 Q18 16 128 *)
  0x4f70d296;       (* arm_SQRDMULH_VEC Q22 Q20 (Q0 :> LANE_H 3) 16 128 *)
  0x4e6b85db;       (* arm_ADD_VEC Q27 Q14 Q11 16 128 *)
  0x6e72860d;       (* arm_SUB_VEC Q13 Q16 Q18 16 128 *)
  0x4f608284;       (* arm_MUL_VEC Q4 Q20 (Q0 :> LANE_H 2) 16 128 *)
  0x3c81041b;       (* arm_STR Q27 X0 (Postimmediate_Offset (word 16)) *)
  0x6e7a8598;       (* arm_SUB_VEC Q24 Q12 Q26 16 128 *)
  0x4f70d1a3;       (* arm_SQRDMULH_VEC Q3 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6081ad;       (* arm_MUL_VEC Q13 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50d31b;       (* arm_SQRDMULH_VEC Q27 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x6f47406d;       (* arm_MLS_VEC Q13 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408309;       (* arm_MUL_VEC Q9 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474369;       (* arm_MLS_VEC Q9 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6885be;       (* arm_ADD_VEC Q30 Q13 Q8 16 128 *)
  0x6e6885ad;       (* arm_SUB_VEC Q13 Q13 Q8 16 128 *)
  0x6f4742c4;       (* arm_MLS_VEC Q4 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x3d802c1e;       (* arm_STR Q30 X0 (Immediate_Offset (word 176)) *)
  0x4f50d1b0;       (* arm_SQRDMULH_VEC Q16 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x3d804c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 304)) *)
  0x4f4081a9;       (* arm_MUL_VEC Q9 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7a858d;       (* arm_ADD_VEC Q13 Q12 Q26 16 128 *)
  0x3d800c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 48)) *)
  0x4f408aed;       (* arm_MUL_VEC Q13 Q23 (Q0 :> LANE_H 4) 16 128 *)
  0x6e6b85d7;       (* arm_SUB_VEC Q23 Q14 Q11 16 128 *)
  0x6f4743ed;       (* arm_MLS_VEC Q13 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474209;       (* arm_MLS_VEC Q9 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4082fe;       (* arm_MUL_VEC Q30 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x6e6d8498;       (* arm_SUB_VEC Q24 Q4 Q13 16 128 *)
  0x4e6d848d;       (* arm_ADD_VEC Q13 Q4 Q13 16 128 *)
  0x4f50d2f7;       (* arm_SQRDMULH_VEC Q23 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x3d806c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 432)) *)
  0x3d801c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 112)) *)
  0x4f50d30d;       (* arm_SQRDMULH_VEC Q13 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408315;       (* arm_MUL_VEC Q21 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4742fe;       (* arm_MLS_VEC Q30 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741b5;       (* arm_MLS_VEC Q21 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3d803c1e;       (* arm_STR Q30 X0 (Immediate_Offset (word 240)) *)
  0x3d805c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 368)) *)
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
