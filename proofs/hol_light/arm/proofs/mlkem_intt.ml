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
  0x3dc00075;       (* arm_LDR Q21 X3 (Immediate_Offset (word 0)) *)
  0x3dc0047e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 16)) *)
  0x3dc00c6d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 48)) *)
  0x3dc0086c;       (* arm_LDR Q12 X3 (Immediate_Offset (word 32)) *)
  0x4e9e2abb;       (* arm_TRN1 Q27 Q21 Q30 32 128 *)
  0x4e9e6ab5;       (* arm_TRN2 Q21 Q21 Q30 32 128 *)
  0x4e8d698a;       (* arm_TRN2 Q10 Q12 Q13 32 128 *)
  0x4e8d2996;       (* arm_TRN1 Q22 Q12 Q13 32 128 *)
  0x3dc01443;       (* arm_LDR Q3 X2 (Immediate_Offset (word 80)) *)
  0x4ed66b65;       (* arm_TRN2 Q5 Q27 Q22 64 128 *)
  0x4eca6aac;       (* arm_TRN2 Q12 Q21 Q10 64 128 *)
  0x4eca2aa9;       (* arm_TRN1 Q9 Q21 Q10 64 128 *)
  0x4ed62b7e;       (* arm_TRN1 Q30 Q27 Q22 64 128 *)
  0x6e6c84b5;       (* arm_SUB_VEC Q21 Q5 Q12 16 128 *)
  0x3dc00c4d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 48)) *)
  0x3dc0084f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 32)) *)
  0x6e63b6bf;       (* arm_SQRDMULH_VEC Q31 Q21 Q3 16 128 *)
  0x6e6987ca;       (* arm_SUB_VEC Q10 Q30 Q9 16 128 *)
  0x3dc02846;       (* arm_LDR Q6 X2 (Immediate_Offset (word 160)) *)
  0x6e6db54d;       (* arm_SQRDMULH_VEC Q13 Q10 Q13 16 128 *)
  0x3dc01043;       (* arm_LDR Q3 X2 (Immediate_Offset (word 64)) *)
  0x4e6987de;       (* arm_ADD_VEC Q30 Q30 Q9 16 128 *)
  0x4e6f9d5c;       (* arm_MUL_VEC Q28 Q10 Q15 16 128 *)
  0x3dc01479;       (* arm_LDR Q25 X3 (Immediate_Offset (word 80)) *)
  0x3cc60458;       (* arm_LDR Q24 X2 (Postimmediate_Offset (word 96)) *)
  0x4e6c84aa;       (* arm_ADD_VEC Q10 Q5 Q12 16 128 *)
  0x4e639eac;       (* arm_MUL_VEC Q12 Q21 Q3 16 128 *)
  0x3dc0106f;       (* arm_LDR Q15 X3 (Immediate_Offset (word 64)) *)
  0x4e6a87c9;       (* arm_ADD_VEC Q9 Q30 Q10 16 128 *)
  0x3dc01863;       (* arm_LDR Q3 X3 (Immediate_Offset (word 96)) *)
  0x6f4743ec;       (* arm_MLS_VEC Q12 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01c7f;       (* arm_LDR Q31 X3 (Immediate_Offset (word 112)) *)
  0x6e6a87d5;       (* arm_SUB_VEC Q21 Q30 Q10 16 128 *)
  0x6f4741bc;       (* arm_MLS_VEC Q28 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9969e5;       (* arm_TRN2 Q5 Q15 Q25 32 128 *)
  0x3cdb004d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4e9929ef;       (* arm_TRN1 Q15 Q15 Q25 32 128 *)
  0x4e9f287a;       (* arm_TRN1 Q26 Q3 Q31 32 128 *)
  0x4e789eab;       (* arm_MUL_VEC Q11 Q21 Q24 16 128 *)
  0x4eda69f3;       (* arm_TRN2 Q19 Q15 Q26 64 128 *)
  0x3dc0145b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 80)) *)
  0x6e6db6be;       (* arm_SQRDMULH_VEC Q30 Q21 Q13 16 128 *)
  0x6e6c8795;       (* arm_SUB_VEC Q21 Q28 Q12 16 128 *)
  0x6e6db6b9;       (* arm_SQRDMULH_VEC Q25 Q21 Q13 16 128 *)
  0x4e6c8790;       (* arm_ADD_VEC Q16 Q28 Q12 16 128 *)
  0x4e9f686d;       (* arm_TRN2 Q13 Q3 Q31 32 128 *)
  0x4e789ea4;       (* arm_MUL_VEC Q4 Q21 Q24 16 128 *)
  0x4ecd28a3;       (* arm_TRN1 Q3 Q5 Q13 64 128 *)
  0x6f4743cb;       (* arm_MLS_VEC Q11 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4ecd68bc;       (* arm_TRN2 Q28 Q5 Q13 64 128 *)
  0x4eda29f5;       (* arm_TRN1 Q21 Q15 Q26 64 128 *)
  0x3dc00c4a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 48)) *)
  0x6f474324;       (* arm_MLS_VEC Q4 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7c8665;       (* arm_SUB_VEC Q5 Q19 Q28 16 128 *)
  0x6e6386ad;       (* arm_SUB_VEC Q13 Q21 Q3 16 128 *)
  0x6e7bb4bf;       (* arm_SQRDMULH_VEC Q31 Q5 Q27 16 128 *)
  0x4e902921;       (* arm_TRN1 Q1 Q9 Q16 32 128 *)
  0x4e906929;       (* arm_TRN2 Q9 Q9 Q16 32 128 *)
  0x3dc00854;       (* arm_LDR Q20 X2 (Immediate_Offset (word 32)) *)
  0x6e6ab5b2;       (* arm_SQRDMULH_VEC Q18 Q13 Q10 16 128 *)
  0x4e6386be;       (* arm_ADD_VEC Q30 Q21 Q3 16 128 *)
  0x4e842979;       (* arm_TRN1 Q25 Q11 Q4 32 128 *)
  0x4e846975;       (* arm_TRN2 Q21 Q11 Q4 32 128 *)
  0x4ed9682a;       (* arm_TRN2 Q10 Q1 Q25 64 128 *)
  0x3cc1042c;       (* arm_LDR Q12 X1 (Postimmediate_Offset (word 16)) *)
  0x4e749daf;       (* arm_MUL_VEC Q15 Q13 Q20 16 128 *)
  0x4ed5692d;       (* arm_TRN2 Q13 Q9 Q21 64 128 *)
  0x4e6d8557;       (* arm_ADD_VEC Q23 Q10 Q13 16 128 *)
  0x6e6d854a;       (* arm_SUB_VEC Q10 Q10 Q13 16 128 *)
  0x4ed52929;       (* arm_TRN1 Q9 Q9 Q21 64 128 *)
  0x4f5cd94d;       (* arm_SQRDMULH_VEC Q13 Q10 (Q12 :> LANE_H 5) 16 128 *)
  0x4f57c2e3;       (* arm_SQDMULH_VEC Q3 Q23 (Q7 :> LANE_H 1) 16 128 *)
  0x4ed92835;       (* arm_TRN1 Q21 Q1 Q25 64 128 *)
  0x4f4c895d;       (* arm_MUL_VEC Q29 Q10 (Q12 :> LANE_H 4) 16 128 *)
  0x4e6986a4;       (* arm_ADD_VEC Q4 Q21 Q9 16 128 *)
  0x6f4741bd;       (* arm_MLS_VEC Q29 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6986aa;       (* arm_SUB_VEC Q10 Q21 Q9 16 128 *)
  0x4f7cd155;       (* arm_SQRDMULH_VEC Q21 Q10 (Q12 :> LANE_H 3) 16 128 *)
  0x4f57c08d;       (* arm_SQDMULH_VEC Q13 Q4 (Q7 :> LANE_H 1) 16 128 *)
  0x4f6c8151;       (* arm_MUL_VEC Q17 Q10 (Q12 :> LANE_H 2) 16 128 *)
  0x4f15246a;       (* arm_SRSHR_VEC Q10 Q3 11 16 128 *)
  0x6f4742b1;       (* arm_MLS_VEC Q17 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4f1525ad;       (* arm_SRSHR_VEC Q13 Q13 11 16 128 *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741a4;       (* arm_MLS_VEC Q4 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7d862b;       (* arm_ADD_VEC Q11 Q17 Q29 16 128 *)
  0x4f57c16d;       (* arm_SQDMULH_VEC Q13 Q11 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7d862a;       (* arm_SUB_VEC Q10 Q17 Q29 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6f47424f;       (* arm_MLS_VEC Q15 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0247a;       (* arm_LDR Q26 X3 (Immediate_Offset (word 144)) *)
  0x4f4c814e;       (* arm_MUL_VEC Q14 Q10 (Q12 :> LANE_H 0) 16 128 *)
  0x3cc60449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 96)) *)
  0x3dc02070;       (* arm_LDR Q16 X3 (Immediate_Offset (word 128)) *)
  0x4f1525b2;       (* arm_SRSHR_VEC Q18 Q13 11 16 128 *)
  0x4f5cd155;       (* arm_SQRDMULH_VEC Q21 Q10 (Q12 :> LANE_H 1) 16 128 *)
  0x4e7c866a;       (* arm_ADD_VEC Q10 Q19 Q28 16 128 *)
  0x4e669ca5;       (* arm_MUL_VEC Q5 Q5 Q6 16 128 *)
  0x3dc01459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 80)) *)
  0x6e77848d;       (* arm_SUB_VEC Q13 Q4 Q23 16 128 *)
  0x6f47424b;       (* arm_MLS_VEC Q11 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6a87c6;       (* arm_ADD_VEC Q6 Q30 Q10 16 128 *)
  0x6e6a87ca;       (* arm_SUB_VEC Q10 Q30 Q10 16 128 *)
  0x3cdb005e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x6f4743e5;       (* arm_MLS_VEC Q5 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9a6a1c;       (* arm_TRN2 Q28 Q16 Q26 32 128 *)
  0x4e699d52;       (* arm_MUL_VEC Q18 Q10 Q9 16 128 *)
  0x3dc02c7b;       (* arm_LDR Q27 X3 (Immediate_Offset (word 176)) *)
  0x6e7eb543;       (* arm_SQRDMULH_VEC Q3 Q10 Q30 16 128 *)
  0x4e77848a;       (* arm_ADD_VEC Q10 Q4 Q23 16 128 *)
  0x6e6585f1;       (* arm_SUB_VEC Q17 Q15 Q5 16 128 *)
  0x3dc02874;       (* arm_LDR Q20 X3 (Immediate_Offset (word 160)) *)
  0x4e6585ff;       (* arm_ADD_VEC Q31 Q15 Q5 16 128 *)
  0x4f5cd1a4;       (* arm_SQRDMULH_VEC Q4 Q13 (Q12 :> LANE_H 1) 16 128 *)
  0x4e9a2a0f;       (* arm_TRN1 Q15 Q16 Q26 32 128 *)
  0x3c84046a;       (* arm_STR Q10 X3 (Postimmediate_Offset (word 64)) *)
  0x6e7eb62a;       (* arm_SQRDMULH_VEC Q10 Q17 Q30 16 128 *)
  0x4e9f28de;       (* arm_TRN1 Q30 Q6 Q31 32 128 *)
  0x3c9d006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e9b6a85;       (* arm_TRN2 Q5 Q20 Q27 32 128 *)
  0x4e699e21;       (* arm_MUL_VEC Q1 Q17 Q9 16 128 *)
  0x4e9b2a89;       (* arm_TRN1 Q9 Q20 Q27 32 128 *)
  0x3dc00854;       (* arm_LDR Q20 X2 (Immediate_Offset (word 32)) *)
  0x6f474072;       (* arm_MLS_VEC Q18 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec52b9b;       (* arm_TRN1 Q27 Q28 Q5 64 128 *)
  0x4ec969f3;       (* arm_TRN2 Q19 Q15 Q9 64 128 *)
  0x6f474141;       (* arm_MLS_VEC Q1 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec929e8;       (* arm_TRN1 Q8 Q15 Q9 64 128 *)
  0x4ec56b9c;       (* arm_TRN2 Q28 Q28 Q5 64 128 *)
  0x3dc00c4f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 48)) *)
  0x4f4c81a0;       (* arm_MUL_VEC Q0 Q13 (Q12 :> LANE_H 0) 16 128 *)
  0x6e7b8509;       (* arm_SUB_VEC Q9 Q8 Q27 16 128 *)
  0x6e7c8665;       (* arm_SUB_VEC Q5 Q19 Q28 16 128 *)
  0x3cc1042c;       (* arm_LDR Q12 X1 (Postimmediate_Offset (word 16)) *)
  0x6f474080;       (* arm_MLS_VEC Q0 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9f68c6;       (* arm_TRN2 Q6 Q6 Q31 32 128 *)
  0x4e812a43;       (* arm_TRN1 Q3 Q18 Q1 32 128 *)
  0x6f4742ae;       (* arm_MLS_VEC Q14 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e816a55;       (* arm_TRN2 Q21 Q18 Q1 32 128 *)
  0x4ec36bca;       (* arm_TRN2 Q10 Q30 Q3 64 128 *)
  0x6e79b4bf;       (* arm_SQRDMULH_VEC Q31 Q5 Q25 16 128 *)
  0x4ed568cd;       (* arm_TRN2 Q13 Q6 Q21 64 128 *)
  0x4ed528d0;       (* arm_TRN1 Q16 Q6 Q21 64 128 *)
  0x3c9e0060;       (* arm_STR Q0 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x6e6fb532;       (* arm_SQRDMULH_VEC Q18 Q9 Q15 16 128 *)
  0x4e6d8557;       (* arm_ADD_VEC Q23 Q10 Q13 16 128 *)
  0x4ec32bc3;       (* arm_TRN1 Q3 Q30 Q3 64 128 *)
  0x3c9f006e;       (* arm_STR Q14 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e6d854a;       (* arm_SUB_VEC Q10 Q10 Q13 16 128 *)
  0x4f57c2ed;       (* arm_SQDMULH_VEC Q13 Q23 (Q7 :> LANE_H 1) 16 128 *)
  0x4e708464;       (* arm_ADD_VEC Q4 Q3 Q16 16 128 *)
  0x4e7b851e;       (* arm_ADD_VEC Q30 Q8 Q27 16 128 *)
  0x4f5cd955;       (* arm_SQRDMULH_VEC Q21 Q10 (Q12 :> LANE_H 5) 16 128 *)
  0x4f4c8946;       (* arm_MUL_VEC Q6 Q10 (Q12 :> LANE_H 4) 16 128 *)
  0x6e70846a;       (* arm_SUB_VEC Q10 Q3 Q16 16 128 *)
  0x4f7cd143;       (* arm_SQRDMULH_VEC Q3 Q10 (Q12 :> LANE_H 3) 16 128 *)
  0x4f6c8142;       (* arm_MUL_VEC Q2 Q10 (Q12 :> LANE_H 2) 16 128 *)
  0x4f1525ad;       (* arm_SRSHR_VEC Q13 Q13 11 16 128 *)
  0x4f57c08a;       (* arm_SQDMULH_VEC Q10 Q4 (Q7 :> LANE_H 1) 16 128 *)
  0x6f474062;       (* arm_MLS_VEC Q2 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742a6;       (* arm_MLS_VEC Q6 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741b7;       (* arm_MLS_VEC Q23 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f15254d;       (* arm_SRSHR_VEC Q13 Q10 11 16 128 *)
  0x4e749d2f;       (* arm_MUL_VEC Q15 Q9 Q20 16 128 *)
  0x4e66844b;       (* arm_ADD_VEC Q11 Q2 Q6 16 128 *)
  0x6f4741a4;       (* arm_MLS_VEC Q4 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e66844a;       (* arm_SUB_VEC Q10 Q2 Q6 16 128 *)
  0x4f57c16d;       (* arm_SQDMULH_VEC Q13 Q11 (Q7 :> LANE_H 1) 16 128 *)
  0x3dc01046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 64)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff5e4;       (* arm_CBNZ X4 (word 2096828) *)
  0x6f47424f;       (* arm_MLS_VEC Q15 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7c8674;       (* arm_ADD_VEC Q20 Q19 Q28 16 128 *)
  0x3cc60458;       (* arm_LDR Q24 X2 (Postimmediate_Offset (word 96)) *)
  0x4e669ca5;       (* arm_MUL_VEC Q5 Q5 Q6 16 128 *)
  0x6e7487d5;       (* arm_SUB_VEC Q21 Q30 Q20 16 128 *)
  0x3cdb0056;       (* arm_LDR Q22 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x6f4743e5;       (* arm_MLS_VEC Q5 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e789ebc;       (* arm_MUL_VEC Q28 Q21 Q24 16 128 *)
  0x6e76b6a6;       (* arm_SQRDMULH_VEC Q6 Q21 Q22 16 128 *)
  0x6e6585e3;       (* arm_SUB_VEC Q3 Q15 Q5 16 128 *)
  0x4f5cd159;       (* arm_SQRDMULH_VEC Q25 Q10 (Q12 :> LANE_H 1) 16 128 *)
  0x6e76b475;       (* arm_SQRDMULH_VEC Q21 Q3 Q22 16 128 *)
  0x4e789c73;       (* arm_MUL_VEC Q19 Q3 Q24 16 128 *)
  0x6f4740dc;       (* arm_MLS_VEC Q28 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6e77849f;       (* arm_SUB_VEC Q31 Q4 Q23 16 128 *)
  0x6f4742b3;       (* arm_MLS_VEC Q19 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7487c3;       (* arm_ADD_VEC Q3 Q30 Q20 16 128 *)
  0x4e6585f5;       (* arm_ADD_VEC Q21 Q15 Q5 16 128 *)
  0x4f1525af;       (* arm_SRSHR_VEC Q15 Q13 11 16 128 *)
  0x4f5cd3f4;       (* arm_SQRDMULH_VEC Q20 Q31 (Q12 :> LANE_H 1) 16 128 *)
  0x4e956866;       (* arm_TRN2 Q6 Q3 Q21 32 128 *)
  0x4e952865;       (* arm_TRN1 Q5 Q3 Q21 32 128 *)
  0x4f4c8152;       (* arm_MUL_VEC Q18 Q10 (Q12 :> LANE_H 0) 16 128 *)
  0x4e932b8d;       (* arm_TRN1 Q13 Q28 Q19 32 128 *)
  0x4e936b83;       (* arm_TRN2 Q3 Q28 Q19 32 128 *)
  0x4f4c83e1;       (* arm_MUL_VEC Q1 Q31 (Q12 :> LANE_H 0) 16 128 *)
  0x3cc10429;       (* arm_LDR Q9 X1 (Postimmediate_Offset (word 16)) *)
  0x4ecd68b5;       (* arm_TRN2 Q21 Q5 Q13 64 128 *)
  0x6f4741eb;       (* arm_MLS_VEC Q11 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec368ca;       (* arm_TRN2 Q10 Q6 Q3 64 128 *)
  0x4ecd28ad;       (* arm_TRN1 Q13 Q5 Q13 64 128 *)
  0x6f474332;       (* arm_MLS_VEC Q18 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6a86bf;       (* arm_SUB_VEC Q31 Q21 Q10 16 128 *)
  0x4ec328c3;       (* arm_TRN1 Q3 Q6 Q3 64 128 *)
  0x4e6a86b9;       (* arm_ADD_VEC Q25 Q21 Q10 16 128 *)
  0x4f59dbea;       (* arm_SQRDMULH_VEC Q10 Q31 (Q9 :> LANE_H 5) 16 128 *)
  0x6e6385b5;       (* arm_SUB_VEC Q21 Q13 Q3 16 128 *)
  0x4f57c33e;       (* arm_SQDMULH_VEC Q30 Q25 (Q7 :> LANE_H 1) 16 128 *)
  0x4e6385a5;       (* arm_ADD_VEC Q5 Q13 Q3 16 128 *)
  0x4f79d2af;       (* arm_SQRDMULH_VEC Q15 Q21 (Q9 :> LANE_H 3) 16 128 *)
  0x4f57c0ad;       (* arm_SQDMULH_VEC Q13 Q5 (Q7 :> LANE_H 1) 16 128 *)
  0x4f498be3;       (* arm_MUL_VEC Q3 Q31 (Q9 :> LANE_H 4) 16 128 *)
  0x6f474143;       (* arm_MLS_VEC Q3 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f1527ca;       (* arm_SRSHR_VEC Q10 Q30 11 16 128 *)
  0x4f1525ad;       (* arm_SRSHR_VEC Q13 Q13 11 16 128 *)
  0x4f6982bf;       (* arm_MUL_VEC Q31 Q21 (Q9 :> LANE_H 2) 16 128 *)
  0x6f4741ff;       (* arm_MLS_VEC Q31 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741a5;       (* arm_MLS_VEC Q5 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474159;       (* arm_MLS_VEC Q25 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6387fe;       (* arm_ADD_VEC Q30 Q31 Q3 16 128 *)
  0x6f474281;       (* arm_MLS_VEC Q1 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6387e3;       (* arm_SUB_VEC Q3 Q31 Q3 16 128 *)
  0x4f57c3ca;       (* arm_SQDMULH_VEC Q10 Q30 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7984ad;       (* arm_SUB_VEC Q13 Q5 Q25 16 128 *)
  0x4f59d075;       (* arm_SQRDMULH_VEC Q21 Q3 (Q9 :> LANE_H 1) 16 128 *)
  0x4f49806c;       (* arm_MUL_VEC Q12 Q3 (Q9 :> LANE_H 0) 16 128 *)
  0x4f152546;       (* arm_SRSHR_VEC Q6 Q10 11 16 128 *)
  0x4f59d1aa;       (* arm_SQRDMULH_VEC Q10 Q13 (Q9 :> LANE_H 1) 16 128 *)
  0x4f4981ad;       (* arm_MUL_VEC Q13 Q13 (Q9 :> LANE_H 0) 16 128 *)
  0x6f4740de;       (* arm_MLS_VEC Q30 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47414d;       (* arm_MLS_VEC Q13 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800861;       (* arm_STR Q1 X3 (Immediate_Offset (word 32)) *)
  0x6f4742ac;       (* arm_MLS_VEC Q12 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e778495;       (* arm_ADD_VEC Q21 Q4 Q23 16 128 *)
  0x4e7984aa;       (* arm_ADD_VEC Q10 Q5 Q25 16 128 *)
  0x3c840475;       (* arm_STR Q21 X3 (Postimmediate_Offset (word 64)) *)
  0x3d80047e;       (* arm_STR Q30 X3 (Immediate_Offset (word 16)) *)
  0x3d80086d;       (* arm_STR Q13 X3 (Immediate_Offset (word 32)) *)
  0x3c84046a;       (* arm_STR Q10 X3 (Postimmediate_Offset (word 64)) *)
  0x3c99006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551504)) *)
  0x3c9f006c;       (* arm_STR Q12 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9b0072;       (* arm_STR Q18 X3 (Immediate_Offset (word 18446744073709551536)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0501d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 320)) *)
  0x3dc04013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 256)) *)
  0x3dc06009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 384)) *)
  0x3dc0701c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 448)) *)
  0x3dc0300b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 192)) *)
  0x3dc0201f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 128)) *)
  0x3dc03403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 208)) *)
  0x3dc0100f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 64)) *)
  0x4e7d8674;       (* arm_ADD_VEC Q20 Q19 Q29 16 128 *)
  0x6e7d8672;       (* arm_SUB_VEC Q18 Q19 Q29 16 128 *)
  0x4e7c853b;       (* arm_ADD_VEC Q27 Q9 Q28 16 128 *)
  0x6e7c8531;       (* arm_SUB_VEC Q17 Q9 Q28 16 128 *)
  0x4f71d250;       (* arm_SQRDMULH_VEC Q16 Q18 (Q1 :> LANE_H 3) 16 128 *)
  0x6e6b87fa;       (* arm_SUB_VEC Q26 Q31 Q11 16 128 *)
  0x4e6b87ff;       (* arm_ADD_VEC Q31 Q31 Q11 16 128 *)
  0x3dc07418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 464)) *)
  0x4f51da37;       (* arm_SQRDMULH_VEC Q23 Q17 (Q1 :> LANE_H 5) 16 128 *)
  0x3dc06413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 400)) *)
  0x4e7b8689;       (* arm_ADD_VEC Q9 Q20 Q27 16 128 *)
  0x6e7b868e;       (* arm_SUB_VEC Q14 Q20 Q27 16 128 *)
  0x4f618256;       (* arm_MUL_VEC Q22 Q18 (Q1 :> LANE_H 2) 16 128 *)
  0x4f418a3d;       (* arm_MUL_VEC Q29 Q17 (Q1 :> LANE_H 4) 16 128 *)
  0x6f474216;       (* arm_MLS_VEC Q22 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742fd;       (* arm_MLS_VEC Q29 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f418350;       (* arm_MUL_VEC Q16 Q26 (Q1 :> LANE_H 0) 16 128 *)
  0x4f51d35c;       (* arm_SQRDMULH_VEC Q28 Q26 (Q1 :> LANE_H 1) 16 128 *)
  0x6e7d86c8;       (* arm_SUB_VEC Q8 Q22 Q29 16 128 *)
  0x4f50d90b;       (* arm_SQRDMULH_VEC Q11 Q8 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408917;       (* arm_MUL_VEC Q23 Q8 (Q0 :> LANE_H 4) 16 128 *)
  0x6f474177;       (* arm_MLS_VEC Q23 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6e788674;       (* arm_SUB_VEC Q20 Q19 Q24 16 128 *)
  0x4f50d9db;       (* arm_SQRDMULH_VEC Q27 Q14 (Q0 :> LANE_H 5) 16 128 *)
  0x3dc00008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 0)) *)
  0x4e7d86d5;       (* arm_ADD_VEC Q21 Q22 Q29 16 128 *)
  0x4f418a9d;       (* arm_MUL_VEC Q29 Q20 (Q1 :> LANE_H 4) 16 128 *)
  0x3dc0440d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 272)) *)
  0x4f51da8a;       (* arm_SQRDMULH_VEC Q10 Q20 (Q1 :> LANE_H 5) 16 128 *)
  0x3dc05402;       (* arm_LDR Q2 X0 (Immediate_Offset (word 336)) *)
  0x4f4089cb;       (* arm_MUL_VEC Q11 Q14 (Q0 :> LANE_H 4) 16 128 *)
  0x4e6f8514;       (* arm_ADD_VEC Q20 Q8 Q15 16 128 *)
  0x6f47436b;       (* arm_MLS_VEC Q11 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6285a4;       (* arm_SUB_VEC Q4 Q13 Q2 16 128 *)
  0x4e788678;       (* arm_ADD_VEC Q24 Q19 Q24 16 128 *)
  0x6e6f8506;       (* arm_SUB_VEC Q6 Q8 Q15 16 128 *)
  0x4f71d08e;       (* arm_SQRDMULH_VEC Q14 Q4 (Q1 :> LANE_H 3) 16 128 *)
  0x4e6285be;       (* arm_ADD_VEC Q30 Q13 Q2 16 128 *)
  0x3dc06813;       (* arm_LDR Q19 X0 (Immediate_Offset (word 416)) *)
  0x4f618096;       (* arm_MUL_VEC Q22 Q4 (Q1 :> LANE_H 2) 16 128 *)
  0x3dc0140f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 80)) *)
  0x4f70d8d1;       (* arm_SQRDMULH_VEC Q17 Q6 (Q0 :> LANE_H 7) 16 128 *)
  0x4e7f868d;       (* arm_ADD_VEC Q13 Q20 Q31 16 128 *)
  0x3dc02404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 144)) *)
  0x6f4741d6;       (* arm_MLS_VEC Q22 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6985b9;       (* arm_ADD_VEC Q25 Q13 Q9 16 128 *)
  0x6e6985a8;       (* arm_SUB_VEC Q8 Q13 Q9 16 128 *)
  0x6f47415d;       (* arm_MLS_VEC Q29 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7887ce;       (* arm_SUB_VEC Q14 Q30 Q24 16 128 *)
  0x4e7887c9;       (* arm_ADD_VEC Q9 Q30 Q24 16 128 *)
  0x3c810419;       (* arm_STR Q25 X0 (Postimmediate_Offset (word 16)) *)
  0x6f474390;       (* arm_MLS_VEC Q16 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc07418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 464)) *)
  0x6e63848d;       (* arm_SUB_VEC Q13 Q4 Q3 16 128 *)
  0x4f6088da;       (* arm_MUL_VEC Q26 Q6 (Q0 :> LANE_H 6) 16 128 *)
  0x6f47423a;       (* arm_MLS_VEC Q26 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7d86db;       (* arm_SUB_VEC Q27 Q22 Q29 16 128 *)
  0x4f51d1bc;       (* arm_SQRDMULH_VEC Q28 Q13 (Q1 :> LANE_H 1) 16 128 *)
  0x4f50db6a;       (* arm_SQRDMULH_VEC Q10 Q27 (Q0 :> LANE_H 5) 16 128 *)
  0x4e70875e;       (* arm_ADD_VEC Q30 Q26 Q16 16 128 *)
  0x4f408112;       (* arm_MUL_VEC Q18 Q8 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7587c5;       (* arm_SUB_VEC Q5 Q30 Q21 16 128 *)
  0x4e7587cc;       (* arm_ADD_VEC Q12 Q30 Q21 16 128 *)
  0x4f50d115;       (* arm_SQRDMULH_VEC Q21 Q8 (Q0 :> LANE_H 1) 16 128 *)
  0x6e708748;       (* arm_SUB_VEC Q8 Q26 Q16 16 128 *)
  0x4f4181b0;       (* arm_MUL_VEC Q16 Q13 (Q1 :> LANE_H 0) 16 128 *)
  0x6e7f868d;       (* arm_SUB_VEC Q13 Q20 Q31 16 128 *)
  0x4e63849f;       (* arm_ADD_VEC Q31 Q4 Q3 16 128 *)
  0x4f6081ba;       (* arm_MUL_VEC Q26 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x3d800c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 48)) *)
  0x4f70d1ad;       (* arm_SQRDMULH_VEC Q13 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608104;       (* arm_MUL_VEC Q4 Q8 (Q0 :> LANE_H 2) 16 128 *)
  0x4f70d108;       (* arm_SQRDMULH_VEC Q8 Q8 (Q0 :> LANE_H 3) 16 128 *)
  0x6f4741ba;       (* arm_MLS_VEC Q26 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742b2;       (* arm_MLS_VEC Q18 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474104;       (* arm_MLS_VEC Q4 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6b8754;       (* arm_SUB_VEC Q20 Q26 Q11 16 128 *)
  0x4f50d0a3;       (* arm_SQRDMULH_VEC Q3 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4e6b8746;       (* arm_ADD_VEC Q6 Q26 Q11 16 128 *)
  0x4f50d299;       (* arm_SQRDMULH_VEC Q25 Q20 (Q0 :> LANE_H 1) 16 128 *)
  0x3d803c12;       (* arm_STR Q18 X0 (Immediate_Offset (word 240)) *)
  0x6e778492;       (* arm_SUB_VEC Q18 Q4 Q23 16 128 *)
  0x4e77849a;       (* arm_ADD_VEC Q26 Q4 Q23 16 128 *)
  0x4f408297;       (* arm_MUL_VEC Q23 Q20 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d24b;       (* arm_SQRDMULH_VEC Q11 Q18 (Q0 :> LANE_H 1) 16 128 *)
  0x3d801c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 112)) *)
  0x6f474337;       (* arm_MLS_VEC Q23 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x3d802c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 176)) *)
  0x4f4080b1;       (* arm_MUL_VEC Q17 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x4f40825a;       (* arm_MUL_VEC Q26 Q18 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474071;       (* arm_MLS_VEC Q17 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
  0x6f47417a;       (* arm_MLS_VEC Q26 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc03403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 208)) *)
  0x4f408b77;       (* arm_MUL_VEC Q23 Q27 (Q0 :> LANE_H 4) 16 128 *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 304)) *)
  0x3d806c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 432)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6f474390;       (* arm_MLS_VEC Q16 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e78867b;       (* arm_SUB_VEC Q27 Q19 Q24 16 128 *)
  0x4e7d86cc;       (* arm_ADD_VEC Q12 Q22 Q29 16 128 *)
  0x3dc00002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 0)) *)
  0x3dc0140a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 80)) *)
  0x4f4089dc;       (* arm_MUL_VEC Q28 Q14 (Q0 :> LANE_H 4) 16 128 *)
  0x3dc02416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 144)) *)
  0x4e788675;       (* arm_ADD_VEC Q21 Q19 Q24 16 128 *)
  0x3dc00412;       (* arm_LDR Q18 X0 (Immediate_Offset (word 16)) *)
  0x4f50d9dd;       (* arm_SQRDMULH_VEC Q29 Q14 (Q0 :> LANE_H 5) 16 128 *)
  0x4e6f8458;       (* arm_ADD_VEC Q24 Q2 Q15 16 128 *)
  0x3dc04405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 272)) *)
  0x6e6f845a;       (* arm_SUB_VEC Q26 Q2 Q15 16 128 *)
  0x4f51db71;       (* arm_SQRDMULH_VEC Q17 Q27 (Q1 :> LANE_H 5) 16 128 *)
  0x4e6386de;       (* arm_ADD_VEC Q30 Q22 Q3 16 128 *)
  0x6e6386c4;       (* arm_SUB_VEC Q4 Q22 Q3 16 128 *)
  0x4f70db46;       (* arm_SQRDMULH_VEC Q6 Q26 (Q0 :> LANE_H 7) 16 128 *)
  0x4e7f8719;       (* arm_ADD_VEC Q25 Q24 Q31 16 128 *)
  0x3dc05403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 336)) *)
  0x6e7f8716;       (* arm_SUB_VEC Q22 Q24 Q31 16 128 *)
  0x4f608b4b;       (* arm_MUL_VEC Q11 Q26 (Q0 :> LANE_H 6) 16 128 *)
  0x4e69872d;       (* arm_ADD_VEC Q13 Q25 Q9 16 128 *)
  0x6f4743bc;       (* arm_MLS_VEC Q28 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6e698738;       (* arm_SUB_VEC Q24 Q25 Q9 16 128 *)
  0x3c81040d;       (* arm_STR Q13 X0 (Postimmediate_Offset (word 16)) *)
  0x4e6a864d;       (* arm_ADD_VEC Q13 Q18 Q10 16 128 *)
  0x6e6a8652;       (* arm_SUB_VEC Q18 Q18 Q10 16 128 *)
  0x6f4740cb;       (* arm_MLS_VEC Q11 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6384b3;       (* arm_ADD_VEC Q19 Q5 Q3 16 128 *)
  0x4f51d08a;       (* arm_SQRDMULH_VEC Q10 Q4 (Q1 :> LANE_H 1) 16 128 *)
  0x6e7e85b4;       (* arm_SUB_VEC Q20 Q13 Q30 16 128 *)
  0x6e75867f;       (* arm_SUB_VEC Q31 Q19 Q21 16 128 *)
  0x4e75866e;       (* arm_ADD_VEC Q14 Q19 Q21 16 128 *)
  0x4f70da49;       (* arm_SQRDMULH_VEC Q9 Q18 (Q0 :> LANE_H 7) 16 128 *)
  0x4e7e85a6;       (* arm_ADD_VEC Q6 Q13 Q30 16 128 *)
  0x6e6384b5;       (* arm_SUB_VEC Q21 Q5 Q3 16 128 *)
  0x4f418b63;       (* arm_MUL_VEC Q3 Q27 (Q1 :> LANE_H 4) 16 128 *)
  0x6e6e84c5;       (* arm_SUB_VEC Q5 Q6 Q14 16 128 *)
  0x6f474223;       (* arm_MLS_VEC Q3 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6e70857a;       (* arm_SUB_VEC Q26 Q11 Q16 16 128 *)
  0x4e708570;       (* arm_ADD_VEC Q16 Q11 Q16 16 128 *)
  0x4e6e84de;       (* arm_ADD_VEC Q30 Q6 Q14 16 128 *)
  0x4f70d35b;       (* arm_SQRDMULH_VEC Q27 Q26 (Q0 :> LANE_H 3) 16 128 *)
  0x4e6c860b;       (* arm_ADD_VEC Q11 Q16 Q12 16 128 *)
  0x6e6c8608;       (* arm_SUB_VEC Q8 Q16 Q12 16 128 *)
  0x4f608350;       (* arm_MUL_VEC Q16 Q26 (Q0 :> LANE_H 2) 16 128 *)
  0x3d800c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 48)) *)
  0x3c81041e;       (* arm_STR Q30 X0 (Postimmediate_Offset (word 16)) *)
  0x4f41809a;       (* arm_MUL_VEC Q26 Q4 (Q1 :> LANE_H 0) 16 128 *)
  0x6f474370;       (* arm_MLS_VEC Q16 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40811e;       (* arm_MUL_VEC Q30 Q8 (Q0 :> LANE_H 0) 16 128 *)
  0x4f40831d;       (* arm_MUL_VEC Q29 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x6e778619;       (* arm_SUB_VEC Q25 Q16 Q23 16 128 *)
  0x4e77860b;       (* arm_ADD_VEC Q11 Q16 Q23 16 128 *)
  0x4f6082db;       (* arm_MUL_VEC Q27 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x4f70d2d6;       (* arm_SQRDMULH_VEC Q22 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x3d80280b;       (* arm_STR Q11 X0 (Immediate_Offset (word 160)) *)
  0x6f47415a;       (* arm_MLS_VEC Q26 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408bf1;       (* arm_MUL_VEC Q17 Q31 (Q0 :> LANE_H 4) 16 128 *)
  0x4f70d28a;       (* arm_SQRDMULH_VEC Q10 Q20 (Q0 :> LANE_H 3) 16 128 *)
  0x4f50dbed;       (* arm_SQRDMULH_VEC Q13 Q31 (Q0 :> LANE_H 5) 16 128 *)
  0x4f60828e;       (* arm_MUL_VEC Q14 Q20 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50d30c;       (* arm_SQRDMULH_VEC Q12 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4741b1;       (* arm_MLS_VEC Q17 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d2b4;       (* arm_SQRDMULH_VEC Q20 Q21 (Q1 :> LANE_H 3) 16 128 *)
  0x4f50d0ad;       (* arm_SQRDMULH_VEC Q13 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4f608a52;       (* arm_MUL_VEC Q18 Q18 (Q0 :> LANE_H 6) 16 128 *)
  0x4f6182bf;       (* arm_MUL_VEC Q31 Q21 (Q1 :> LANE_H 2) 16 128 *)
  0x4f4080af;       (* arm_MUL_VEC Q15 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47414e;       (* arm_MLS_VEC Q14 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474132;       (* arm_MLS_VEC Q18 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408324;       (* arm_MUL_VEC Q4 Q25 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7185c5;       (* arm_ADD_VEC Q5 Q14 Q17 16 128 *)
  0x6f4742db;       (* arm_MLS_VEC Q27 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7185c9;       (* arm_SUB_VEC Q9 Q14 Q17 16 128 *)
  0x3d801c05;       (* arm_STR Q5 X0 (Immediate_Offset (word 112)) *)
  0x6f47429f;       (* arm_MLS_VEC Q31 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a8651;       (* arm_SUB_VEC Q17 Q18 Q26 16 128 *)
  0x4e7a8655;       (* arm_ADD_VEC Q21 Q18 Q26 16 128 *)
  0x4f50d132;       (* arm_SQRDMULH_VEC Q18 Q9 (Q0 :> LANE_H 1) 16 128 *)
  0x4e7c8765;       (* arm_ADD_VEC Q5 Q27 Q28 16 128 *)
  0x4f70d22a;       (* arm_SQRDMULH_VEC Q10 Q17 (Q0 :> LANE_H 3) 16 128 *)
  0x6e7c8770;       (* arm_SUB_VEC Q16 Q27 Q28 16 128 *)
  0x3d801805;       (* arm_STR Q5 X0 (Immediate_Offset (word 96)) *)
  0x4e6387f7;       (* arm_ADD_VEC Q23 Q31 Q3 16 128 *)
  0x6e6387fa;       (* arm_SUB_VEC Q26 Q31 Q3 16 128 *)
  0x4f50d205;       (* arm_SQRDMULH_VEC Q5 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x4e7786a3;       (* arm_ADD_VEC Q3 Q21 Q23 16 128 *)
  0x4f50d326;       (* arm_SQRDMULH_VEC Q6 Q25 (Q0 :> LANE_H 1) 16 128 *)
  0x3d800c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 48)) *)
  0x4f50d114;       (* arm_SQRDMULH_VEC Q20 Q8 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408213;       (* arm_MUL_VEC Q19 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x4f408b48;       (* arm_MUL_VEC Q8 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x6e7786b5;       (* arm_SUB_VEC Q21 Q21 Q23 16 128 *)
  0x4f608223;       (* arm_MUL_VEC Q3 Q17 (Q0 :> LANE_H 2) 16 128 *)
  0x4f4082ae;       (* arm_MUL_VEC Q14 Q21 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50db51;       (* arm_SQRDMULH_VEC Q17 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x6f474143;       (* arm_MLS_VEC Q3 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408130;       (* arm_MUL_VEC Q16 Q9 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474228;       (* arm_MLS_VEC Q8 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47419d;       (* arm_MLS_VEC Q29 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474250;       (* arm_MLS_VEC Q16 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47429e;       (* arm_MLS_VEC Q30 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d2b7;       (* arm_SQRDMULH_VEC Q23 Q21 (Q0 :> LANE_H 1) 16 128 *)
  0x4e688475;       (* arm_ADD_VEC Q21 Q3 Q8 16 128 *)
  0x6f4740c4;       (* arm_MLS_VEC Q4 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x3d802c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 176)) *)
  0x3d80481e;       (* arm_STR Q30 X0 (Immediate_Offset (word 288)) *)
  0x6f4740b3;       (* arm_MLS_VEC Q19 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6e68846a;       (* arm_SUB_VEC Q10 Q3 Q8 16 128 *)
  0x6f4742ee;       (* arm_MLS_VEC Q14 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x3d806804;       (* arm_STR Q4 X0 (Immediate_Offset (word 416)) *)
  0x3d80381d;       (* arm_STR Q29 X0 (Immediate_Offset (word 224)) *)
  0x4f50d155;       (* arm_SQRDMULH_VEC Q21 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x3d805c10;       (* arm_STR Q16 X0 (Immediate_Offset (word 368)) *)
  0x3d805813;       (* arm_STR Q19 X0 (Immediate_Offset (word 352)) *)
  0x6f4741af;       (* arm_MLS_VEC Q15 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 304)) *)
  0x4f40814a;       (* arm_MUL_VEC Q10 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4742aa;       (* arm_MLS_VEC Q10 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3d803c0f;       (* arm_STR Q15 X0 (Immediate_Offset (word 240)) *)
  0x3d806c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 432)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

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
          [(word pc,0x828); (z_12345,160); (z_67,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                intt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x810) /\
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
            (1--1153) THEN
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
       [(word pc,0x828); (z_12345,160); (z_67,768)] /\
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
