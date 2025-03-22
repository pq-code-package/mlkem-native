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
     0xaa0003e3;       (* arm_MOV X3 X0 *)
     0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
     0x3dc0006b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 0)) *)
     0x3dc0046a;       (* arm_LDR Q10 X3 (Immediate_Offset (word 16)) *)
     0x3dc00c71;       (* arm_LDR Q17 X3 (Immediate_Offset (word 48)) *)
     0x3dc00875;       (* arm_LDR Q21 X3 (Immediate_Offset (word 32)) *)
     0x4e8a6963;       (* arm_TRN2 Q3 Q11 Q10 32 128 *)
     0x4e8a296a;       (* arm_TRN1 Q10 Q11 Q10 32 128 *)
     0x4e912abb;       (* arm_TRN1 Q27 Q21 Q17 32 128 *)
     0x3dc0144d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 80)) *)
     0x4edb6946;       (* arm_TRN2 Q6 Q10 Q27 64 128 *)
     0x4e916aa9;       (* arm_TRN2 Q9 Q21 Q17 32 128 *)
     0x4edb2958;       (* arm_TRN1 Q24 Q10 Q27 64 128 *)
     0x3dc00855;       (* arm_LDR Q21 X2 (Immediate_Offset (word 32)) *)
     0x4ec92874;       (* arm_TRN1 Q20 Q3 Q9 64 128 *)
     0x4ec9686c;       (* arm_TRN2 Q12 Q3 Q9 64 128 *)
     0x6e748701;       (* arm_SUB_VEC Q1 Q24 Q20 16 128 *)
     0x6e6c84c3;       (* arm_SUB_VEC Q3 Q6 Q12 16 128 *)
     0x3dc00c5b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 48)) *)
     0x3dc0105e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 64)) *)
     0x6e7bb42a;       (* arm_SQRDMULH_VEC Q10 Q1 Q27 16 128 *)
     0x6e6db46d;       (* arm_SQRDMULH_VEC Q13 Q3 Q13 16 128 *)
     0x4e7e9c6e;       (* arm_MUL_VEC Q14 Q3 Q30 16 128 *)
     0x4e759c2b;       (* arm_MUL_VEC Q11 Q1 Q21 16 128 *)
     0x4e6c84d5;       (* arm_ADD_VEC Q21 Q6 Q12 16 128 *)
     0x4e748701;       (* arm_ADD_VEC Q1 Q24 Q20 16 128 *)
     0x6f4741ae;       (* arm_MLS_VEC Q14 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x6f47414b;       (* arm_MLS_VEC Q11 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x3cc6044a;       (* arm_LDR Q10 X2 (Postimmediate_Offset (word 96)) *)
     0x6e758434;       (* arm_SUB_VEC Q20 Q1 Q21 16 128 *)
     0x6e6e857d;       (* arm_SUB_VEC Q29 Q11 Q14 16 128 *)
     0x3cdb0059;       (* arm_LDR Q25 X2 (Immediate_Offset (word 18446744073709551536)) *)
     0x4e6a9fbb;       (* arm_MUL_VEC Q27 Q29 Q10 16 128 *)
     0x4e6a9e90;       (* arm_MUL_VEC Q16 Q20 Q10 16 128 *)
     0x6e79b7ad;       (* arm_SQRDMULH_VEC Q13 Q29 Q25 16 128 *)
     0x6e79b68a;       (* arm_SQRDMULH_VEC Q10 Q20 Q25 16 128 *)
     0x4e758425;       (* arm_ADD_VEC Q5 Q1 Q21 16 128 *)
     0x4e6e857f;       (* arm_ADD_VEC Q31 Q11 Q14 16 128 *)
     0x6f4741bb;       (* arm_MLS_VEC Q27 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474150;       (* arm_MLS_VEC Q16 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x3cc1042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 16)) *)
     0x4e9f68b5;       (* arm_TRN2 Q21 Q5 Q31 32 128 *)
     0x4e9b6a0a;       (* arm_TRN2 Q10 Q16 Q27 32 128 *)
     0x4e9b2a06;       (* arm_TRN1 Q6 Q16 Q27 32 128 *)
     0x4e9f28a5;       (* arm_TRN1 Q5 Q5 Q31 32 128 *)
     0x4eca2aad;       (* arm_TRN1 Q13 Q21 Q10 64 128 *)
     0x4eca6ab5;       (* arm_TRN2 Q21 Q21 Q10 64 128 *)
     0x4ec668aa;       (* arm_TRN2 Q10 Q5 Q6 64 128 *)
     0x4ec628a6;       (* arm_TRN1 Q6 Q5 Q6 64 128 *)
     0x4e75855d;       (* arm_ADD_VEC Q29 Q10 Q21 16 128 *)
     0x4e6d84c0;       (* arm_ADD_VEC Q0 Q6 Q13 16 128 *)
     0x6e6d84c3;       (* arm_SUB_VEC Q3 Q6 Q13 16 128 *)
     0x4f57c3ad;       (* arm_SQDMULH_VEC Q13 Q29 (Q7 :> LANE_H 1) 16 128 *)
     0x4f57c01e;       (* arm_SQDMULH_VEC Q30 Q0 (Q7 :> LANE_H 1) 16 128 *)
     0x6e75854c;       (* arm_SUB_VEC Q12 Q10 Q21 16 128 *)
     0x4f6b8068;       (* arm_MUL_VEC Q8 Q3 (Q11 :> LANE_H 2) 16 128 *)
     0x4f1525ad;       (* arm_SRSHR_VEC Q13 Q13 11 16 128 *)
     0x4f1527c4;       (* arm_SRSHR_VEC Q4 Q30 11 16 128 *)
     0x4f7bd07c;       (* arm_SQRDMULH_VEC Q28 Q3 (Q11 :> LANE_H 3) 16 128 *)
     0x6f4741bd;       (* arm_MLS_VEC Q29 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474080;       (* arm_MLS_VEC Q0 Q4 (Q7 :> LANE_H 0) 16 128 *)
     0x4f5bd98a;       (* arm_SQRDMULH_VEC Q10 Q12 (Q11 :> LANE_H 5) 16 128 *)
     0x4f4b899b;       (* arm_MUL_VEC Q27 Q12 (Q11 :> LANE_H 4) 16 128 *)
     0x6f474388;       (* arm_MLS_VEC Q8 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x6e7d8402;       (* arm_SUB_VEC Q2 Q0 Q29 16 128 *)
     0x4e7d840d;       (* arm_ADD_VEC Q13 Q0 Q29 16 128 *)
     0x6f47415b;       (* arm_MLS_VEC Q27 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x4f4b8057;       (* arm_MUL_VEC Q23 Q2 (Q11 :> LANE_H 0) 16 128 *)
     0x4f5bd050;       (* arm_SQRDMULH_VEC Q16 Q2 (Q11 :> LANE_H 1) 16 128 *)
     0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
     0x6e7b851a;       (* arm_SUB_VEC Q26 Q8 Q27 16 128 *)
     0x4e7b8511;       (* arm_ADD_VEC Q17 Q8 Q27 16 128 *)
     0x6f474217;       (* arm_MLS_VEC Q23 Q16 (Q7 :> LANE_H 0) 16 128 *)
     0x4f4b8348;       (* arm_MUL_VEC Q8 Q26 (Q11 :> LANE_H 0) 16 128 *)
     0x4f5bd356;       (* arm_SQRDMULH_VEC Q22 Q26 (Q11 :> LANE_H 1) 16 128 *)
     0x4f57c233;       (* arm_SQDMULH_VEC Q19 Q17 (Q7 :> LANE_H 1) 16 128 *)
     0x3d800877;       (* arm_STR Q23 X3 (Immediate_Offset (word 32)) *)
     0x3dc01074;       (* arm_LDR Q20 X3 (Immediate_Offset (word 64)) *)
     0x4f15266a;       (* arm_SRSHR_VEC Q10 Q19 11 16 128 *)
     0x3dc01465;       (* arm_LDR Q5 X3 (Immediate_Offset (word 80)) *)
     0x6f474151;       (* arm_MLS_VEC Q17 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x3dc01877;       (* arm_LDR Q23 X3 (Immediate_Offset (word 96)) *)
     0x3dc01c6b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 112)) *)
     0x4e856a89;       (* arm_TRN2 Q9 Q20 Q5 32 128 *)
     0x4e852a9b;       (* arm_TRN1 Q27 Q20 Q5 32 128 *)
     0x4e8b6ae6;       (* arm_TRN2 Q6 Q23 Q11 32 128 *)
     0x4e8b2aef;       (* arm_TRN1 Q15 Q23 Q11 32 128 *)
     0x3dc0105a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 64)) *)
     0x4ecf6b70;       (* arm_TRN2 Q16 Q27 Q15 64 128 *)
     0x4ecf2b64;       (* arm_TRN1 Q4 Q27 Q15 64 128 *)
     0x4ec66923;       (* arm_TRN2 Q3 Q9 Q6 64 128 *)
     0x4ec62935;       (* arm_TRN1 Q21 Q9 Q6 64 128 *)
     0x6e63861b;       (* arm_SUB_VEC Q27 Q16 Q3 16 128 *)
     0x6e758486;       (* arm_SUB_VEC Q6 Q4 Q21 16 128 *)
     0x3dc0085d;       (* arm_LDR Q29 X2 (Immediate_Offset (word 32)) *)
     0x3dc00c53;       (* arm_LDR Q19 X2 (Immediate_Offset (word 48)) *)
     0x3dc0144c;       (* arm_LDR Q12 X2 (Immediate_Offset (word 80)) *)
     0x3d800471;       (* arm_STR Q17 X3 (Immediate_Offset (word 16)) *)
     0x6e73b4d3;       (* arm_SQRDMULH_VEC Q19 Q6 Q19 16 128 *)
     0x6e6cb762;       (* arm_SQRDMULH_VEC Q2 Q27 Q12 16 128 *)
     0x4e7a9f69;       (* arm_MUL_VEC Q9 Q27 Q26 16 128 *)
     0x4e7d9cda;       (* arm_MUL_VEC Q26 Q6 Q29 16 128 *)
     0x4e638612;       (* arm_ADD_VEC Q18 Q16 Q3 16 128 *)
     0x4e75849d;       (* arm_ADD_VEC Q29 Q4 Q21 16 128 *)
     0x6f474049;       (* arm_MLS_VEC Q9 Q2 (Q7 :> LANE_H 0) 16 128 *)
     0x6f47427a;       (* arm_MLS_VEC Q26 Q19 (Q7 :> LANE_H 0) 16 128 *)
     0x3dc00440;       (* arm_LDR Q0 X2 (Immediate_Offset (word 16)) *)
     0x3cc6044b;       (* arm_LDR Q11 X2 (Postimmediate_Offset (word 96)) *)
     0x6e7287b8;       (* arm_SUB_VEC Q24 Q29 Q18 16 128 *)
     0x6e69875e;       (* arm_SUB_VEC Q30 Q26 Q9 16 128 *)
     0x4e7287aa;       (* arm_ADD_VEC Q10 Q29 Q18 16 128 *)
     0x6e60b702;       (* arm_SQRDMULH_VEC Q2 Q24 Q0 16 128 *)
     0x4e6b9f12;       (* arm_MUL_VEC Q18 Q24 Q11 16 128 *)
     0x4e6b9fd0;       (* arm_MUL_VEC Q16 Q30 Q11 16 128 *)
     0x6e60b7d9;       (* arm_SQRDMULH_VEC Q25 Q30 Q0 16 128 *)
     0x4e69874c;       (* arm_ADD_VEC Q12 Q26 Q9 16 128 *)
     0x6f474052;       (* arm_MLS_VEC Q18 Q2 (Q7 :> LANE_H 0) 16 128 *)
     0x3cc1042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 16)) *)
     0x6f474330;       (* arm_MLS_VEC Q16 Q25 (Q7 :> LANE_H 0) 16 128 *)
     0x4e8c695a;       (* arm_TRN2 Q26 Q10 Q12 32 128 *)
     0x6f4742c8;       (* arm_MLS_VEC Q8 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x4e8c2945;       (* arm_TRN1 Q5 Q10 Q12 32 128 *)
     0x4e906a58;       (* arm_TRN2 Q24 Q18 Q16 32 128 *)
     0x4e902a59;       (* arm_TRN1 Q25 Q18 Q16 32 128 *)
     0x3d800c68;       (* arm_STR Q8 X3 (Immediate_Offset (word 48)) *)
     0x4ed86b44;       (* arm_TRN2 Q4 Q26 Q24 64 128 *)
     0x4ed82b5e;       (* arm_TRN1 Q30 Q26 Q24 64 128 *)
     0x4ed968b4;       (* arm_TRN2 Q20 Q5 Q25 64 128 *)
     0x4ed928a3;       (* arm_TRN1 Q3 Q5 Q25 64 128 *)
     0x4e648685;       (* arm_ADD_VEC Q5 Q20 Q4 16 128 *)
     0x4e7e8460;       (* arm_ADD_VEC Q0 Q3 Q30 16 128 *)
     0x6e64868f;       (* arm_SUB_VEC Q15 Q20 Q4 16 128 *)
     0x4f57c0a1;       (* arm_SQDMULH_VEC Q1 Q5 (Q7 :> LANE_H 1) 16 128 *)
     0x4f57c018;       (* arm_SQDMULH_VEC Q24 Q0 (Q7 :> LANE_H 1) 16 128 *)
     0x6e7e8472;       (* arm_SUB_VEC Q18 Q3 Q30 16 128 *)
     0x4f5bd9f1;       (* arm_SQRDMULH_VEC Q17 Q15 (Q11 :> LANE_H 5) 16 128 *)
     0x4f152430;       (* arm_SRSHR_VEC Q16 Q1 11 16 128 *)
     0x4f15271d;       (* arm_SRSHR_VEC Q29 Q24 11 16 128 *)
     0x4f6b8248;       (* arm_MUL_VEC Q8 Q18 (Q11 :> LANE_H 2) 16 128 *)
     0x6f474205;       (* arm_MLS_VEC Q5 Q16 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4743a0;       (* arm_MLS_VEC Q0 Q29 (Q7 :> LANE_H 0) 16 128 *)
     0x4f7bd244;       (* arm_SQRDMULH_VEC Q4 Q18 (Q11 :> LANE_H 3) 16 128 *)
     0x4f4b89fb;       (* arm_MUL_VEC Q27 Q15 (Q11 :> LANE_H 4) 16 128 *)
     0x3c84046d;       (* arm_STR Q13 X3 (Postimmediate_Offset (word 64)) *)
     0x6e65841d;       (* arm_SUB_VEC Q29 Q0 Q5 16 128 *)
     0x6f474088;       (* arm_MLS_VEC Q8 Q4 (Q7 :> LANE_H 0) 16 128 *)
     0x6f47423b;       (* arm_MLS_VEC Q27 Q17 (Q7 :> LANE_H 0) 16 128 *)
     0x4f5bd3b0;       (* arm_SQRDMULH_VEC Q16 Q29 (Q11 :> LANE_H 1) 16 128 *)
     0x4f4b83b7;       (* arm_MUL_VEC Q23 Q29 (Q11 :> LANE_H 0) 16 128 *)
     0x4e65840d;       (* arm_ADD_VEC Q13 Q0 Q5 16 128 *)
     0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
     0xb5fff5e4;       (* arm_CBNZ X4 (word 2096828) *)
     0x6e7b8512;       (* arm_SUB_VEC Q18 Q8 Q27 16 128 *)
     0x4e7b8500;       (* arm_ADD_VEC Q0 Q8 Q27 16 128 *)
     0x6f474217;       (* arm_MLS_VEC Q23 Q16 (Q7 :> LANE_H 0) 16 128 *)
     0x4f4b825b;       (* arm_MUL_VEC Q27 Q18 (Q11 :> LANE_H 0) 16 128 *)
     0x4f57c008;       (* arm_SQDMULH_VEC Q8 Q0 (Q7 :> LANE_H 1) 16 128 *)
     0x4f5bd25a;       (* arm_SQRDMULH_VEC Q26 Q18 (Q11 :> LANE_H 1) 16 128 *)
     0x3c84046d;       (* arm_STR Q13 X3 (Postimmediate_Offset (word 64)) *)
     0x4f152510;       (* arm_SRSHR_VEC Q16 Q8 11 16 128 *)
     0x6f47435b;       (* arm_MLS_VEC Q27 Q26 (Q7 :> LANE_H 0) 16 128 *)
     0x3c9e0077;       (* arm_STR Q23 X3 (Immediate_Offset (word 18446744073709551584)) *)
     0x6f474200;       (* arm_MLS_VEC Q0 Q16 (Q7 :> LANE_H 0) 16 128 *)
     0x3c9f007b;       (* arm_STR Q27 X3 (Immediate_Offset (word 18446744073709551600)) *)
     0x3c9d0060;       (* arm_STR Q0 X3 (Immediate_Offset (word 18446744073709551568)) *)
     0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
     0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
     0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
     0x52804005;       (* arm_MOV W5 (rvalue (word 512)) *)
     0x4e020cbd;       (* arm_DUP_GEN Q29 X5 16 128 *)
     0x52827605;       (* arm_MOV W5 (rvalue (word 5040)) *)
     0x4e020cbe;       (* arm_DUP_GEN Q30 X5 16 128 *)
     0x3dc0301f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 192)) *)
     0x3dc02015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 128)) *)
     0x3dc0400c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 256)) *)
     0x6e7f86ad;       (* arm_SUB_VEC Q13 Q21 Q31 16 128 *)
     0x3dc06009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 384)) *)
     0x4f4181bb;       (* arm_MUL_VEC Q27 Q13 (Q1 :> LANE_H 0) 16 128 *)
     0x3dc05003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 320)) *)
     0x3dc0700a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 448)) *)
     0x4e63858f;       (* arm_ADD_VEC Q15 Q12 Q3 16 128 *)
     0x6e63859c;       (* arm_SUB_VEC Q28 Q12 Q3 16 128 *)
     0x4e6a8526;       (* arm_ADD_VEC Q6 Q9 Q10 16 128 *)
     0x3dc01005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 64)) *)
     0x6e6685e3;       (* arm_SUB_VEC Q3 Q15 Q6 16 128 *)
     0x6e6a852a;       (* arm_SUB_VEC Q10 Q9 Q10 16 128 *)
     0x4e7f86bf;       (* arm_ADD_VEC Q31 Q21 Q31 16 128 *)
     0x4f50d86c;       (* arm_SQRDMULH_VEC Q12 Q3 (Q0 :> LANE_H 5) 16 128 *)
     0x4f408873;       (* arm_MUL_VEC Q19 Q3 (Q0 :> LANE_H 4) 16 128 *)
     0x4f418958;       (* arm_MUL_VEC Q24 Q10 (Q1 :> LANE_H 4) 16 128 *)
     0x3dc00003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 0)) *)
     0x4f51d94a;       (* arm_SQRDMULH_VEC Q10 Q10 (Q1 :> LANE_H 5) 16 128 *)
     0x4f51d1b5;       (* arm_SQRDMULH_VEC Q21 Q13 (Q1 :> LANE_H 1) 16 128 *)
     0x6f474193;       (* arm_MLS_VEC Q19 Q12 (Q7 :> LANE_H 0) 16 128 *)
     0x6e65846d;       (* arm_SUB_VEC Q13 Q3 Q5 16 128 *)
     0x6f474158;       (* arm_MLS_VEC Q24 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4742bb;       (* arm_MLS_VEC Q27 Q21 (Q7 :> LANE_H 0) 16 128 *)
     0x4f70d9b5;       (* arm_SQRDMULH_VEC Q21 Q13 (Q0 :> LANE_H 7) 16 128 *)
     0x4e65846c;       (* arm_ADD_VEC Q12 Q3 Q5 16 128 *)
     0x4f6089a9;       (* arm_MUL_VEC Q9 Q13 (Q0 :> LANE_H 6) 16 128 *)
     0x4e6685ea;       (* arm_ADD_VEC Q10 Q15 Q6 16 128 *)
     0x4e7f858d;       (* arm_ADD_VEC Q13 Q12 Q31 16 128 *)
     0x3dc04414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 272)) *)
     0x6f4742a9;       (* arm_MLS_VEC Q9 Q21 (Q7 :> LANE_H 0) 16 128 *)
     0x4e6a85a5;       (* arm_ADD_VEC Q5 Q13 Q10 16 128 *)
     0x3dc06419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 400)) *)
     0x6e7eb4b6;       (* arm_SQRDMULH_VEC Q22 Q5 Q30 16 128 *)
     0x4f61838f;       (* arm_MUL_VEC Q15 Q28 (Q1 :> LANE_H 2) 16 128 *)
     0x6e6a85a3;       (* arm_SUB_VEC Q3 Q13 Q10 16 128 *)
     0x4f71d38a;       (* arm_SQRDMULH_VEC Q10 Q28 (Q1 :> LANE_H 3) 16 128 *)
     0x6e7b8526;       (* arm_SUB_VEC Q6 Q9 Q27 16 128 *)
     0x6e7f858d;       (* arm_SUB_VEC Q13 Q12 Q31 16 128 *)
     0x4f618870;       (* arm_MUL_VEC Q16 Q3 (Q1 :> LANE_H 6) 16 128 *)
     0x6f47414f;       (* arm_MLS_VEC Q15 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x4f70d1aa;       (* arm_SQRDMULH_VEC Q10 Q13 (Q0 :> LANE_H 3) 16 128 *)
     0x4f6081bf;       (* arm_MUL_VEC Q31 Q13 (Q0 :> LANE_H 2) 16 128 *)
     0x4e7b8529;       (* arm_ADD_VEC Q9 Q9 Q27 16 128 *)
     0x4e7885ec;       (* arm_ADD_VEC Q12 Q15 Q24 16 128 *)
     0x3dc0540d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 336)) *)
     0x6f47415f;       (* arm_MLS_VEC Q31 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x6e7885ea;       (* arm_SUB_VEC Q10 Q15 Q24 16 128 *)
     0x4e6d868e;       (* arm_ADD_VEC Q14 Q20 Q13 16 128 *)
     0x6e6d869c;       (* arm_SUB_VEC Q28 Q20 Q13 16 128 *)
     0x6e7387ed;       (* arm_SUB_VEC Q13 Q31 Q19 16 128 *)
     0x4e7387f4;       (* arm_ADD_VEC Q20 Q31 Q19 16 128 *)
     0x4f71d87b;       (* arm_SQRDMULH_VEC Q27 Q3 (Q1 :> LANE_H 7) 16 128 *)
     0x4f408948;       (* arm_MUL_VEC Q8 Q10 (Q0 :> LANE_H 4) 16 128 *)
     0x4f50d94a;       (* arm_SQRDMULH_VEC Q10 Q10 (Q0 :> LANE_H 5) 16 128 *)
     0x4e6c8538;       (* arm_ADD_VEC Q24 Q9 Q12 16 128 *)
     0x3dc07417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 464)) *)
     0x3dc0141f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 80)) *)
     0x4e77872b;       (* arm_ADD_VEC Q11 Q25 Q23 16 128 *)
     0x4f6080d1;       (* arm_MUL_VEC Q17 Q6 (Q0 :> LANE_H 2) 16 128 *)
     0x6f474148;       (* arm_MLS_VEC Q8 Q10 (Q7 :> LANE_H 0) 16 128 *)
     0x3dc03415;       (* arm_LDR Q21 X0 (Immediate_Offset (word 208)) *)
     0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
     0x6e6b85c3;       (* arm_SUB_VEC Q3 Q14 Q11 16 128 *)
     0x3dc0240a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 144)) *)
     0x4f50d862;       (* arm_SQRDMULH_VEC Q2 Q3 (Q0 :> LANE_H 5) 16 128 *)
     0x4f408872;       (* arm_MUL_VEC Q18 Q3 (Q0 :> LANE_H 4) 16 128 *)
     0x6e778723;       (* arm_SUB_VEC Q3 Q25 Q23 16 128 *)
     0x6e75855a;       (* arm_SUB_VEC Q26 Q10 Q21 16 128 *)
     0x4e758557;       (* arm_ADD_VEC Q23 Q10 Q21 16 128 *)
     0x6f474370;       (* arm_MLS_VEC Q16 Q27 (Q7 :> LANE_H 0) 16 128 *)
     0x4f418864;       (* arm_MUL_VEC Q4 Q3 (Q1 :> LANE_H 4) 16 128 *)
     0x4f418353;       (* arm_MUL_VEC Q19 Q26 (Q1 :> LANE_H 0) 16 128 *)
     0x4f51d34f;       (* arm_SQRDMULH_VEC Q15 Q26 (Q1 :> LANE_H 1) 16 128 *)
     0x3dc0041b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 16)) *)
     0x4f51d875;       (* arm_SQRDMULH_VEC Q21 Q3 (Q1 :> LANE_H 5) 16 128 *)
     0x6f474052;       (* arm_MLS_VEC Q18 Q2 (Q7 :> LANE_H 0) 16 128 *)
     0x4e7d9ca2;       (* arm_MUL_VEC Q2 Q5 Q29 16 128 *)
     0x4f70d0c3;       (* arm_SQRDMULH_VEC Q3 Q6 (Q0 :> LANE_H 3) 16 128 *)
     0x6e7f876a;       (* arm_SUB_VEC Q10 Q27 Q31 16 128 *)
     0x6f4742a4;       (* arm_MLS_VEC Q4 Q21 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4741f3;       (* arm_MLS_VEC Q19 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x4f70d946;       (* arm_SQRDMULH_VEC Q6 Q10 (Q0 :> LANE_H 7) 16 128 *)
     0x4f60895a;       (* arm_MUL_VEC Q26 Q10 (Q0 :> LANE_H 6) 16 128 *)
     0x4e7f876a;       (* arm_ADD_VEC Q10 Q27 Q31 16 128 *)
     0x4e6b85df;       (* arm_ADD_VEC Q31 Q14 Q11 16 128 *)
     0x3d804010;       (* arm_STR Q16 X0 (Immediate_Offset (word 256)) *)
     0x6f474071;       (* arm_MLS_VEC Q17 Q3 (Q7 :> LANE_H 0) 16 128 *)
     0x4e778550;       (* arm_ADD_VEC Q16 Q10 Q23 16 128 *)
     0x3dc04803;       (* arm_LDR Q3 X0 (Immediate_Offset (word 288)) *)
     0x6e68862b;       (* arm_SUB_VEC Q11 Q17 Q8 16 128 *)
     0x6f4742c2;       (* arm_MLS_VEC Q2 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4740da;       (* arm_MLS_VEC Q26 Q6 (Q7 :> LANE_H 0) 16 128 *)
     0x4f50d176;       (* arm_SQRDMULH_VEC Q22 Q11 (Q0 :> LANE_H 1) 16 128 *)
     0x4e7f8605;       (* arm_ADD_VEC Q5 Q16 Q31 16 128 *)
     0x4f40816b;       (* arm_MUL_VEC Q11 Q11 (Q0 :> LANE_H 0) 16 128 *)
     0x3dc06819;       (* arm_LDR Q25 X0 (Immediate_Offset (word 416)) *)
     0x3dc03815;       (* arm_LDR Q21 X0 (Immediate_Offset (word 224)) *)
     0x6f4742cb;       (* arm_MLS_VEC Q11 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x4f50d1af;       (* arm_SQRDMULH_VEC Q15 Q13 (Q0 :> LANE_H 1) 16 128 *)
     0x6e7eb4b6;       (* arm_SQRDMULH_VEC Q22 Q5 Q30 16 128 *)
     0x4f61838e;       (* arm_MUL_VEC Q14 Q28 (Q1 :> LANE_H 2) 16 128 *)
     0x6e7f861b;       (* arm_SUB_VEC Q27 Q16 Q31 16 128 *)
     0x6e738746;       (* arm_SUB_VEC Q6 Q26 Q19 16 128 *)
     0x4e68863f;       (* arm_ADD_VEC Q31 Q17 Q8 16 128 *)
     0x4f71d388;       (* arm_SQRDMULH_VEC Q8 Q28 (Q1 :> LANE_H 3) 16 128 *)
     0x6e7eb71c;       (* arm_SQRDMULH_VEC Q28 Q24 Q30 16 128 *)
     0x4f618b70;       (* arm_MUL_VEC Q16 Q27 (Q1 :> LANE_H 6) 16 128 *)
     0x3d80301f;       (* arm_STR Q31 X0 (Immediate_Offset (word 192)) *)
     0x6e778551;       (* arm_SUB_VEC Q17 Q10 Q23 16 128 *)
     0x3d80700b;       (* arm_STR Q11 X0 (Immediate_Offset (word 448)) *)
     0x6f47410e;       (* arm_MLS_VEC Q14 Q8 (Q7 :> LANE_H 0) 16 128 *)
     0x3c810402;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
     0x4e7d9f0b;       (* arm_MUL_VEC Q11 Q24 Q29 16 128 *)
     0x4f70d238;       (* arm_SQRDMULH_VEC Q24 Q17 (Q0 :> LANE_H 3) 16 128 *)
     0x4f608231;       (* arm_MUL_VEC Q17 Q17 (Q0 :> LANE_H 2) 16 128 *)
     0x4f4081b7;       (* arm_MUL_VEC Q23 Q13 (Q0 :> LANE_H 0) 16 128 *)
     0x6e6c852d;       (* arm_SUB_VEC Q13 Q9 Q12 16 128 *)
     0x4e738749;       (* arm_ADD_VEC Q9 Q26 Q19 16 128 *)
     0x4e6485cc;       (* arm_ADD_VEC Q12 Q14 Q4 16 128 *)
     0x4f71d9ba;       (* arm_SQRDMULH_VEC Q26 Q13 (Q1 :> LANE_H 7) 16 128 *)
     0x4f6189a8;       (* arm_MUL_VEC Q8 Q13 (Q1 :> LANE_H 6) 16 128 *)
     0x3dc0540d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 336)) *)
     0x6f47438b;       (* arm_MLS_VEC Q11 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474348;       (* arm_MLS_VEC Q8 Q26 (Q7 :> LANE_H 0) 16 128 *)
     0x6e6485da;       (* arm_SUB_VEC Q26 Q14 Q4 16 128 *)
     0x6f474311;       (* arm_MLS_VEC Q17 Q24 (Q7 :> LANE_H 0) 16 128 *)
     0x4e6d846e;       (* arm_ADD_VEC Q14 Q3 Q13 16 128 *)
     0x3d804c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 304)) *)
     0x6e6d847c;       (* arm_SUB_VEC Q28 Q3 Q13 16 128 *)
     0x3d800c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 48)) *)
     0x6e72862d;       (* arm_SUB_VEC Q13 Q17 Q18 16 128 *)
     0x3d801c14;       (* arm_STR Q20 X0 (Immediate_Offset (word 112)) *)
     0x4e728634;       (* arm_ADD_VEC Q20 Q17 Q18 16 128 *)
     0x4f71db7b;       (* arm_SQRDMULH_VEC Q27 Q27 (Q1 :> LANE_H 7) 16 128 *)
     0x6f4741f7;       (* arm_MLS_VEC Q23 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x4f408b48;       (* arm_MUL_VEC Q8 Q26 (Q0 :> LANE_H 4) 16 128 *)
     0x4f50db52;       (* arm_SQRDMULH_VEC Q18 Q26 (Q0 :> LANE_H 5) 16 128 *)
     0x4e6c8538;       (* arm_ADD_VEC Q24 Q9 Q12 16 128 *)
     0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
     0x3dc07417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 464)) *)
     0x3dc0141f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 80)) *)
     0x4e77872b;       (* arm_ADD_VEC Q11 Q25 Q23 16 128 *)
     0x4f6080d1;       (* arm_MUL_VEC Q17 Q6 (Q0 :> LANE_H 2) 16 128 *)
     0x6f474248;       (* arm_MLS_VEC Q8 Q18 (Q7 :> LANE_H 0) 16 128 *)
     0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
     0xb5fff5a4;       (* arm_CBNZ X4 (word 2096820) *)
     0x4f4081a3;       (* arm_MUL_VEC Q3 Q13 (Q0 :> LANE_H 0) 16 128 *)
     0x4f50d1ad;       (* arm_SQRDMULH_VEC Q13 Q13 (Q0 :> LANE_H 1) 16 128 *)
     0x6f474370;       (* arm_MLS_VEC Q16 Q27 (Q7 :> LANE_H 0) 16 128 *)
     0x4e6b85cf;       (* arm_ADD_VEC Q15 Q14 Q11 16 128 *)
     0x6e6b85db;       (* arm_SUB_VEC Q27 Q14 Q11 16 128 *)
     0x6e7eb71a;       (* arm_SQRDMULH_VEC Q26 Q24 Q30 16 128 *)
     0x4e7d9f02;       (* arm_MUL_VEC Q2 Q24 Q29 16 128 *)
     0x4e7d9cab;       (* arm_MUL_VEC Q11 Q5 Q29 16 128 *)
     0x6e778724;       (* arm_SUB_VEC Q4 Q25 Q23 16 128 *)
     0x6e6c852e;       (* arm_SUB_VEC Q14 Q9 Q12 16 128 *)
     0x4f61838a;       (* arm_MUL_VEC Q10 Q28 (Q1 :> LANE_H 2) 16 128 *)
     0x4f71d389;       (* arm_SQRDMULH_VEC Q9 Q28 (Q1 :> LANE_H 3) 16 128 *)
     0x6f4742cb;       (* arm_MLS_VEC Q11 Q22 (Q7 :> LANE_H 0) 16 128 *)
     0x4f70d0dc;       (* arm_SQRDMULH_VEC Q28 Q6 (Q0 :> LANE_H 3) 16 128 *)
     0x3d802014;       (* arm_STR Q20 X0 (Immediate_Offset (word 128)) *)
     0x3dc02406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 144)) *)
     0x6f474391;       (* arm_MLS_VEC Q17 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x6f4741a3;       (* arm_MLS_VEC Q3 Q13 (Q7 :> LANE_H 0) 16 128 *)
     0x6e7584d9;       (* arm_SUB_VEC Q25 Q6 Q21 16 128 *)
     0x4e7584d4;       (* arm_ADD_VEC Q20 Q6 Q21 16 128 *)
     0x6e68862c;       (* arm_SUB_VEC Q12 Q17 Q8 16 128 *)
     0x4e688635;       (* arm_ADD_VEC Q21 Q17 Q8 16 128 *)
     0x3dc00412;       (* arm_LDR Q18 X0 (Immediate_Offset (word 16)) *)
     0x3d804010;       (* arm_STR Q16 X0 (Immediate_Offset (word 256)) *)
     0x4f408b76;       (* arm_MUL_VEC Q22 Q27 (Q0 :> LANE_H 4) 16 128 *)
     0x4e7f8658;       (* arm_ADD_VEC Q24 Q18 Q31 16 128 *)
     0x6e7f865c;       (* arm_SUB_VEC Q28 Q18 Q31 16 128 *)
     0x4f50db68;       (* arm_SQRDMULH_VEC Q8 Q27 (Q0 :> LANE_H 5) 16 128 *)
     0x4e748717;       (* arm_ADD_VEC Q23 Q24 Q20 16 128 *)
     0x6f474342;       (* arm_MLS_VEC Q2 Q26 (Q7 :> LANE_H 0) 16 128 *)
     0x4f418886;       (* arm_MUL_VEC Q6 Q4 (Q1 :> LANE_H 4) 16 128 *)
     0x6e6f86f1;       (* arm_SUB_VEC Q17 Q23 Q15 16 128 *)
     0x4e6f86fa;       (* arm_ADD_VEC Q26 Q23 Q15 16 128 *)
     0x4f51d88f;       (* arm_SQRDMULH_VEC Q15 Q4 (Q1 :> LANE_H 5) 16 128 *)
     0x4f71d9df;       (* arm_SQRDMULH_VEC Q31 Q14 (Q1 :> LANE_H 7) 16 128 *)
     0x4f6189ce;       (* arm_MUL_VEC Q14 Q14 (Q1 :> LANE_H 6) 16 128 *)
     0x6f47412a;       (* arm_MLS_VEC Q10 Q9 (Q7 :> LANE_H 0) 16 128 *)
     0x3c81040b;       (* arm_STR Q11 X0 (Postimmediate_Offset (word 16)) *)
     0x4f51d337;       (* arm_SQRDMULH_VEC Q23 Q25 (Q1 :> LANE_H 1) 16 128 *)
     0x3d805c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 368)) *)
     0x4f418332;       (* arm_MUL_VEC Q18 Q25 (Q1 :> LANE_H 0) 16 128 *)
     0x6e748719;       (* arm_SUB_VEC Q25 Q24 Q20 16 128 *)
     0x4e7d9f45;       (* arm_MUL_VEC Q5 Q26 Q29 16 128 *)
     0x4f608b98;       (* arm_MUL_VEC Q24 Q28 (Q0 :> LANE_H 6) 16 128 *)
     0x3d802c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 176)) *)
     0x6f4742f2;       (* arm_MLS_VEC Q18 Q23 (Q7 :> LANE_H 0) 16 128 *)
     0x4f70db94;       (* arm_SQRDMULH_VEC Q20 Q28 (Q0 :> LANE_H 7) 16 128 *)
     0x6f4741e6;       (* arm_MLS_VEC Q6 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x6e7eb74f;       (* arm_SQRDMULH_VEC Q15 Q26 Q30 16 128 *)
     0x4f70d33b;       (* arm_SQRDMULH_VEC Q27 Q25 (Q0 :> LANE_H 3) 16 128 *)
     0x6f474116;       (* arm_MLS_VEC Q22 Q8 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474298;       (* arm_MLS_VEC Q24 Q20 (Q7 :> LANE_H 0) 16 128 *)
     0x6e668549;       (* arm_SUB_VEC Q9 Q10 Q6 16 128 *)
     0x4f608334;       (* arm_MUL_VEC Q20 Q25 (Q0 :> LANE_H 2) 16 128 *)
     0x4e66854b;       (* arm_ADD_VEC Q11 Q10 Q6 16 128 *)
     0x6e728715;       (* arm_SUB_VEC Q21 Q24 Q18 16 128 *)
     0x4f50d93c;       (* arm_SQRDMULH_VEC Q28 Q9 (Q0 :> LANE_H 5) 16 128 *)
     0x4f408933;       (* arm_MUL_VEC Q19 Q9 (Q0 :> LANE_H 4) 16 128 *)
     0x4f6082a8;       (* arm_MUL_VEC Q8 Q21 (Q0 :> LANE_H 2) 16 128 *)
     0x4f70d2a3;       (* arm_SQRDMULH_VEC Q3 Q21 (Q0 :> LANE_H 3) 16 128 *)
     0x3d800c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 48)) *)
     0x4e728709;       (* arm_ADD_VEC Q9 Q24 Q18 16 128 *)
     0x6f474374;       (* arm_MLS_VEC Q20 Q27 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474393;       (* arm_MLS_VEC Q19 Q28 (Q7 :> LANE_H 0) 16 128 *)
     0x4f618a3c;       (* arm_MUL_VEC Q28 Q17 (Q1 :> LANE_H 6) 16 128 *)
     0x4f71da3b;       (* arm_SQRDMULH_VEC Q27 Q17 (Q1 :> LANE_H 7) 16 128 *)
     0x6f4741e5;       (* arm_MLS_VEC Q5 Q15 (Q7 :> LANE_H 0) 16 128 *)
     0x6f474068;       (* arm_MLS_VEC Q8 Q3 (Q7 :> LANE_H 0) 16 128 *)
     0x6e76868a;       (* arm_SUB_VEC Q10 Q20 Q22 16 128 *)
     0x4e6b8522;       (* arm_ADD_VEC Q2 Q9 Q11 16 128 *)
     0x6f4743ee;       (* arm_MLS_VEC Q14 Q31 (Q7 :> LANE_H 0) 16 128 *)
     0x6e738519;       (* arm_SUB_VEC Q25 Q8 Q19 16 128 *)
     0x6e6b852d;       (* arm_SUB_VEC Q13 Q9 Q11 16 128 *)
     0x4f50d143;       (* arm_SQRDMULH_VEC Q3 Q10 (Q0 :> LANE_H 1) 16 128 *)
     0x4f40814f;       (* arm_MUL_VEC Q15 Q10 (Q0 :> LANE_H 0) 16 128 *)
     0x4f40833a;       (* arm_MUL_VEC Q26 Q25 (Q0 :> LANE_H 0) 16 128 *)
     0x4f50d339;       (* arm_SQRDMULH_VEC Q25 Q25 (Q0 :> LANE_H 1) 16 128 *)
     0x4e7d9c4b;       (* arm_MUL_VEC Q11 Q2 Q29 16 128 *)
     0x4e768690;       (* arm_ADD_VEC Q16 Q20 Q22 16 128 *)
     0x3c810405;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
     0x6f47433a;       (* arm_MLS_VEC Q26 Q25 (Q7 :> LANE_H 0) 16 128 *)
     0x6e7eb457;       (* arm_SQRDMULH_VEC Q23 Q2 Q30 16 128 *)
     0x6f47406f;       (* arm_MLS_VEC Q15 Q3 (Q7 :> LANE_H 0) 16 128 *)
     0x4f6189b1;       (* arm_MUL_VEC Q17 Q13 (Q1 :> LANE_H 6) 16 128 *)
     0x3d806c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 432)) *)
     0x6f4742eb;       (* arm_MLS_VEC Q11 Q23 (Q7 :> LANE_H 0) 16 128 *)
     0x4e738515;       (* arm_ADD_VEC Q21 Q8 Q19 16 128 *)
     0x3d801c10;       (* arm_STR Q16 X0 (Immediate_Offset (word 112)) *)
     0x4f71d9a6;       (* arm_SQRDMULH_VEC Q6 Q13 (Q1 :> LANE_H 7) 16 128 *)
     0x3d800c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 48)) *)
     0x4f50d184;       (* arm_SQRDMULH_VEC Q4 Q12 (Q0 :> LANE_H 1) 16 128 *)
     0x3d805c0f;       (* arm_STR Q15 X0 (Immediate_Offset (word 368)) *)
     0x6f4740d1;       (* arm_MLS_VEC Q17 Q6 (Q7 :> LANE_H 0) 16 128 *)
     0x3d80480e;       (* arm_STR Q14 X0 (Immediate_Offset (word 288)) *)
     0x4f408198;       (* arm_MUL_VEC Q24 Q12 (Q0 :> LANE_H 0) 16 128 *)
     0x3d802c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 176)) *)
     0x6f47437c;       (* arm_MLS_VEC Q28 Q27 (Q7 :> LANE_H 0) 16 128 *)
     0x3d804c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 304)) *)
     0x6f474098;       (* arm_MLS_VEC Q24 Q4 (Q7 :> LANE_H 0) 16 128 *)
     0x3d803c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 240)) *)
     0x3d806818;       (* arm_STR Q24 X0 (Immediate_Offset (word 416)) *)
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
            (1--1025) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1025" THEN
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
