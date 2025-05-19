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
  0x3dc00071;       (* arm_LDR Q17 X3 (Immediate_Offset (word 0)) *)
  0x3dc00474;       (* arm_LDR Q20 X3 (Immediate_Offset (word 16)) *)
  0x3dc01446;       (* arm_LDR Q6 X2 (Immediate_Offset (word 80)) *)
  0x4e942a39;       (* arm_TRN1 Q25 Q17 Q20 32 128 *)
  0x4e946a31;       (* arm_TRN2 Q17 Q17 Q20 32 128 *)
  0x3dc00874;       (* arm_LDR Q20 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c62;       (* arm_LDR Q2 X3 (Immediate_Offset (word 48)) *)
  0x3dc00457;       (* arm_LDR Q23 X2 (Immediate_Offset (word 16)) *)
  0x4e826a9d;       (* arm_TRN2 Q29 Q20 Q2 32 128 *)
  0x4e822a94;       (* arm_TRN1 Q20 Q20 Q2 32 128 *)
  0x3dc0147a;       (* arm_LDR Q26 X3 (Immediate_Offset (word 80)) *)
  0x4edd6a22;       (* arm_TRN2 Q2 Q17 Q29 64 128 *)
  0x4ed46b2a;       (* arm_TRN2 Q10 Q25 Q20 64 128 *)
  0x4ed42b34;       (* arm_TRN1 Q20 Q25 Q20 64 128 *)
  0x6e628559;       (* arm_SUB_VEC Q25 Q10 Q2 16 128 *)
  0x4edd2a31;       (* arm_TRN1 Q17 Q17 Q29 64 128 *)
  0x4e628542;       (* arm_ADD_VEC Q2 Q10 Q2 16 128 *)
  0x6e66b726;       (* arm_SQRDMULH_VEC Q6 Q25 Q6 16 128 *)
  0x6e71869d;       (* arm_SUB_VEC Q29 Q20 Q17 16 128 *)
  0x3dc00c4a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 48)) *)
  0x3dc00844;       (* arm_LDR Q4 X2 (Immediate_Offset (word 32)) *)
  0x6e6ab7aa;       (* arm_SQRDMULH_VEC Q10 Q29 Q10 16 128 *)
  0x3dc0104d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 64)) *)
  0x4e649fbd;       (* arm_MUL_VEC Q29 Q29 Q4 16 128 *)
  0x4e718691;       (* arm_ADD_VEC Q17 Q20 Q17 16 128 *)
  0x4e6d9f34;       (* arm_MUL_VEC Q20 Q25 Q13 16 128 *)
  0x3cc60459;       (* arm_LDR Q25 X2 (Postimmediate_Offset (word 96)) *)
  0x6f47415d;       (* arm_MLS_VEC Q29 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740d4;       (* arm_MLS_VEC Q20 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6e628626;       (* arm_SUB_VEC Q6 Q17 Q2 16 128 *)
  0x3dc0106d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 64)) *)
  0x6e7487aa;       (* arm_SUB_VEC Q10 Q29 Q20 16 128 *)
  0x4e628631;       (* arm_ADD_VEC Q17 Q17 Q2 16 128 *)
  0x6e77b4c2;       (* arm_SQRDMULH_VEC Q2 Q6 Q23 16 128 *)
  0x6e77b557;       (* arm_SQRDMULH_VEC Q23 Q10 Q23 16 128 *)
  0x4e7487b4;       (* arm_ADD_VEC Q20 Q29 Q20 16 128 *)
  0x4e799d5d;       (* arm_MUL_VEC Q29 Q10 Q25 16 128 *)
  0x4e799cc6;       (* arm_MUL_VEC Q6 Q6 Q25 16 128 *)
  0x4e942a39;       (* arm_TRN1 Q25 Q17 Q20 32 128 *)
  0x4e946a31;       (* arm_TRN2 Q17 Q17 Q20 32 128 *)
  0x6f4742fd;       (* arm_MLS_VEC Q29 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474046;       (* arm_MLS_VEC Q6 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x4e9a69a5;       (* arm_TRN2 Q5 Q13 Q26 32 128 *)
  0x4e9d68c2;       (* arm_TRN2 Q2 Q6 Q29 32 128 *)
  0x4e9a29bb;       (* arm_TRN1 Q27 Q13 Q26 32 128 *)
  0x4e9d28c6;       (* arm_TRN1 Q6 Q6 Q29 32 128 *)
  0x4ec22a37;       (* arm_TRN1 Q23 Q17 Q2 64 128 *)
  0x4ec26a31;       (* arm_TRN2 Q17 Q17 Q2 64 128 *)
  0x4ec66b22;       (* arm_TRN2 Q2 Q25 Q6 64 128 *)
  0x4ec62b26;       (* arm_TRN1 Q6 Q25 Q6 64 128 *)
  0x4e718448;       (* arm_ADD_VEC Q8 Q2 Q17 16 128 *)
  0x6e718451;       (* arm_SUB_VEC Q17 Q2 Q17 16 128 *)
  0x4e7784d3;       (* arm_ADD_VEC Q19 Q6 Q23 16 128 *)
  0x4f57c112;       (* arm_SQDMULH_VEC Q18 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7784d9;       (* arm_SUB_VEC Q25 Q6 Q23 16 128 *)
  0x4f448a20;       (* arm_MUL_VEC Q0 Q17 (Q4 :> LANE_H 4) 16 128 *)
  0x4f54da26;       (* arm_SQRDMULH_VEC Q6 Q17 (Q4 :> LANE_H 5) 16 128 *)
  0x4f74d322;       (* arm_SQRDMULH_VEC Q2 Q25 (Q4 :> LANE_H 3) 16 128 *)
  0x4f64832a;       (* arm_MUL_VEC Q10 Q25 (Q4 :> LANE_H 2) 16 128 *)
  0x4f152651;       (* arm_SRSHR_VEC Q17 Q18 11 16 128 *)
  0x6f4740c0;       (* arm_MLS_VEC Q0 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c279;       (* arm_SQDMULH_VEC Q25 Q19 (Q7 :> LANE_H 1) 16 128 *)
  0x6f47404a;       (* arm_MLS_VEC Q10 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01458;       (* arm_LDR Q24 X2 (Immediate_Offset (word 80)) *)
  0x4f152726;       (* arm_SRSHR_VEC Q6 Q25 11 16 128 *)
  0x4e608554;       (* arm_ADD_VEC Q20 Q10 Q0 16 128 *)
  0x6f474228;       (* arm_MLS_VEC Q8 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740d3;       (* arm_MLS_VEC Q19 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c291;       (* arm_SQDMULH_VEC Q17 Q20 (Q7 :> LANE_H 1) 16 128 *)
  0x3dc01862;       (* arm_LDR Q2 X3 (Immediate_Offset (word 96)) *)
  0x4e688666;       (* arm_ADD_VEC Q6 Q19 Q8 16 128 *)
  0x4f152631;       (* arm_SRSHR_VEC Q17 Q17 11 16 128 *)
  0x3dc0044e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 16)) *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6e68867a;       (* arm_SUB_VEC Q26 Q19 Q8 16 128 *)
  0x3dc01c7e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 112)) *)
  0x4f448349;       (* arm_MUL_VEC Q9 Q26 (Q4 :> LANE_H 0) 16 128 *)
  0x4f54d350;       (* arm_SQRDMULH_VEC Q16 Q26 (Q4 :> LANE_H 1) 16 128 *)
  0x4e9e685a;       (* arm_TRN2 Q26 Q2 Q30 32 128 *)
  0x3c840466;       (* arm_STR Q6 X3 (Postimmediate_Offset (word 64)) *)
  0x6f474234;       (* arm_MLS_VEC Q20 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4eda68a6;       (* arm_TRN2 Q6 Q5 Q26 64 128 *)
  0x6f474209;       (* arm_MLS_VEC Q9 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9e285f;       (* arm_TRN1 Q31 Q2 Q30 32 128 *)
  0x3c9d0074;       (* arm_STR Q20 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x4eda28bc;       (* arm_TRN1 Q28 Q5 Q26 64 128 *)
  0x3c9e0069;       (* arm_STR Q9 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x4edf2b69;       (* arm_TRN1 Q9 Q27 Q31 64 128 *)
  0x3dc00c4b;       (* arm_LDR Q11 X2 (Immediate_Offset (word 48)) *)
  0x6e7c8535;       (* arm_SUB_VEC Q21 Q9 Q28 16 128 *)
  0x3dc0085d;       (* arm_LDR Q29 X2 (Immediate_Offset (word 32)) *)
  0x6e6bb6ba;       (* arm_SQRDMULH_VEC Q26 Q21 Q11 16 128 *)
  0x4edf6b68;       (* arm_TRN2 Q8 Q27 Q31 64 128 *)
  0x4e7d9ead;       (* arm_MUL_VEC Q13 Q21 Q29 16 128 *)
  0x6e668512;       (* arm_SUB_VEC Q18 Q8 Q6 16 128 *)
  0x3dc01050;       (* arm_LDR Q16 X2 (Immediate_Offset (word 64)) *)
  0x6f47434d;       (* arm_MLS_VEC Q13 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e78b641;       (* arm_SQRDMULH_VEC Q1 Q18 Q24 16 128 *)
  0x4e709e58;       (* arm_MUL_VEC Q24 Q18 Q16 16 128 *)
  0x4e668515;       (* arm_ADD_VEC Q21 Q8 Q6 16 128 *)
  0x4e7c8529;       (* arm_ADD_VEC Q9 Q9 Q28 16 128 *)
  0x6e608557;       (* arm_SUB_VEC Q23 Q10 Q0 16 128 *)
  0x6f474038;       (* arm_MLS_VEC Q24 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4e758532;       (* arm_ADD_VEC Q18 Q9 Q21 16 128 *)
  0x3cc6044f;       (* arm_LDR Q15 X2 (Postimmediate_Offset (word 96)) *)
  0x4e7885a8;       (* arm_ADD_VEC Q8 Q13 Q24 16 128 *)
  0x6e7885bc;       (* arm_SUB_VEC Q28 Q13 Q24 16 128 *)
  0x6e758538;       (* arm_SUB_VEC Q24 Q9 Q21 16 128 *)
  0x4e882a50;       (* arm_TRN1 Q16 Q18 Q8 32 128 *)
  0x6e6eb79f;       (* arm_SQRDMULH_VEC Q31 Q28 Q14 16 128 *)
  0x4e6f9f8b;       (* arm_MUL_VEC Q11 Q28 Q15 16 128 *)
  0x6e6eb71b;       (* arm_SQRDMULH_VEC Q27 Q24 Q14 16 128 *)
  0x4e6f9f1a;       (* arm_MUL_VEC Q26 Q24 Q15 16 128 *)
  0x3dc01073;       (* arm_LDR Q19 X3 (Immediate_Offset (word 64)) *)
  0x6f4743eb;       (* arm_MLS_VEC Q11 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47437a;       (* arm_MLS_VEC Q26 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01478;       (* arm_LDR Q24 X3 (Immediate_Offset (word 80)) *)
  0x4e886a45;       (* arm_TRN2 Q5 Q18 Q8 32 128 *)
  0x4e8b6b41;       (* arm_TRN2 Q1 Q26 Q11 32 128 *)
  0x4e982a7b;       (* arm_TRN1 Q27 Q19 Q24 32 128 *)
  0x4e8b2b4a;       (* arm_TRN1 Q10 Q26 Q11 32 128 *)
  0x4ec128b6;       (* arm_TRN1 Q22 Q5 Q1 64 128 *)
  0x4ec168ad;       (* arm_TRN2 Q13 Q5 Q1 64 128 *)
  0x4e986a65;       (* arm_TRN2 Q5 Q19 Q24 32 128 *)
  0x4eca6a18;       (* arm_TRN2 Q24 Q16 Q10 64 128 *)
  0x4eca2a1f;       (* arm_TRN1 Q31 Q16 Q10 64 128 *)
  0x4e6d8708;       (* arm_ADD_VEC Q8 Q24 Q13 16 128 *)
  0x6e6d870e;       (* arm_SUB_VEC Q14 Q24 Q13 16 128 *)
  0x3dc01458;       (* arm_LDR Q24 X2 (Immediate_Offset (word 80)) *)
  0x6e7687f1;       (* arm_SUB_VEC Q17 Q31 Q22 16 128 *)
  0x4f57c10c;       (* arm_SQDMULH_VEC Q12 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x4e7687f3;       (* arm_ADD_VEC Q19 Q31 Q22 16 128 *)
  0x4f54d2fa;       (* arm_SQRDMULH_VEC Q26 Q23 (Q4 :> LANE_H 1) 16 128 *)
  0x4f4482eb;       (* arm_MUL_VEC Q11 Q23 (Q4 :> LANE_H 0) 16 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x4f152594;       (* arm_SRSHR_VEC Q20 Q12 11 16 128 *)
  0x4f57c276;       (* arm_SQDMULH_VEC Q22 Q19 (Q7 :> LANE_H 1) 16 128 *)
  0x4f74d23f;       (* arm_SQRDMULH_VEC Q31 Q17 (Q4 :> LANE_H 3) 16 128 *)
  0x4f54d9d2;       (* arm_SQRDMULH_VEC Q18 Q14 (Q4 :> LANE_H 5) 16 128 *)
  0x4f4489c0;       (* arm_MUL_VEC Q0 Q14 (Q4 :> LANE_H 4) 16 128 *)
  0x4f64822a;       (* arm_MUL_VEC Q10 Q17 (Q4 :> LANE_H 2) 16 128 *)
  0x6f474288;       (* arm_MLS_VEC Q8 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4f1526d5;       (* arm_SRSHR_VEC Q21 Q22 11 16 128 *)
  0x6f474240;       (* arm_MLS_VEC Q0 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743ea;       (* arm_MLS_VEC Q10 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742b3;       (* arm_MLS_VEC Q19 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01862;       (* arm_LDR Q2 X3 (Immediate_Offset (word 96)) *)
  0x4e608554;       (* arm_ADD_VEC Q20 Q10 Q0 16 128 *)
  0x6f47434b;       (* arm_MLS_VEC Q11 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4e688666;       (* arm_ADD_VEC Q6 Q19 Q8 16 128 *)
  0x4f57c291;       (* arm_SQDMULH_VEC Q17 Q20 (Q7 :> LANE_H 1) 16 128 *)
  0x3dc0044e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 16)) *)
  0x3c9f006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x4f152631;       (* arm_SRSHR_VEC Q17 Q17 11 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff5e4;       (* arm_CBNZ X4 (word 2096828) *)
  0x6e688677;       (* arm_SUB_VEC Q23 Q19 Q8 16 128 *)
  0x6f474234;       (* arm_MLS_VEC Q20 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6e608551;       (* arm_SUB_VEC Q17 Q10 Q0 16 128 *)
  0x4f54d2ef;       (* arm_SQRDMULH_VEC Q15 Q23 (Q4 :> LANE_H 1) 16 128 *)
  0x4f4482f2;       (* arm_MUL_VEC Q18 Q23 (Q4 :> LANE_H 0) 16 128 *)
  0x4f54d235;       (* arm_SQRDMULH_VEC Q21 Q17 (Q4 :> LANE_H 1) 16 128 *)
  0x4f448239;       (* arm_MUL_VEC Q25 Q17 (Q4 :> LANE_H 0) 16 128 *)
  0x3dc01c77;       (* arm_LDR Q23 X3 (Immediate_Offset (word 112)) *)
  0x3c840466;       (* arm_STR Q6 X3 (Postimmediate_Offset (word 64)) *)
  0x3dc0105c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 64)) *)
  0x4e97685a;       (* arm_TRN2 Q26 Q2 Q23 32 128 *)
  0x3c9d0074;       (* arm_STR Q20 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e97285d;       (* arm_TRN1 Q29 Q2 Q23 32 128 *)
  0x4eda28b7;       (* arm_TRN1 Q23 Q5 Q26 64 128 *)
  0x3dc00854;       (* arm_LDR Q20 X2 (Immediate_Offset (word 32)) *)
  0x4edd6b70;       (* arm_TRN2 Q16 Q27 Q29 64 128 *)
  0x4eda68b1;       (* arm_TRN2 Q17 Q5 Q26 64 128 *)
  0x4edd2b73;       (* arm_TRN1 Q19 Q27 Q29 64 128 *)
  0x6e71861f;       (* arm_SUB_VEC Q31 Q16 Q17 16 128 *)
  0x4e718606;       (* arm_ADD_VEC Q6 Q16 Q17 16 128 *)
  0x3dc00c51;       (* arm_LDR Q17 X2 (Immediate_Offset (word 48)) *)
  0x6e78b7e9;       (* arm_SQRDMULH_VEC Q9 Q31 Q24 16 128 *)
  0x6e77866b;       (* arm_SUB_VEC Q11 Q19 Q23 16 128 *)
  0x4e7c9ffa;       (* arm_MUL_VEC Q26 Q31 Q28 16 128 *)
  0x4e778668;       (* arm_ADD_VEC Q8 Q19 Q23 16 128 *)
  0x6e71b56a;       (* arm_SQRDMULH_VEC Q10 Q11 Q17 16 128 *)
  0x4e749d7e;       (* arm_MUL_VEC Q30 Q11 Q20 16 128 *)
  0x4e66851d;       (* arm_ADD_VEC Q29 Q8 Q6 16 128 *)
  0x6f47413a;       (* arm_MLS_VEC Q26 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6e668500;       (* arm_SUB_VEC Q0 Q8 Q6 16 128 *)
  0x6f47415e;       (* arm_MLS_VEC Q30 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc60449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 96)) *)
  0x6e6eb413;       (* arm_SQRDMULH_VEC Q19 Q0 Q14 16 128 *)
  0x6e7a87cb;       (* arm_SUB_VEC Q11 Q30 Q26 16 128 *)
  0x6f4741f2;       (* arm_MLS_VEC Q18 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e699c03;       (* arm_MUL_VEC Q3 Q0 Q9 16 128 *)
  0x6e6eb565;       (* arm_SQRDMULH_VEC Q5 Q11 Q14 16 128 *)
  0x4e699d74;       (* arm_MUL_VEC Q20 Q11 Q9 16 128 *)
  0x3c9e0072;       (* arm_STR Q18 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x6f474263;       (* arm_MLS_VEC Q3 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7a87d2;       (* arm_ADD_VEC Q18 Q30 Q26 16 128 *)
  0x6f4740b4;       (* arm_MLS_VEC Q20 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc10426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 16)) *)
  0x4e922ba8;       (* arm_TRN1 Q8 Q29 Q18 32 128 *)
  0x4e942862;       (* arm_TRN1 Q2 Q3 Q20 32 128 *)
  0x4e946865;       (* arm_TRN2 Q5 Q3 Q20 32 128 *)
  0x4e926ba0;       (* arm_TRN2 Q0 Q29 Q18 32 128 *)
  0x4ec2691f;       (* arm_TRN2 Q31 Q8 Q2 64 128 *)
  0x4ec22917;       (* arm_TRN1 Q23 Q8 Q2 64 128 *)
  0x4ec52801;       (* arm_TRN1 Q1 Q0 Q5 64 128 *)
  0x4ec5680d;       (* arm_TRN2 Q13 Q0 Q5 64 128 *)
  0x4e6186ee;       (* arm_ADD_VEC Q14 Q23 Q1 16 128 *)
  0x4e6d87fb;       (* arm_ADD_VEC Q27 Q31 Q13 16 128 *)
  0x6e6d87e4;       (* arm_SUB_VEC Q4 Q31 Q13 16 128 *)
  0x4f57c1dc;       (* arm_SQDMULH_VEC Q28 Q14 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c37e;       (* arm_SQDMULH_VEC Q30 Q27 (Q7 :> LANE_H 1) 16 128 *)
  0x4f56d89a;       (* arm_SQRDMULH_VEC Q26 Q4 (Q6 :> LANE_H 5) 16 128 *)
  0x4f46888a;       (* arm_MUL_VEC Q10 Q4 (Q6 :> LANE_H 4) 16 128 *)
  0x4f152780;       (* arm_SRSHR_VEC Q0 Q28 11 16 128 *)
  0x4f1527de;       (* arm_SRSHR_VEC Q30 Q30 11 16 128 *)
  0x6e6186ef;       (* arm_SUB_VEC Q15 Q23 Q1 16 128 *)
  0x6f47400e;       (* arm_MLS_VEC Q14 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743db;       (* arm_MLS_VEC Q27 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4f76d1f4;       (* arm_SQRDMULH_VEC Q20 Q15 (Q6 :> LANE_H 3) 16 128 *)
  0x4f6681e8;       (* arm_MUL_VEC Q8 Q15 (Q6 :> LANE_H 2) 16 128 *)
  0x6f4742b9;       (* arm_MLS_VEC Q25 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47434a;       (* arm_MLS_VEC Q10 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7b85c2;       (* arm_SUB_VEC Q2 Q14 Q27 16 128 *)
  0x6f474288;       (* arm_MLS_VEC Q8 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9f0079;       (* arm_STR Q25 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7b85d8;       (* arm_ADD_VEC Q24 Q14 Q27 16 128 *)
  0x4f56d053;       (* arm_SQRDMULH_VEC Q19 Q2 (Q6 :> LANE_H 1) 16 128 *)
  0x4e6a8501;       (* arm_ADD_VEC Q1 Q8 Q10 16 128 *)
  0x6e6a850a;       (* arm_SUB_VEC Q10 Q8 Q10 16 128 *)
  0x4f468054;       (* arm_MUL_VEC Q20 Q2 (Q6 :> LANE_H 0) 16 128 *)
  0x4f57c02b;       (* arm_SQDMULH_VEC Q11 Q1 (Q7 :> LANE_H 1) 16 128 *)
  0x4f56d151;       (* arm_SQRDMULH_VEC Q17 Q10 (Q6 :> LANE_H 1) 16 128 *)
  0x4f468143;       (* arm_MUL_VEC Q3 Q10 (Q6 :> LANE_H 0) 16 128 *)
  0x6f474274;       (* arm_MLS_VEC Q20 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f15257a;       (* arm_SRSHR_VEC Q26 Q11 11 16 128 *)
  0x3c840478;       (* arm_STR Q24 X3 (Postimmediate_Offset (word 64)) *)
  0x6f474223;       (* arm_MLS_VEC Q3 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474341;       (* arm_MLS_VEC Q1 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9e0074;       (* arm_STR Q20 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f0063;       (* arm_STR Q3 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9d0061;       (* arm_STR Q1 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0201d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 128)) *)
  0x3dc03002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 192)) *)
  0x3dc0400a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 256)) *)
  0x3dc05004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 320)) *)
  0x3dc0600d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 384)) *)
  0x3dc07005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 448)) *)
  0x4e648543;       (* arm_ADD_VEC Q3 Q10 Q4 16 128 *)
  0x4e6287bb;       (* arm_ADD_VEC Q27 Q29 Q2 16 128 *)
  0x4e6585b8;       (* arm_ADD_VEC Q24 Q13 Q5 16 128 *)
  0x3dc00019;       (* arm_LDR Q25 X0 (Immediate_Offset (word 0)) *)
  0x4e788475;       (* arm_ADD_VEC Q21 Q3 Q24 16 128 *)
  0x3dc01017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 64)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x6e778731;       (* arm_SUB_VEC Q17 Q25 Q23 16 128 *)
  0x4e778734;       (* arm_ADD_VEC Q20 Q25 Q23 16 128 *)
  0x6e6287a6;       (* arm_SUB_VEC Q6 Q29 Q2 16 128 *)
  0x4f70da39;       (* arm_SQRDMULH_VEC Q25 Q17 (Q0 :> LANE_H 7) 16 128 *)
  0x4f608a31;       (* arm_MUL_VEC Q17 Q17 (Q0 :> LANE_H 6) 16 128 *)
  0x6e7b8682;       (* arm_SUB_VEC Q2 Q20 Q27 16 128 *)
  0x4e7b8694;       (* arm_ADD_VEC Q20 Q20 Q27 16 128 *)
  0x4f51d0d7;       (* arm_SQRDMULH_VEC Q23 Q6 (Q1 :> LANE_H 1) 16 128 *)
  0x4f4180c6;       (* arm_MUL_VEC Q6 Q6 (Q1 :> LANE_H 0) 16 128 *)
  0x6f474331;       (* arm_MLS_VEC Q17 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6e648559;       (* arm_SUB_VEC Q25 Q10 Q4 16 128 *)
  0x4f70d05d;       (* arm_SQRDMULH_VEC Q29 Q2 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608042;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 2) 16 128 *)
  0x6e75868a;       (* arm_SUB_VEC Q10 Q20 Q21 16 128 *)
  0x4e758694;       (* arm_ADD_VEC Q20 Q20 Q21 16 128 *)
  0x6f4742e6;       (* arm_MLS_VEC Q6 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d337;       (* arm_SQRDMULH_VEC Q23 Q25 (Q1 :> LANE_H 3) 16 128 *)
  0x4f618339;       (* arm_MUL_VEC Q25 Q25 (Q1 :> LANE_H 2) 16 128 *)
  0x6e6585a4;       (* arm_SUB_VEC Q4 Q13 Q5 16 128 *)
  0x6e66862d;       (* arm_SUB_VEC Q13 Q17 Q6 16 128 *)
  0x4e668631;       (* arm_ADD_VEC Q17 Q17 Q6 16 128 *)
  0x6f4742f9;       (* arm_MLS_VEC Q25 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d886;       (* arm_SQRDMULH_VEC Q6 Q4 (Q1 :> LANE_H 5) 16 128 *)
  0x6f4743a2;       (* arm_MLS_VEC Q2 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4f418897;       (* arm_MUL_VEC Q23 Q4 (Q1 :> LANE_H 4) 16 128 *)
  0x4f70d1bd;       (* arm_SQRDMULH_VEC Q29 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6081a4;       (* arm_MUL_VEC Q4 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50d14d;       (* arm_SQRDMULH_VEC Q13 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40814a;       (* arm_MUL_VEC Q10 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x3c810414;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 16)) *)
  0x6f4740d7;       (* arm_MLS_VEC Q23 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743a4;       (* arm_MLS_VEC Q4 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6e788474;       (* arm_SUB_VEC Q20 Q3 Q24 16 128 *)
  0x6f4741aa;       (* arm_MLS_VEC Q10 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e778726;       (* arm_SUB_VEC Q6 Q25 Q23 16 128 *)
  0x4f50da9d;       (* arm_SQRDMULH_VEC Q29 Q20 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408a94;       (* arm_MUL_VEC Q20 Q20 (Q0 :> LANE_H 4) 16 128 *)
  0x4e778739;       (* arm_ADD_VEC Q25 Q25 Q23 16 128 *)
  0x4f50d8d7;       (* arm_SQRDMULH_VEC Q23 Q6 (Q0 :> LANE_H 5) 16 128 *)
  0x4f4088c6;       (* arm_MUL_VEC Q6 Q6 (Q0 :> LANE_H 4) 16 128 *)
  0x6f4743b4;       (* arm_MLS_VEC Q20 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6e79863d;       (* arm_SUB_VEC Q29 Q17 Q25 16 128 *)
  0x4e798631;       (* arm_ADD_VEC Q17 Q17 Q25 16 128 *)
  0x6f4742e6;       (* arm_MLS_VEC Q6 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d3b9;       (* arm_SQRDMULH_VEC Q25 Q29 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4083b7;       (* arm_MUL_VEC Q23 Q29 (Q0 :> LANE_H 0) 16 128 *)
  0x6e74845d;       (* arm_SUB_VEC Q29 Q2 Q20 16 128 *)
  0x4e748454;       (* arm_ADD_VEC Q20 Q2 Q20 16 128 *)
  0x6e668482;       (* arm_SUB_VEC Q2 Q4 Q6 16 128 *)
  0x6f474337;       (* arm_MLS_VEC Q23 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d3b9;       (* arm_SQRDMULH_VEC Q25 Q29 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4083bd;       (* arm_MUL_VEC Q29 Q29 (Q0 :> LANE_H 0) 16 128 *)
  0x4e668486;       (* arm_ADD_VEC Q6 Q4 Q6 16 128 *)
  0x4f50d044;       (* arm_SQRDMULH_VEC Q4 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408042;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47433d;       (* arm_MLS_VEC Q29 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x3d803c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 240)) *)
  0x3dc00019;       (* arm_LDR Q25 X0 (Immediate_Offset (word 0)) *)
  0x6f474082;       (* arm_MLS_VEC Q2 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 304)) *)
  0x3dc01017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 64)) *)
  0x3d805c1d;       (* arm_STR Q29 X0 (Immediate_Offset (word 368)) *)
  0x3dc0201d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 128)) *)
  0x3d806c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 432)) *)
  0x3dc03002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 192)) *)
  0x3d800c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 48)) *)
  0x3dc0400a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 256)) *)
  0x3dc05004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 320)) *)
  0x3dc0600d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 384)) *)
  0x3dc07005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 448)) *)
  0x3d801c14;       (* arm_STR Q20 X0 (Immediate_Offset (word 112)) *)
  0x4e648543;       (* arm_ADD_VEC Q3 Q10 Q4 16 128 *)
  0x4e6585b8;       (* arm_ADD_VEC Q24 Q13 Q5 16 128 *)
  0x3d802c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 176)) *)
  0x4e6287bb;       (* arm_ADD_VEC Q27 Q29 Q2 16 128 *)
  0x4e788475;       (* arm_ADD_VEC Q21 Q3 Q24 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4e778736;       (* arm_ADD_VEC Q22 Q25 Q23 16 128 *)
  0x6e788471;       (* arm_SUB_VEC Q17 Q3 Q24 16 128 *)
  0x6e778739;       (* arm_SUB_VEC Q25 Q25 Q23 16 128 *)
  0x6e7b86d3;       (* arm_SUB_VEC Q19 Q22 Q27 16 128 *)
  0x4f408a3c;       (* arm_MUL_VEC Q28 Q17 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50da34;       (* arm_SQRDMULH_VEC Q20 Q17 (Q0 :> LANE_H 5) 16 128 *)
  0x4f70d271;       (* arm_SQRDMULH_VEC Q17 Q19 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608278;       (* arm_MUL_VEC Q24 Q19 (Q0 :> LANE_H 2) 16 128 *)
  0x6e6287bf;       (* arm_SUB_VEC Q31 Q29 Q2 16 128 *)
  0x4f70db33;       (* arm_SQRDMULH_VEC Q19 Q25 (Q0 :> LANE_H 7) 16 128 *)
  0x6f47429c;       (* arm_MLS_VEC Q28 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474238;       (* arm_MLS_VEC Q24 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d3e9;       (* arm_SQRDMULH_VEC Q9 Q31 (Q1 :> LANE_H 1) 16 128 *)
  0x4f4183fa;       (* arm_MUL_VEC Q26 Q31 (Q1 :> LANE_H 0) 16 128 *)
  0x4f608b37;       (* arm_MUL_VEC Q23 Q25 (Q0 :> LANE_H 6) 16 128 *)
  0x6e7c8711;       (* arm_SUB_VEC Q17 Q24 Q28 16 128 *)
  0x6e6585a5;       (* arm_SUB_VEC Q5 Q13 Q5 16 128 *)
  0x6f47413a;       (* arm_MLS_VEC Q26 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d234;       (* arm_SQRDMULH_VEC Q20 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408231;       (* arm_MUL_VEC Q17 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474277;       (* arm_MLS_VEC Q23 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d8a6;       (* arm_SQRDMULH_VEC Q6 Q5 (Q1 :> LANE_H 5) 16 128 *)
  0x4f4188a5;       (* arm_MUL_VEC Q5 Q5 (Q1 :> LANE_H 4) 16 128 *)
  0x6f474291;       (* arm_MLS_VEC Q17 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a86f0;       (* arm_SUB_VEC Q16 Q23 Q26 16 128 *)
  0x6e648543;       (* arm_SUB_VEC Q3 Q10 Q4 16 128 *)
  0x6f4740c5;       (* arm_MLS_VEC Q5 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f60821d;       (* arm_MUL_VEC Q29 Q16 (Q0 :> LANE_H 2) 16 128 *)
  0x4f70d206;       (* arm_SQRDMULH_VEC Q6 Q16 (Q0 :> LANE_H 3) 16 128 *)
  0x4f71d064;       (* arm_SQRDMULH_VEC Q4 Q3 (Q1 :> LANE_H 3) 16 128 *)
  0x4e7b86db;       (* arm_ADD_VEC Q27 Q22 Q27 16 128 *)
  0x4f618063;       (* arm_MUL_VEC Q3 Q3 (Q1 :> LANE_H 2) 16 128 *)
  0x6f4740dd;       (* arm_MLS_VEC Q29 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6e758779;       (* arm_SUB_VEC Q25 Q27 Q21 16 128 *)
  0x3d806011;       (* arm_STR Q17 X0 (Immediate_Offset (word 384)) *)
  0x6f474083;       (* arm_MLS_VEC Q3 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d322;       (* arm_SQRDMULH_VEC Q2 Q25 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40832a;       (* arm_MUL_VEC Q10 Q25 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7a86e4;       (* arm_ADD_VEC Q4 Q23 Q26 16 128 *)
  0x4e658474;       (* arm_ADD_VEC Q20 Q3 Q5 16 128 *)
  0x6e658477;       (* arm_SUB_VEC Q23 Q3 Q5 16 128 *)
  0x6f47404a;       (* arm_MLS_VEC Q10 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4e74848d;       (* arm_ADD_VEC Q13 Q4 Q20 16 128 *)
  0x4f408ae6;       (* arm_MUL_VEC Q6 Q23 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50daf7;       (* arm_SQRDMULH_VEC Q23 Q23 (Q0 :> LANE_H 5) 16 128 *)
  0x3d80400a;       (* arm_STR Q10 X0 (Immediate_Offset (word 256)) *)
  0x6e748489;       (* arm_SUB_VEC Q9 Q4 Q20 16 128 *)
  0x3d80100d;       (* arm_STR Q13 X0 (Immediate_Offset (word 64)) *)
  0x6f4742e6;       (* arm_MLS_VEC Q6 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d137;       (* arm_SQRDMULH_VEC Q23 Q9 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408139;       (* arm_MUL_VEC Q25 Q9 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7c8702;       (* arm_ADD_VEC Q2 Q24 Q28 16 128 *)
  0x6e6687b1;       (* arm_SUB_VEC Q17 Q29 Q6 16 128 *)
  0x4e6687a6;       (* arm_ADD_VEC Q6 Q29 Q6 16 128 *)
  0x6f4742f9;       (* arm_MLS_VEC Q25 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d234;       (* arm_SQRDMULH_VEC Q20 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408231;       (* arm_MUL_VEC Q17 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x3d803006;       (* arm_STR Q6 X0 (Immediate_Offset (word 192)) *)
  0x4e758777;       (* arm_ADD_VEC Q23 Q27 Q21 16 128 *)
  0x3d805019;       (* arm_STR Q25 X0 (Immediate_Offset (word 320)) *)
  0x6f474291;       (* arm_MLS_VEC Q17 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3c810417;       (* arm_STR Q23 X0 (Postimmediate_Offset (word 16)) *)
  0x3d801c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 112)) *)
  0x3d806c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 432)) *)
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
          [(word pc,0x6f8); (z_12345,160); (z_67,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                intt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x6e0) /\
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
            (1--1155) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1155" THEN
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
