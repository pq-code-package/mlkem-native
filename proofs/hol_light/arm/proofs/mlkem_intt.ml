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
  0x3dc00463;       (* arm_LDR Q3 X3 (Immediate_Offset (word 16)) *)
  0x3dc00074;       (* arm_LDR Q20 X3 (Immediate_Offset (word 0)) *)
  0x3dc00879;       (* arm_LDR Q25 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c78;       (* arm_LDR Q24 X3 (Immediate_Offset (word 48)) *)
  0x3dc01455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 80)) *)
  0x4e982b32;       (* arm_TRN1 Q18 Q25 Q24 32 128 *)
  0x4e832a86;       (* arm_TRN1 Q6 Q20 Q3 32 128 *)
  0x4e986b2c;       (* arm_TRN2 Q12 Q25 Q24 32 128 *)
  0x4e836a9f;       (* arm_TRN2 Q31 Q20 Q3 32 128 *)
  0x4ed268dc;       (* arm_TRN2 Q28 Q6 Q18 64 128 *)
  0x4ed228d9;       (* arm_TRN1 Q25 Q6 Q18 64 128 *)
  0x4ecc6bef;       (* arm_TRN2 Q15 Q31 Q12 64 128 *)
  0x4ecc2bf4;       (* arm_TRN1 Q20 Q31 Q12 64 128 *)
  0x4e6f8784;       (* arm_ADD_VEC Q4 Q28 Q15 16 128 *)
  0x4e748721;       (* arm_ADD_VEC Q1 Q25 Q20 16 128 *)
  0x6e6f879e;       (* arm_SUB_VEC Q30 Q28 Q15 16 128 *)
  0x6e748723;       (* arm_SUB_VEC Q3 Q25 Q20 16 128 *)
  0x4e648426;       (* arm_ADD_VEC Q6 Q1 Q4 16 128 *)
  0x6e75b7c9;       (* arm_SQRDMULH_VEC Q9 Q30 Q21 16 128 *)
  0x3dc01055;       (* arm_LDR Q21 X2 (Immediate_Offset (word 64)) *)
  0x3dc00c59;       (* arm_LDR Q25 X2 (Immediate_Offset (word 48)) *)
  0x4e759fd5;       (* arm_MUL_VEC Q21 Q30 Q21 16 128 *)
  0x3dc0085e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 32)) *)
  0x6e64843c;       (* arm_SUB_VEC Q28 Q1 Q4 16 128 *)
  0x3dc00441;       (* arm_LDR Q1 X2 (Immediate_Offset (word 16)) *)
  0x6f474135;       (* arm_MLS_VEC Q21 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6e79b469;       (* arm_SQRDMULH_VEC Q9 Q3 Q25 16 128 *)
  0x4e7e9c74;       (* arm_MUL_VEC Q20 Q3 Q30 16 128 *)
  0x3cc6045d;       (* arm_LDR Q29 X2 (Postimmediate_Offset (word 96)) *)
  0x3dc01871;       (* arm_LDR Q17 X3 (Immediate_Offset (word 96)) *)
  0x6f474134;       (* arm_MLS_VEC Q20 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01c63;       (* arm_LDR Q3 X3 (Immediate_Offset (word 112)) *)
  0x4e7d9f84;       (* arm_MUL_VEC Q4 Q28 Q29 16 128 *)
  0x6e758699;       (* arm_SUB_VEC Q25 Q20 Q21 16 128 *)
  0x4e832a2f;       (* arm_TRN1 Q15 Q17 Q3 32 128 *)
  0x6e61b79c;       (* arm_SQRDMULH_VEC Q28 Q28 Q1 16 128 *)
  0x4e836a3f;       (* arm_TRN2 Q31 Q17 Q3 32 128 *)
  0x4e7d9f3e;       (* arm_MUL_VEC Q30 Q25 Q29 16 128 *)
  0x4e758694;       (* arm_ADD_VEC Q20 Q20 Q21 16 128 *)
  0x6f474384;       (* arm_MLS_VEC Q4 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e61b723;       (* arm_SQRDMULH_VEC Q3 Q25 Q1 16 128 *)
  0x3dc0107c;       (* arm_LDR Q28 X3 (Immediate_Offset (word 64)) *)
  0x4e9428d9;       (* arm_TRN1 Q25 Q6 Q20 32 128 *)
  0x6f47407e;       (* arm_MLS_VEC Q30 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0147b;       (* arm_LDR Q27 X3 (Immediate_Offset (word 80)) *)
  0x4e9468c6;       (* arm_TRN2 Q6 Q6 Q20 32 128 *)
  0x4e9e2883;       (* arm_TRN1 Q3 Q4 Q30 32 128 *)
  0x4e9b6b8a;       (* arm_TRN2 Q10 Q28 Q27 32 128 *)
  0x4e9e6894;       (* arm_TRN2 Q20 Q4 Q30 32 128 *)
  0x4ec36b28;       (* arm_TRN2 Q8 Q25 Q3 64 128 *)
  0x4ec32b29;       (* arm_TRN1 Q9 Q25 Q3 64 128 *)
  0x4ed428c1;       (* arm_TRN1 Q1 Q6 Q20 64 128 *)
  0x4ed468de;       (* arm_TRN2 Q30 Q6 Q20 64 128 *)
  0x4e618524;       (* arm_ADD_VEC Q4 Q9 Q1 16 128 *)
  0x4e7e850b;       (* arm_ADD_VEC Q11 Q8 Q30 16 128 *)
  0x4edf6959;       (* arm_TRN2 Q25 Q10 Q31 64 128 *)
  0x4f57c086;       (* arm_SQDMULH_VEC Q6 Q4 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c174;       (* arm_SQDMULH_VEC Q20 Q11 (Q7 :> LANE_H 1) 16 128 *)
  0x3dc01455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 80)) *)
  0x4f1524c0;       (* arm_SRSHR_VEC Q0 Q6 11 16 128 *)
  0x4f152683;       (* arm_SRSHR_VEC Q3 Q20 11 16 128 *)
  0x4e9b2b82;       (* arm_TRN1 Q2 Q28 Q27 32 128 *)
  0x6f474004;       (* arm_MLS_VEC Q4 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47406b;       (* arm_MLS_VEC Q11 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc10420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 16)) *)
  0x4ecf6854;       (* arm_TRN2 Q20 Q2 Q15 64 128 *)
  0x6e6b8486;       (* arm_SUB_VEC Q6 Q4 Q11 16 128 *)
  0x6e798685;       (* arm_SUB_VEC Q5 Q20 Q25 16 128 *)
  0x6e618536;       (* arm_SUB_VEC Q22 Q9 Q1 16 128 *)
  0x4f50d0c3;       (* arm_SQRDMULH_VEC Q3 Q6 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4080c6;       (* arm_MUL_VEC Q6 Q6 (Q0 :> LANE_H 0) 16 128 *)
  0x6e75b4ac;       (* arm_SQRDMULH_VEC Q12 Q5 Q21 16 128 *)
  0x3dc01053;       (* arm_LDR Q19 X2 (Immediate_Offset (word 64)) *)
  0x6f474066;       (* arm_MLS_VEC Q6 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc6044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 96)) *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x3d800866;       (* arm_STR Q6 X3 (Immediate_Offset (word 32)) *)
  0x3cdb0052;       (* arm_LDR Q18 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4e739cba;       (* arm_MUL_VEC Q26 Q5 Q19 16 128 *)
  0x4edf2950;       (* arm_TRN1 Q16 Q10 Q31 64 128 *)
  0x4f6082db;       (* arm_MUL_VEC Q27 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x4ecf284a;       (* arm_TRN1 Q10 Q2 Q15 64 128 *)
  0x4e6b8485;       (* arm_ADD_VEC Q5 Q4 Q11 16 128 *)
  0x6f47419a;       (* arm_MLS_VEC Q26 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e70854b;       (* arm_ADD_VEC Q11 Q10 Q16 16 128 *)
  0x4e798686;       (* arm_ADD_VEC Q6 Q20 Q25 16 128 *)
  0x3cdc0059;       (* arm_LDR Q25 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x3cdd005c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x3dc02862;       (* arm_LDR Q2 X3 (Immediate_Offset (word 160)) *)
  0x3dc01053;       (* arm_LDR Q19 X2 (Immediate_Offset (word 64)) *)
  0x6e7e8511;       (* arm_SUB_VEC Q17 Q8 Q30 16 128 *)
  0x3dc02461;       (* arm_LDR Q1 X3 (Immediate_Offset (word 144)) *)
  0x4f50da29;       (* arm_SQRDMULH_VEC Q9 Q17 (Q0 :> LANE_H 5) 16 128 *)
  0x3c840465;       (* arm_STR Q5 X3 (Postimmediate_Offset (word 64)) *)
  0x3dc01c7e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 112)) *)
  0x6e70854a;       (* arm_SUB_VEC Q10 Q10 Q16 16 128 *)
  0x3dc01070;       (* arm_LDR Q16 X3 (Immediate_Offset (word 64)) *)
  0x6e7cb558;       (* arm_SQRDMULH_VEC Q24 Q10 Q28 16 128 *)
  0x4e799d4d;       (* arm_MUL_VEC Q13 Q10 Q25 16 128 *)
  0x6e668575;       (* arm_SUB_VEC Q21 Q11 Q6 16 128 *)
  0x4e9e284f;       (* arm_TRN1 Q15 Q2 Q30 32 128 *)
  0x4e9e685f;       (* arm_TRN2 Q31 Q2 Q30 32 128 *)
  0x6f47430d;       (* arm_MLS_VEC Q13 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6e9ebd;       (* arm_MUL_VEC Q29 Q21 Q14 16 128 *)
  0x3dc0144c;       (* arm_LDR Q12 X2 (Immediate_Offset (word 80)) *)
  0x6e7a85bc;       (* arm_SUB_VEC Q28 Q13 Q26 16 128 *)
  0x4e816a0a;       (* arm_TRN2 Q10 Q16 Q1 32 128 *)
  0x4e66857e;       (* arm_ADD_VEC Q30 Q11 Q6 16 128 *)
  0x6e72b782;       (* arm_SQRDMULH_VEC Q2 Q28 Q18 16 128 *)
  0x4e6e9f88;       (* arm_MUL_VEC Q8 Q28 Q14 16 128 *)
  0x6e72b6b2;       (* arm_SQRDMULH_VEC Q18 Q21 Q18 16 128 *)
  0x3cc6044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 96)) *)
  0x6f474048;       (* arm_MLS_VEC Q8 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7a85ab;       (* arm_ADD_VEC Q11 Q13 Q26 16 128 *)
  0x6f47425d;       (* arm_MLS_VEC Q29 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d2d4;       (* arm_SQRDMULH_VEC Q20 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x4e8b2bd7;       (* arm_TRN1 Q23 Q30 Q11 32 128 *)
  0x4e8b6bdc;       (* arm_TRN2 Q28 Q30 Q11 32 128 *)
  0x4e886bad;       (* arm_TRN2 Q13 Q29 Q8 32 128 *)
  0x4e882bab;       (* arm_TRN1 Q11 Q29 Q8 32 128 *)
  0x6f47429b;       (* arm_MLS_VEC Q27 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4ecd2b95;       (* arm_TRN1 Q21 Q28 Q13 64 128 *)
  0x4ecb6ae8;       (* arm_TRN2 Q8 Q23 Q11 64 128 *)
  0x4ecb2af8;       (* arm_TRN1 Q24 Q23 Q11 64 128 *)
  0x4f408a3a;       (* arm_MUL_VEC Q26 Q17 (Q0 :> LANE_H 4) 16 128 *)
  0x4ecd6b9e;       (* arm_TRN2 Q30 Q28 Q13 64 128 *)
  0x4e758704;       (* arm_ADD_VEC Q4 Q24 Q21 16 128 *)
  0x4e7e850b;       (* arm_ADD_VEC Q11 Q8 Q30 16 128 *)
  0x6f47413a;       (* arm_MLS_VEC Q26 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c091;       (* arm_SQDMULH_VEC Q17 Q4 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c17d;       (* arm_SQDMULH_VEC Q29 Q11 (Q7 :> LANE_H 1) 16 128 *)
  0x4edf6959;       (* arm_TRN2 Q25 Q10 Q31 64 128 *)
  0x4e7a8762;       (* arm_ADD_VEC Q2 Q27 Q26 16 128 *)
  0x4f15263c;       (* arm_SRSHR_VEC Q28 Q17 11 16 128 *)
  0x4f1527ad;       (* arm_SRSHR_VEC Q13 Q29 11 16 128 *)
  0x4f57c054;       (* arm_SQDMULH_VEC Q20 Q2 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7a8765;       (* arm_SUB_VEC Q5 Q27 Q26 16 128 *)
  0x6f474384;       (* arm_MLS_VEC Q4 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741ab;       (* arm_MLS_VEC Q11 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152697;       (* arm_SRSHR_VEC Q23 Q20 11 16 128 *)
  0x4f50d0b1;       (* arm_SQRDMULH_VEC Q17 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4080a9;       (* arm_MUL_VEC Q9 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4742e2;       (* arm_MLS_VEC Q2 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6b849d;       (* arm_SUB_VEC Q29 Q4 Q11 16 128 *)
  0x3cc10420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 16)) *)
  0x3c9d0062;       (* arm_STR Q2 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e812a02;       (* arm_TRN1 Q2 Q16 Q1 32 128 *)
  0x4f50d3a3;       (* arm_SQRDMULH_VEC Q3 Q29 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4083a6;       (* arm_MUL_VEC Q6 Q29 (Q0 :> LANE_H 0) 16 128 *)
  0x4ecf6854;       (* arm_TRN2 Q20 Q2 Q15 64 128 *)
  0x6f474229;       (* arm_MLS_VEC Q9 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6e798685;       (* arm_SUB_VEC Q5 Q20 Q25 16 128 *)
  0x6f474066;       (* arm_MLS_VEC Q6 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6e758716;       (* arm_SUB_VEC Q22 Q24 Q21 16 128 *)
  0x3c9f0069;       (* arm_STR Q9 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e6cb4ac;       (* arm_SQRDMULH_VEC Q12 Q5 Q12 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff5e4;       (* arm_CBNZ X4 (word 2096828) *)
  0x4f6082d5;       (* arm_MUL_VEC Q21 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x4e739cbc;       (* arm_MUL_VEC Q28 Q5 Q19 16 128 *)
  0x4edf294a;       (* arm_TRN1 Q10 Q10 Q31 64 128 *)
  0x4ecf2842;       (* arm_TRN1 Q2 Q2 Q15 64 128 *)
  0x4e6b848b;       (* arm_ADD_VEC Q11 Q4 Q11 16 128 *)
  0x6e7e851e;       (* arm_SUB_VEC Q30 Q8 Q30 16 128 *)
  0x4e798697;       (* arm_ADD_VEC Q23 Q20 Q25 16 128 *)
  0x4e6a8458;       (* arm_ADD_VEC Q24 Q2 Q10 16 128 *)
  0x4f408bc8;       (* arm_MUL_VEC Q8 Q30 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50dbc5;       (* arm_SQRDMULH_VEC Q5 Q30 (Q0 :> LANE_H 5) 16 128 *)
  0x4f70d2d6;       (* arm_SQRDMULH_VEC Q22 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x4e77871e;       (* arm_ADD_VEC Q30 Q24 Q23 16 128 *)
  0x3cdd005a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f4740a8;       (* arm_MLS_VEC Q8 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6a8445;       (* arm_SUB_VEC Q5 Q2 Q10 16 128 *)
  0x3cdc004d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6f4742d5;       (* arm_MLS_VEC Q21 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800866;       (* arm_STR Q6 X3 (Immediate_Offset (word 32)) *)
  0x4e6d9ca3;       (* arm_MUL_VEC Q3 Q5 Q13 16 128 *)
  0x6e7ab4b6;       (* arm_SQRDMULH_VEC Q22 Q5 Q26 16 128 *)
  0x6e6886b2;       (* arm_SUB_VEC Q18 Q21 Q8 16 128 *)
  0x6f47419c;       (* arm_MLS_VEC Q28 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x3c84046b;       (* arm_STR Q11 X3 (Postimmediate_Offset (word 64)) *)
  0x6f4742c3;       (* arm_MLS_VEC Q3 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d250;       (* arm_SQRDMULH_VEC Q16 Q18 (Q0 :> LANE_H 1) 16 128 *)
  0x6e77870a;       (* arm_SUB_VEC Q10 Q24 Q23 16 128 *)
  0x4f408251;       (* arm_MUL_VEC Q17 Q18 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7c846b;       (* arm_SUB_VEC Q11 Q3 Q28 16 128 *)
  0x4e6e9d4d;       (* arm_MUL_VEC Q13 Q10 Q14 16 128 *)
  0x4e7c8476;       (* arm_ADD_VEC Q22 Q3 Q28 16 128 *)
  0x4e6e9d6e;       (* arm_MUL_VEC Q14 Q11 Q14 16 128 *)
  0x3cdb005a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4e966bc2;       (* arm_TRN2 Q2 Q30 Q22 32 128 *)
  0x6f474211;       (* arm_MLS_VEC Q17 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7ab54a;       (* arm_SQRDMULH_VEC Q10 Q10 Q26 16 128 *)
  0x6e7ab56b;       (* arm_SQRDMULH_VEC Q11 Q11 Q26 16 128 *)
  0x3cc10429;       (* arm_LDR Q9 X1 (Postimmediate_Offset (word 16)) *)
  0x6f47414d;       (* arm_MLS_VEC Q13 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47416e;       (* arm_MLS_VEC Q14 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e962bc6;       (* arm_TRN1 Q6 Q30 Q22 32 128 *)
  0x4e6886a8;       (* arm_ADD_VEC Q8 Q21 Q8 16 128 *)
  0x3c9f0071;       (* arm_STR Q17 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e8e69a0;       (* arm_TRN2 Q0 Q13 Q14 32 128 *)
  0x4e8e29a1;       (* arm_TRN1 Q1 Q13 Q14 32 128 *)
  0x4f57c10d;       (* arm_SQDMULH_VEC Q13 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x4ec02858;       (* arm_TRN1 Q24 Q2 Q0 64 128 *)
  0x4ec06842;       (* arm_TRN2 Q2 Q2 Q0 64 128 *)
  0x4ec168da;       (* arm_TRN2 Q26 Q6 Q1 64 128 *)
  0x4ec128cb;       (* arm_TRN1 Q11 Q6 Q1 64 128 *)
  0x4e628756;       (* arm_ADD_VEC Q22 Q26 Q2 16 128 *)
  0x6e78857c;       (* arm_SUB_VEC Q28 Q11 Q24 16 128 *)
  0x6e62875b;       (* arm_SUB_VEC Q27 Q26 Q2 16 128 *)
  0x4e78856a;       (* arm_ADD_VEC Q10 Q11 Q24 16 128 *)
  0x4f79d38b;       (* arm_SQRDMULH_VEC Q11 Q28 (Q9 :> LANE_H 3) 16 128 *)
  0x4f698398;       (* arm_MUL_VEC Q24 Q28 (Q9 :> LANE_H 2) 16 128 *)
  0x4f57c2c1;       (* arm_SQDMULH_VEC Q1 Q22 (Q7 :> LANE_H 1) 16 128 *)
  0x4f59db60;       (* arm_SQRDMULH_VEC Q0 Q27 (Q9 :> LANE_H 5) 16 128 *)
  0x4f1525ac;       (* arm_SRSHR_VEC Q12 Q13 11 16 128 *)
  0x6f474178;       (* arm_MLS_VEC Q24 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c14e;       (* arm_SQDMULH_VEC Q14 Q10 (Q7 :> LANE_H 1) 16 128 *)
  0x4f498b7b;       (* arm_MUL_VEC Q27 Q27 (Q9 :> LANE_H 4) 16 128 *)
  0x6f474188;       (* arm_MLS_VEC Q8 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152425;       (* arm_SRSHR_VEC Q5 Q1 11 16 128 *)
  0x4f1525ce;       (* arm_SRSHR_VEC Q14 Q14 11 16 128 *)
  0x6f47401b;       (* arm_MLS_VEC Q27 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740b6;       (* arm_MLS_VEC Q22 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741ca;       (* arm_MLS_VEC Q10 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9d0068;       (* arm_STR Q8 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x6e7b8702;       (* arm_SUB_VEC Q2 Q24 Q27 16 128 *)
  0x4e7b870e;       (* arm_ADD_VEC Q14 Q24 Q27 16 128 *)
  0x6e76854b;       (* arm_SUB_VEC Q11 Q10 Q22 16 128 *)
  0x4e768554;       (* arm_ADD_VEC Q20 Q10 Q22 16 128 *)
  0x4f57c1d6;       (* arm_SQDMULH_VEC Q22 Q14 (Q7 :> LANE_H 1) 16 128 *)
  0x4f59d168;       (* arm_SQRDMULH_VEC Q8 Q11 (Q9 :> LANE_H 1) 16 128 *)
  0x4f49817b;       (* arm_MUL_VEC Q27 Q11 (Q9 :> LANE_H 0) 16 128 *)
  0x4f59d040;       (* arm_SQRDMULH_VEC Q0 Q2 (Q9 :> LANE_H 1) 16 128 *)
  0x4f49804b;       (* arm_MUL_VEC Q11 Q2 (Q9 :> LANE_H 0) 16 128 *)
  0x4f1526ca;       (* arm_SRSHR_VEC Q10 Q22 11 16 128 *)
  0x6f47411b;       (* arm_MLS_VEC Q27 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3c840474;       (* arm_STR Q20 X3 (Postimmediate_Offset (word 64)) *)
  0x6f47400b;       (* arm_MLS_VEC Q11 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47414e;       (* arm_MLS_VEC Q14 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9e007b;       (* arm_STR Q27 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9d006e;       (* arm_STR Q14 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc00002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 0)) *)
  0x3dc0100a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 64)) *)
  0x3dc0200b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 128)) *)
  0x6e6a844e;       (* arm_SUB_VEC Q14 Q2 Q10 16 128 *)
  0x4e6a8442;       (* arm_ADD_VEC Q2 Q2 Q10 16 128 *)
  0x3dc0300a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 192)) *)
  0x4f70d9c8;       (* arm_SQRDMULH_VEC Q8 Q14 (Q0 :> LANE_H 7) 16 128 *)
  0x4f6089ce;       (* arm_MUL_VEC Q14 Q14 (Q0 :> LANE_H 6) 16 128 *)
  0x6e6a8576;       (* arm_SUB_VEC Q22 Q11 Q10 16 128 *)
  0x4e6a856a;       (* arm_ADD_VEC Q10 Q11 Q10 16 128 *)
  0x3dc0700b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 448)) *)
  0x4e6a844d;       (* arm_ADD_VEC Q13 Q2 Q10 16 128 *)
  0x6e6a8442;       (* arm_SUB_VEC Q2 Q2 Q10 16 128 *)
  0x4f51d2ca;       (* arm_SQRDMULH_VEC Q10 Q22 (Q1 :> LANE_H 1) 16 128 *)
  0x4f4182d6;       (* arm_MUL_VEC Q22 Q22 (Q1 :> LANE_H 0) 16 128 *)
  0x6f47410e;       (* arm_MLS_VEC Q14 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d048;       (* arm_SQRDMULH_VEC Q8 Q2 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608042;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 2) 16 128 *)
  0x6f474156;       (* arm_MLS_VEC Q22 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0400a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 256)) *)
  0x6f474102;       (* arm_MLS_VEC Q2 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7685c8;       (* arm_SUB_VEC Q8 Q14 Q22 16 128 *)
  0x4e7685ce;       (* arm_ADD_VEC Q14 Q14 Q22 16 128 *)
  0x3dc06016;       (* arm_LDR Q22 X0 (Immediate_Offset (word 384)) *)
  0x4f70d118;       (* arm_SQRDMULH_VEC Q24 Q8 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608108;       (* arm_MUL_VEC Q8 Q8 (Q0 :> LANE_H 2) 16 128 *)
  0x6e6b86da;       (* arm_SUB_VEC Q26 Q22 Q11 16 128 *)
  0x4e6b86cb;       (* arm_ADD_VEC Q11 Q22 Q11 16 128 *)
  0x3dc05016;       (* arm_LDR Q22 X0 (Immediate_Offset (word 320)) *)
  0x4f51db50;       (* arm_SQRDMULH_VEC Q16 Q26 (Q1 :> LANE_H 5) 16 128 *)
  0x4f418b5a;       (* arm_MUL_VEC Q26 Q26 (Q1 :> LANE_H 4) 16 128 *)
  0x4e768557;       (* arm_ADD_VEC Q23 Q10 Q22 16 128 *)
  0x6e76854a;       (* arm_SUB_VEC Q10 Q10 Q22 16 128 *)
  0x6f474308;       (* arm_MLS_VEC Q8 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6b86f6;       (* arm_ADD_VEC Q22 Q23 Q11 16 128 *)
  0x4f618158;       (* arm_MUL_VEC Q24 Q10 (Q1 :> LANE_H 2) 16 128 *)
  0x4f71d14a;       (* arm_SQRDMULH_VEC Q10 Q10 (Q1 :> LANE_H 3) 16 128 *)
  0x6e7685b3;       (* arm_SUB_VEC Q19 Q13 Q22 16 128 *)
  0x4e7685b2;       (* arm_ADD_VEC Q18 Q13 Q22 16 128 *)
  0x6e6b86eb;       (* arm_SUB_VEC Q11 Q23 Q11 16 128 *)
  0x6f474158;       (* arm_MLS_VEC Q24 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47421a;       (* arm_MLS_VEC Q26 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d96a;       (* arm_SQRDMULH_VEC Q10 Q11 (Q0 :> LANE_H 5) 16 128 *)
  0x4f40896b;       (* arm_MUL_VEC Q11 Q11 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50d276;       (* arm_SQRDMULH_VEC Q22 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x6e7a870d;       (* arm_SUB_VEC Q13 Q24 Q26 16 128 *)
  0x4f408270;       (* arm_MUL_VEC Q16 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47414b;       (* arm_MLS_VEC Q11 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d9aa;       (* arm_SQRDMULH_VEC Q10 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x4f4089ad;       (* arm_MUL_VEC Q13 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x4e7a8718;       (* arm_ADD_VEC Q24 Q24 Q26 16 128 *)
  0x6e6b845a;       (* arm_SUB_VEC Q26 Q2 Q11 16 128 *)
  0x4e6b8449;       (* arm_ADD_VEC Q9 Q2 Q11 16 128 *)
  0x4e7885cb;       (* arm_ADD_VEC Q11 Q14 Q24 16 128 *)
  0x6e7885ce;       (* arm_SUB_VEC Q14 Q14 Q24 16 128 *)
  0x4f50d342;       (* arm_SQRDMULH_VEC Q2 Q26 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408358;       (* arm_MUL_VEC Q24 Q26 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47414d;       (* arm_MLS_VEC Q13 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742d0;       (* arm_MLS_VEC Q16 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d1ca;       (* arm_SQRDMULH_VEC Q10 Q14 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474058;       (* arm_MLS_VEC Q24 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6d8516;       (* arm_ADD_VEC Q22 Q8 Q13 16 128 *)
  0x3d804010;       (* arm_STR Q16 X0 (Immediate_Offset (word 256)) *)
  0x6e6d8502;       (* arm_SUB_VEC Q2 Q8 Q13 16 128 *)
  0x3d806018;       (* arm_STR Q24 X0 (Immediate_Offset (word 384)) *)
  0x4f4081cd;       (* arm_MUL_VEC Q13 Q14 (Q0 :> LANE_H 0) 16 128 *)
  0x3d803016;       (* arm_STR Q22 X0 (Immediate_Offset (word 192)) *)
  0x4f50d055;       (* arm_SQRDMULH_VEC Q21 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc02406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 144)) *)
  0x3dc0340e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 208)) *)
  0x6f47414d;       (* arm_MLS_VEC Q13 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80100b;       (* arm_STR Q11 X0 (Immediate_Offset (word 64)) *)
  0x6e6e84ca;       (* arm_SUB_VEC Q10 Q6 Q14 16 128 *)
  0x3dc0040b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 16)) *)
  0x4f51d153;       (* arm_SQRDMULH_VEC Q19 Q10 (Q1 :> LANE_H 1) 16 128 *)
  0x4f418154;       (* arm_MUL_VEC Q20 Q10 (Q1 :> LANE_H 0) 16 128 *)
  0x3dc0141c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 80)) *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6f474274;       (* arm_MLS_VEC Q20 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0741f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 464)) *)
  0x6e7c8576;       (* arm_SUB_VEC Q22 Q11 Q28 16 128 *)
  0x3dc0441e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 272)) *)
  0x4f70dac8;       (* arm_SQRDMULH_VEC Q8 Q22 (Q0 :> LANE_H 7) 16 128 *)
  0x4f608ac3;       (* arm_MUL_VEC Q3 Q22 (Q0 :> LANE_H 6) 16 128 *)
  0x4f408045;       (* arm_MUL_VEC Q5 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x3d80500d;       (* arm_STR Q13 X0 (Immediate_Offset (word 320)) *)
  0x4e7c856a;       (* arm_ADD_VEC Q10 Q11 Q28 16 128 *)
  0x3dc05416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 336)) *)
  0x3dc06404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 400)) *)
  0x6e7687d7;       (* arm_SUB_VEC Q23 Q30 Q22 16 128 *)
  0x4e7687db;       (* arm_ADD_VEC Q27 Q30 Q22 16 128 *)
  0x6f474103;       (* arm_MLS_VEC Q3 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742a5;       (* arm_MLS_VEC Q5 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0080b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 32)) *)
  0x6e7f8491;       (* arm_SUB_VEC Q17 Q4 Q31 16 128 *)
  0x4e6e84c2;       (* arm_ADD_VEC Q2 Q6 Q14 16 128 *)
  0x4f6182f3;       (* arm_MUL_VEC Q19 Q23 (Q1 :> LANE_H 2) 16 128 *)
  0x6e748476;       (* arm_SUB_VEC Q22 Q3 Q20 16 128 *)
  0x4e62854e;       (* arm_ADD_VEC Q14 Q10 Q2 16 128 *)
  0x6e628558;       (* arm_SUB_VEC Q24 Q10 Q2 16 128 *)
  0x4f71d2e2;       (* arm_SQRDMULH_VEC Q2 Q23 (Q1 :> LANE_H 3) 16 128 *)
  0x4f70d2de;       (* arm_SQRDMULH_VEC Q30 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6082d7;       (* arm_MUL_VEC Q23 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x4f51da2f;       (* arm_SQRDMULH_VEC Q15 Q17 (Q1 :> LANE_H 5) 16 128 *)
  0x6f474053;       (* arm_MLS_VEC Q19 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7f8482;       (* arm_ADD_VEC Q2 Q4 Q31 16 128 *)
  0x4f418a35;       (* arm_MUL_VEC Q21 Q17 (Q1 :> LANE_H 4) 16 128 *)
  0x4f70d316;       (* arm_SQRDMULH_VEC Q22 Q24 (Q0 :> LANE_H 3) 16 128 *)
  0x6e62877a;       (* arm_SUB_VEC Q26 Q27 Q2 16 128 *)
  0x4e628768;       (* arm_ADD_VEC Q8 Q27 Q2 16 128 *)
  0x4f60831c;       (* arm_MUL_VEC Q28 Q24 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50db4a;       (* arm_SQRDMULH_VEC Q10 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408b5f;       (* arm_MUL_VEC Q31 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x6f4741f5;       (* arm_MLS_VEC Q21 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742dc;       (* arm_MLS_VEC Q28 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6885d1;       (* arm_SUB_VEC Q17 Q14 Q8 16 128 *)
  0x6f47415f;       (* arm_MLS_VEC Q31 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6e75867b;       (* arm_SUB_VEC Q27 Q19 Q21 16 128 *)
  0x4f50d23d;       (* arm_SQRDMULH_VEC Q29 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40822a;       (* arm_MUL_VEC Q10 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7f878f;       (* arm_SUB_VEC Q15 Q28 Q31 16 128 *)
  0x4f50db71;       (* arm_SQRDMULH_VEC Q17 Q27 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408b79;       (* arm_MUL_VEC Q25 Q27 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50d1e6;       (* arm_SQRDMULH_VEC Q6 Q15 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4081fb;       (* arm_MUL_VEC Q27 Q15 (Q0 :> LANE_H 0) 16 128 *)
  0x4e758670;       (* arm_ADD_VEC Q16 Q19 Q21 16 128 *)
  0x6f474239;       (* arm_MLS_VEC Q25 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743d7;       (* arm_MLS_VEC Q23 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740db;       (* arm_MLS_VEC Q27 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc02806;       (* arm_LDR Q6 X0 (Immediate_Offset (word 160)) *)
  0x4e7986f6;       (* arm_ADD_VEC Q22 Q23 Q25 16 128 *)
  0x3d80641b;       (* arm_STR Q27 X0 (Immediate_Offset (word 400)) *)
  0x4e748464;       (* arm_ADD_VEC Q4 Q3 Q20 16 128 *)
  0x3d803416;       (* arm_STR Q22 X0 (Immediate_Offset (word 208)) *)
  0x6f4743aa;       (* arm_MLS_VEC Q10 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x3d807005;       (* arm_STR Q5 X0 (Immediate_Offset (word 448)) *)
  0x4e708494;       (* arm_ADD_VEC Q20 Q4 Q16 16 128 *)
  0x3c810412;       (* arm_STR Q18 X0 (Postimmediate_Offset (word 16)) *)
  0x6e708492;       (* arm_SUB_VEC Q18 Q4 Q16 16 128 *)
  0x3d80400a;       (* arm_STR Q10 X0 (Immediate_Offset (word 256)) *)
  0x6e7986e2;       (* arm_SUB_VEC Q2 Q23 Q25 16 128 *)
  0x4f50d24c;       (* arm_SQRDMULH_VEC Q12 Q18 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40824d;       (* arm_MUL_VEC Q13 Q18 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6885d2;       (* arm_ADD_VEC Q18 Q14 Q8 16 128 *)
  0x3dc0340e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 208)) *)
  0x6f47418d;       (* arm_MLS_VEC Q13 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 112)) *)
  0x6e6e84c3;       (* arm_SUB_VEC Q3 Q6 Q14 16 128 *)
  0x4e7f8789;       (* arm_ADD_VEC Q9 Q28 Q31 16 128 *)
  0x3d801014;       (* arm_STR Q20 X0 (Immediate_Offset (word 64)) *)
  0x4f51d073;       (* arm_SQRDMULH_VEC Q19 Q3 (Q1 :> LANE_H 1) 16 128 *)
  0x4f418074;       (* arm_MUL_VEC Q20 Q3 (Q1 :> LANE_H 0) 16 128 *)
  0x4f50d055;       (* arm_SQRDMULH_VEC Q21 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc0141c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 80)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6f474274;       (* arm_MLS_VEC Q20 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7c856a;       (* arm_SUB_VEC Q10 Q11 Q28 16 128 *)
  0x4e7c856b;       (* arm_ADD_VEC Q11 Q11 Q28 16 128 *)
  0x4f408042;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x3d80500d;       (* arm_STR Q13 X0 (Immediate_Offset (word 320)) *)
  0x4e6e84d9;       (* arm_ADD_VEC Q25 Q6 Q14 16 128 *)
  0x3c810412;       (* arm_STR Q18 X0 (Postimmediate_Offset (word 16)) *)
  0x4f70d951;       (* arm_SQRDMULH_VEC Q17 Q10 (Q0 :> LANE_H 7) 16 128 *)
  0x3d801c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 112)) *)
  0x3dc07008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 448)) *)
  0x3dc0400d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 256)) *)
  0x3dc0601a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 384)) *)
  0x3dc05018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 320)) *)
  0x4e68874f;       (* arm_ADD_VEC Q15 Q26 Q8 16 128 *)
  0x6e688748;       (* arm_SUB_VEC Q8 Q26 Q8 16 128 *)
  0x6e7885ac;       (* arm_SUB_VEC Q12 Q13 Q24 16 128 *)
  0x4e7885b8;       (* arm_ADD_VEC Q24 Q13 Q24 16 128 *)
  0x4f51d912;       (* arm_SQRDMULH_VEC Q18 Q8 (Q1 :> LANE_H 5) 16 128 *)
  0x4f61819a;       (* arm_MUL_VEC Q26 Q12 (Q1 :> LANE_H 2) 16 128 *)
  0x4f418908;       (* arm_MUL_VEC Q8 Q8 (Q1 :> LANE_H 4) 16 128 *)
  0x4f71d190;       (* arm_SQRDMULH_VEC Q16 Q12 (Q1 :> LANE_H 3) 16 128 *)
  0x4f60894a;       (* arm_MUL_VEC Q10 Q10 (Q0 :> LANE_H 6) 16 128 *)
  0x4e798576;       (* arm_ADD_VEC Q22 Q11 Q25 16 128 *)
  0x6f474248;       (* arm_MLS_VEC Q8 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47421a;       (* arm_MLS_VEC Q26 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47422a;       (* arm_MLS_VEC Q10 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6f8717;       (* arm_ADD_VEC Q23 Q24 Q15 16 128 *)
  0x6e79856b;       (* arm_SUB_VEC Q11 Q11 Q25 16 128 *)
  0x6e688743;       (* arm_SUB_VEC Q3 Q26 Q8 16 128 *)
  0x6e74854e;       (* arm_SUB_VEC Q14 Q10 Q20 16 128 *)
  0x6e7786d3;       (* arm_SUB_VEC Q19 Q22 Q23 16 128 *)
  0x4f408872;       (* arm_MUL_VEC Q18 Q3 (Q0 :> LANE_H 4) 16 128 *)
  0x4f70d1d1;       (* arm_SQRDMULH_VEC Q17 Q14 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6081ce;       (* arm_MUL_VEC Q14 Q14 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50d863;       (* arm_SQRDMULH_VEC Q3 Q3 (Q0 :> LANE_H 5) 16 128 *)
  0x6e6f8710;       (* arm_SUB_VEC Q16 Q24 Q15 16 128 *)
  0x6f4742a2;       (* arm_MLS_VEC Q2 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47422e;       (* arm_MLS_VEC Q14 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474072;       (* arm_MLS_VEC Q18 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50da1f;       (* arm_SQRDMULH_VEC Q31 Q16 (Q0 :> LANE_H 5) 16 128 *)
  0x3d806c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 432)) *)
  0x4f408a0d;       (* arm_MUL_VEC Q13 Q16 (Q0 :> LANE_H 4) 16 128 *)
  0x4e7285d8;       (* arm_ADD_VEC Q24 Q14 Q18 16 128 *)
  0x4f70d162;       (* arm_SQRDMULH_VEC Q2 Q11 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608175;       (* arm_MUL_VEC Q21 Q11 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4743ed;       (* arm_MLS_VEC Q13 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e688750;       (* arm_ADD_VEC Q16 Q26 Q8 16 128 *)
  0x4e74855c;       (* arm_ADD_VEC Q28 Q10 Q20 16 128 *)
  0x6f474055;       (* arm_MLS_VEC Q21 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7285ce;       (* arm_SUB_VEC Q14 Q14 Q18 16 128 *)
  0x4e708782;       (* arm_ADD_VEC Q2 Q28 Q16 16 128 *)
  0x6e70878a;       (* arm_SUB_VEC Q10 Q28 Q16 16 128 *)
  0x6e6d86b0;       (* arm_SUB_VEC Q16 Q21 Q13 16 128 *)
  0x4f50d27b;       (* arm_SQRDMULH_VEC Q27 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40827a;       (* arm_MUL_VEC Q26 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d213;       (* arm_SQRDMULH_VEC Q19 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40821c;       (* arm_MUL_VEC Q28 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d1c8;       (* arm_SQRDMULH_VEC Q8 Q14 (Q0 :> LANE_H 1) 16 128 *)
  0x6f47437a;       (* arm_MLS_VEC Q26 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4081ce;       (* arm_MUL_VEC Q14 Q14 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47427c;       (* arm_MLS_VEC Q28 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d154;       (* arm_SQRDMULH_VEC Q20 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x3d80401a;       (* arm_STR Q26 X0 (Immediate_Offset (word 256)) *)
  0x4f40814a;       (* arm_MUL_VEC Q10 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x3d80601c;       (* arm_STR Q28 X0 (Immediate_Offset (word 384)) *)
  0x4e7786d6;       (* arm_ADD_VEC Q22 Q22 Q23 16 128 *)
  0x3d803018;       (* arm_STR Q24 X0 (Immediate_Offset (word 192)) *)
  0x6f47428a;       (* arm_MLS_VEC Q10 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801002;       (* arm_STR Q2 X0 (Immediate_Offset (word 64)) *)
  0x6f47410e;       (* arm_MLS_VEC Q14 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3c810416;       (* arm_STR Q22 X0 (Postimmediate_Offset (word 16)) *)
  0x4e6d86ab;       (* arm_ADD_VEC Q11 Q21 Q13 16 128 *)
  0x3d804c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 304)) *)
  0x3d801c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 112)) *)
  0x3d806c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 432)) *)
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
