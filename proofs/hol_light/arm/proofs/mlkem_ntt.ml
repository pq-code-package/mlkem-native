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
  0x3dc06416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 400)) *)
  0x3dc07003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 448)) *)
  0x3dc0100e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 64)) *)
  0x3dc07409;       (* arm_LDR Q9 X0 (Immediate_Offset (word 464)) *)
  0x3dc06010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 384)) *)
  0x3dc0500d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 320)) *)
  0x3dc03017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 192)) *)
  0x3dc04413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 272)) *)
  0x4f50d07c;       (* arm_SQRDMULH_VEC Q28 Q3 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc03405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 208)) *)
  0x3dc04014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 256)) *)
  0x3dc0201f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 128)) *)
  0x4f408131;       (* arm_MUL_VEC Q17 Q9 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc00412;       (* arm_LDR Q18 X0 (Immediate_Offset (word 16)) *)
  0x3dc05404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 336)) *)
  0x3dc02406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 144)) *)
  0x4f50d128;       (* arm_SQRDMULH_VEC Q8 Q9 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc0000b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 0)) *)
  0x4f50d1aa;       (* arm_SQRDMULH_VEC Q10 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40807a;       (* arm_MUL_VEC Q26 Q3 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc01403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 80)) *)
  0x4f4081be;       (* arm_MUL_VEC Q30 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47415e;       (* arm_MLS_VEC Q30 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47439a;       (* arm_MLS_VEC Q26 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408275;       (* arm_MUL_VEC Q21 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7e85c2;       (* arm_ADD_VEC Q2 Q14 Q30 16 128 *)
  0x4f50d2cd;       (* arm_SQRDMULH_VEC Q13 Q22 (Q0 :> LANE_H 1) 16 128 *)
  0x4e7a86fd;       (* arm_ADD_VEC Q29 Q23 Q26 16 128 *)
  0x6e7a86fb;       (* arm_SUB_VEC Q27 Q23 Q26 16 128 *)
  0x6f474111;       (* arm_MLS_VEC Q17 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7e85da;       (* arm_SUB_VEC Q26 Q14 Q30 16 128 *)
  0x4f408217;       (* arm_MUL_VEC Q23 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d20a;       (* arm_SQRDMULH_VEC Q10 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40808c;       (* arm_MUL_VEC Q12 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d099;       (* arm_SQRDMULH_VEC Q25 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4082c9;       (* arm_MUL_VEC Q9 Q22 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4741a9;       (* arm_MLS_VEC Q9 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408284;       (* arm_MUL_VEC Q4 Q20 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d28f;       (* arm_SQRDMULH_VEC Q15 Q20 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474157;       (* arm_MLS_VEC Q23 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47432c;       (* arm_MLS_VEC Q12 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d26e;       (* arm_SQRDMULH_VEC Q14 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x4e7787f4;       (* arm_ADD_VEC Q20 Q31 Q23 16 128 *)
  0x6e7787f9;       (* arm_SUB_VEC Q25 Q31 Q23 16 128 *)
  0x4f408b7c;       (* arm_MUL_VEC Q28 Q27 (Q0 :> LANE_H 4) 16 128 *)
  0x4e6c8477;       (* arm_ADD_VEC Q23 Q3 Q12 16 128 *)
  0x6e6c847e;       (* arm_SUB_VEC Q30 Q3 Q12 16 128 *)
  0x6f4741e4;       (* arm_MLS_VEC Q4 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6984cc;       (* arm_ADD_VEC Q12 Q6 Q9 16 128 *)
  0x6e6984d6;       (* arm_SUB_VEC Q22 Q6 Q9 16 128 *)
  0x6f4741d5;       (* arm_MLS_VEC Q21 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d3a9;       (* arm_SQRDMULH_VEC Q9 Q29 (Q0 :> LANE_H 3) 16 128 *)
  0x4e648573;       (* arm_ADD_VEC Q19 Q11 Q4 16 128 *)
  0x4f70d198;       (* arm_SQRDMULH_VEC Q24 Q12 (Q0 :> LANE_H 3) 16 128 *)
  0x6e648570;       (* arm_SUB_VEC Q16 Q11 Q4 16 128 *)
  0x4e75864a;       (* arm_ADD_VEC Q10 Q18 Q21 16 128 *)
  0x6e758643;       (* arm_SUB_VEC Q3 Q18 Q21 16 128 *)
  0x4f50db6b;       (* arm_SQRDMULH_VEC Q11 Q27 (Q0 :> LANE_H 5) 16 128 *)
  0x4e7184bf;       (* arm_ADD_VEC Q31 Q5 Q17 16 128 *)
  0x4f6083b2;       (* arm_MUL_VEC Q18 Q29 (Q0 :> LANE_H 2) 16 128 *)
  0x4f408b3d;       (* arm_MUL_VEC Q29 Q25 (Q0 :> LANE_H 4) 16 128 *)
  0x6f474132;       (* arm_MLS_VEC Q18 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47417c;       (* arm_MLS_VEC Q28 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d289;       (* arm_SQRDMULH_VEC Q9 Q20 (Q0 :> LANE_H 3) 16 128 *)
  0x6e72844d;       (* arm_SUB_VEC Q13 Q2 Q18 16 128 *)
  0x4e728444;       (* arm_ADD_VEC Q4 Q2 Q18 16 128 *)
  0x4f70d3eb;       (* arm_SQRDMULH_VEC Q11 Q31 (Q0 :> LANE_H 3) 16 128 *)
  0x4e7c8755;       (* arm_ADD_VEC Q21 Q26 Q28 16 128 *)
  0x6e7c874e;       (* arm_SUB_VEC Q14 Q26 Q28 16 128 *)
  0x4f6083e6;       (* arm_MUL_VEC Q6 Q31 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50db28;       (* arm_SQRDMULH_VEC Q8 Q25 (Q0 :> LANE_H 5) 16 128 *)
  0x6f474166;       (* arm_MLS_VEC Q6 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d1af;       (* arm_SQRDMULH_VEC Q15 Q13 (Q1 :> LANE_H 1) 16 128 *)
  0x4f60829a;       (* arm_MUL_VEC Q26 Q20 (Q0 :> LANE_H 2) 16 128 *)
  0x4e6686eb;       (* arm_ADD_VEC Q11 Q23 Q6 16 128 *)
  0x6e6686f7;       (* arm_SUB_VEC Q23 Q23 Q6 16 128 *)
  0x4f71d2b2;       (* arm_SQRDMULH_VEC Q18 Q21 (Q1 :> LANE_H 3) 16 128 *)
  0x4f70d899;       (* arm_SQRDMULH_VEC Q25 Q4 (Q0 :> LANE_H 7) 16 128 *)
  0x4f51d9c6;       (* arm_SQRDMULH_VEC Q6 Q14 (Q1 :> LANE_H 5) 16 128 *)
  0x4f4189ce;       (* arm_MUL_VEC Q14 Q14 (Q1 :> LANE_H 4) 16 128 *)
  0x6f47413a;       (* arm_MLS_VEC Q26 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47411d;       (* arm_MLS_VEC Q29 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4181bc;       (* arm_MUL_VEC Q28 Q13 (Q1 :> LANE_H 0) 16 128 *)
  0x6e7a867b;       (* arm_SUB_VEC Q27 Q19 Q26 16 128 *)
  0x4e7a867a;       (* arm_ADD_VEC Q26 Q19 Q26 16 128 *)
  0x6f4741fc;       (* arm_MLS_VEC Q28 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7d860d;       (* arm_ADD_VEC Q13 Q16 Q29 16 128 *)
  0x4f608893;       (* arm_MUL_VEC Q19 Q4 (Q0 :> LANE_H 6) 16 128 *)
  0x6e7d8604;       (* arm_SUB_VEC Q4 Q16 Q29 16 128 *)
  0x4f608190;       (* arm_MUL_VEC Q16 Q12 (Q0 :> LANE_H 2) 16 128 *)
  0x4e7c877d;       (* arm_ADD_VEC Q29 Q27 Q28 16 128 *)
  0x4f6182a9;       (* arm_MUL_VEC Q9 Q21 (Q1 :> LANE_H 2) 16 128 *)
  0x3d80201d;       (* arm_STR Q29 X0 (Immediate_Offset (word 128)) *)
  0x6f474249;       (* arm_MLS_VEC Q9 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740ce;       (* arm_MLS_VEC Q14 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7c8768;       (* arm_SUB_VEC Q8 Q27 Q28 16 128 *)
  0x6f474333;       (* arm_MLS_VEC Q19 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x3d803008;       (* arm_STR Q8 X0 (Immediate_Offset (word 192)) *)
  0x4e6985bc;       (* arm_ADD_VEC Q28 Q13 Q9 16 128 *)
  0x6f474310;       (* arm_MLS_VEC Q16 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6985b5;       (* arm_SUB_VEC Q21 Q13 Q9 16 128 *)
  0x4e6e8489;       (* arm_ADD_VEC Q9 Q4 Q14 16 128 *)
  0x6e6e8484;       (* arm_SUB_VEC Q4 Q4 Q14 16 128 *)
  0x4f51d2f4;       (* arm_SQRDMULH_VEC Q20 Q23 (Q1 :> LANE_H 1) 16 128 *)
  0x4e73874f;       (* arm_ADD_VEC Q15 Q26 Q19 16 128 *)
  0x4f70d979;       (* arm_SQRDMULH_VEC Q25 Q11 (Q0 :> LANE_H 7) 16 128 *)
  0x6e738746;       (* arm_SUB_VEC Q6 Q26 Q19 16 128 *)
  0x3c81040f;       (* arm_STR Q15 X0 (Postimmediate_Offset (word 16)) *)
  0x6e708558;       (* arm_SUB_VEC Q24 Q10 Q16 16 128 *)
  0x4e70854c;       (* arm_ADD_VEC Q12 Q10 Q16 16 128 *)
  0x4f608970;       (* arm_MUL_VEC Q16 Q11 (Q0 :> LANE_H 6) 16 128 *)
  0x4f4182ee;       (* arm_MUL_VEC Q14 Q23 (Q1 :> LANE_H 0) 16 128 *)
  0x6f474330;       (* arm_MLS_VEC Q16 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50dad3;       (* arm_SQRDMULH_VEC Q19 Q22 (Q0 :> LANE_H 5) 16 128 *)
  0x6f47428e;       (* arm_MLS_VEC Q14 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408ada;       (* arm_MUL_VEC Q26 Q22 (Q0 :> LANE_H 4) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6e7184b6;       (* arm_SUB_VEC Q22 Q5 Q17 16 128 *)
  0x3d800c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 48)) *)
  0x6f47427a;       (* arm_MLS_VEC Q26 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc03405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 208)) *)
  0x4e6e871b;       (* arm_ADD_VEC Q27 Q24 Q14 16 128 *)
  0x3dc07414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 464)) *)
  0x3dc0541f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 336)) *)
  0x4f50dad7;       (* arm_SQRDMULH_VEC Q23 Q22 (Q0 :> LANE_H 5) 16 128 *)
  0x3dc0240f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 144)) *)
  0x3dc06413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 400)) *)
  0x4f408ac8;       (* arm_MUL_VEC Q8 Q22 (Q0 :> LANE_H 4) 16 128 *)
  0x4e708582;       (* arm_ADD_VEC Q2 Q12 Q16 16 128 *)
  0x6e7a846a;       (* arm_SUB_VEC Q10 Q3 Q26 16 128 *)
  0x3dc0140b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 80)) *)
  0x4f4083f2;       (* arm_MUL_VEC Q18 Q31 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc0441d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 272)) *)
  0x3d806c04;       (* arm_STR Q4 X0 (Immediate_Offset (word 432)) *)
  0x3c810402;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
  0x4f50d3e4;       (* arm_SQRDMULH_VEC Q4 Q31 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc00002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 0)) *)
  0x6e6e870d;       (* arm_SUB_VEC Q13 Q24 Q14 16 128 *)
  0x3d80381c;       (* arm_STR Q28 X0 (Immediate_Offset (word 224)) *)
  0x4e7a8479;       (* arm_ADD_VEC Q25 Q3 Q26 16 128 *)
  0x4f50d28e;       (* arm_SQRDMULH_VEC Q14 Q20 (Q0 :> LANE_H 1) 16 128 *)
  0x6e708586;       (* arm_SUB_VEC Q6 Q12 Q16 16 128 *)
  0x3d804815;       (* arm_STR Q21 X0 (Immediate_Offset (word 288)) *)
  0x4f408291;       (* arm_MUL_VEC Q17 Q20 (Q0 :> LANE_H 0) 16 128 *)
  0x3d801c1b;       (* arm_STR Q27 X0 (Immediate_Offset (word 112)) *)
  0x3d805809;       (* arm_STR Q9 X0 (Immediate_Offset (word 352)) *)
  0x6f4742e8;       (* arm_MLS_VEC Q8 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x3d802c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 176)) *)
  0x4f50d274;       (* arm_SQRDMULH_VEC Q20 Q19 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408277;       (* arm_MUL_VEC Q23 Q19 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6887d5;       (* arm_ADD_VEC Q21 Q30 Q8 16 128 *)
  0x6f4741d1;       (* arm_MLS_VEC Q17 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6887db;       (* arm_SUB_VEC Q27 Q30 Q8 16 128 *)
  0x6f474297;       (* arm_MLS_VEC Q23 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51db76;       (* arm_SQRDMULH_VEC Q22 Q27 (Q1 :> LANE_H 5) 16 128 *)
  0x4e7184bc;       (* arm_ADD_VEC Q28 Q5 Q17 16 128 *)
  0x6f474092;       (* arm_MLS_VEC Q18 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7785f4;       (* arm_SUB_VEC Q20 Q15 Q23 16 128 *)
  0x4e7785ec;       (* arm_ADD_VEC Q12 Q15 Q23 16 128 *)
  0x4f418b77;       (* arm_MUL_VEC Q23 Q27 (Q1 :> LANE_H 4) 16 128 *)
  0x6f4742d7;       (* arm_MLS_VEC Q23 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e72856f;       (* arm_ADD_VEC Q15 Q11 Q18 16 128 *)
  0x6e72857e;       (* arm_SUB_VEC Q30 Q11 Q18 16 128 *)
  0x4f70d398;       (* arm_SQRDMULH_VEC Q24 Q28 (Q0 :> LANE_H 3) 16 128 *)
  0x4f70d19b;       (* arm_SQRDMULH_VEC Q27 Q12 (Q0 :> LANE_H 3) 16 128 *)
  0x6e778544;       (* arm_SUB_VEC Q4 Q10 Q23 16 128 *)
  0x4e778549;       (* arm_ADD_VEC Q9 Q10 Q23 16 128 *)
  0x4f60839a;       (* arm_MUL_VEC Q26 Q28 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50d3ae;       (* arm_SQRDMULH_VEC Q14 Q29 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4083ab;       (* arm_MUL_VEC Q11 Q29 (Q0 :> LANE_H 0) 16 128 *)
  0x4f608188;       (* arm_MUL_VEC Q8 Q12 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4741cb;       (* arm_MLS_VEC Q11 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d2ae;       (* arm_SQRDMULH_VEC Q14 Q21 (Q1 :> LANE_H 3) 16 128 *)
  0x6f474368;       (* arm_MLS_VEC Q8 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6b8456;       (* arm_ADD_VEC Q22 Q2 Q11 16 128 *)
  0x6e6b8443;       (* arm_SUB_VEC Q3 Q2 Q11 16 128 *)
  0x6f47431a;       (* arm_MLS_VEC Q26 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6182b7;       (* arm_MUL_VEC Q23 Q21 (Q1 :> LANE_H 2) 16 128 *)
  0x4e6886cc;       (* arm_ADD_VEC Q12 Q22 Q8 16 128 *)
  0x6e6886d8;       (* arm_SUB_VEC Q24 Q22 Q8 16 128 *)
  0x4f50da93;       (* arm_SQRDMULH_VEC Q19 Q20 (Q0 :> LANE_H 5) 16 128 *)
  0x6e7a85f0;       (* arm_SUB_VEC Q16 Q15 Q26 16 128 *)
  0x4e7a85f6;       (* arm_ADD_VEC Q22 Q15 Q26 16 128 *)
  0x6f4741d7;       (* arm_MLS_VEC Q23 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d21f;       (* arm_SQRDMULH_VEC Q31 Q16 (Q1 :> LANE_H 1) 16 128 *)
  0x4f70dacf;       (* arm_SQRDMULH_VEC Q15 Q22 (Q0 :> LANE_H 7) 16 128 *)
  0x4e77873c;       (* arm_ADD_VEC Q28 Q25 Q23 16 128 *)
  0x6e778735;       (* arm_SUB_VEC Q21 Q25 Q23 16 128 *)
  0x4f41820e;       (* arm_MUL_VEC Q14 Q16 (Q1 :> LANE_H 0) 16 128 *)
  0x4f608ad0;       (* arm_MUL_VEC Q16 Q22 (Q0 :> LANE_H 6) 16 128 *)
  0x6f4741f0;       (* arm_MLS_VEC Q16 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743ee;       (* arm_MLS_VEC Q14 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408a9a;       (* arm_MUL_VEC Q26 Q20 (Q0 :> LANE_H 4) 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6f47427a;       (* arm_MLS_VEC Q26 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7184b7;       (* arm_SUB_VEC Q23 Q5 Q17 16 128 *)
  0x3d806c04;       (* arm_STR Q4 X0 (Immediate_Offset (word 432)) *)
  0x6e70858b;       (* arm_SUB_VEC Q11 Q12 Q16 16 128 *)
  0x3d800c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 48)) *)
  0x4f50daf2;       (* arm_SQRDMULH_VEC Q18 Q23 (Q0 :> LANE_H 5) 16 128 *)
  0x3d805c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 368)) *)
  0x3d80100b;       (* arm_STR Q11 X0 (Immediate_Offset (word 64)) *)
  0x4e70858a;       (* arm_ADD_VEC Q10 Q12 Q16 16 128 *)
  0x3d803c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 240)) *)
  0x4e7a846c;       (* arm_ADD_VEC Q12 Q3 Q26 16 128 *)
  0x4f408af1;       (* arm_MUL_VEC Q17 Q23 (Q0 :> LANE_H 4) 16 128 *)
  0x3d804c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 304)) *)
  0x6e6e8715;       (* arm_SUB_VEC Q21 Q24 Q14 16 128 *)
  0x6f474251;       (* arm_MLS_VEC Q17 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x3c81040a;       (* arm_STR Q10 X0 (Postimmediate_Offset (word 16)) *)
  0x3d802c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 176)) *)
  0x4e6e8715;       (* arm_ADD_VEC Q21 Q24 Q14 16 128 *)
  0x6e7a846a;       (* arm_SUB_VEC Q10 Q3 Q26 16 128 *)
  0x3d801c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 112)) *)
  0x6e7187d7;       (* arm_SUB_VEC Q23 Q30 Q17 16 128 *)
  0x4e7187c5;       (* arm_ADD_VEC Q5 Q30 Q17 16 128 *)
  0x4f51daed;       (* arm_SQRDMULH_VEC Q13 Q23 (Q1 :> LANE_H 5) 16 128 *)
  0x4f418af2;       (* arm_MUL_VEC Q18 Q23 (Q1 :> LANE_H 4) 16 128 *)
  0x4f71d0b5;       (* arm_SQRDMULH_VEC Q21 Q5 (Q1 :> LANE_H 3) 16 128 *)
  0x6f4741b2;       (* arm_MLS_VEC Q18 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6180a8;       (* arm_MUL_VEC Q8 Q5 (Q1 :> LANE_H 2) 16 128 *)
  0x6f4742a8;       (* arm_MLS_VEC Q8 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e72854d;       (* arm_ADD_VEC Q13 Q10 Q18 16 128 *)
  0x3d805c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 368)) *)
  0x6e72854d;       (* arm_SUB_VEC Q13 Q10 Q18 16 128 *)
  0x6e688595;       (* arm_SUB_VEC Q21 Q12 Q8 16 128 *)
  0x4e688588;       (* arm_ADD_VEC Q8 Q12 Q8 16 128 *)
  0x3d806c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 432)) *)
  0x3d804c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 304)) *)
  0x3d803c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 240)) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc00c01;       (* arm_LDR Q1 X0 (Immediate_Offset (word 48)) *)
  0x3cc10425;       (* arm_LDR Q5 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc0105d;       (* arm_LDR Q29 X2 (Immediate_Offset (word 64)) *)
  0x3dc01c0d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 112)) *)
  0x3dc00810;       (* arm_LDR Q16 X0 (Immediate_Offset (word 32)) *)
  0x3dc00402;       (* arm_LDR Q2 X0 (Immediate_Offset (word 16)) *)
  0x3dc00008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 0)) *)
  0x3dc0180a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 96)) *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x4f55d02b;       (* arm_SQRDMULH_VEC Q11 Q1 (Q5 :> LANE_H 1) 16 128 *)
  0x3dc00c52;       (* arm_LDR Q18 X2 (Immediate_Offset (word 48)) *)
  0x4f55d203;       (* arm_SQRDMULH_VEC Q3 Q16 (Q5 :> LANE_H 1) 16 128 *)
  0x4f458037;       (* arm_MUL_VEC Q23 Q1 (Q5 :> LANE_H 0) 16 128 *)
  0x6f474177;       (* arm_MLS_VEC Q23 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0145b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 80)) *)
  0x4f458211;       (* arm_MUL_VEC Q17 Q16 (Q5 :> LANE_H 0) 16 128 *)
  0x6f474071;       (* arm_MLS_VEC Q17 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6e778455;       (* arm_SUB_VEC Q21 Q2 Q23 16 128 *)
  0x4e77845f;       (* arm_ADD_VEC Q31 Q2 Q23 16 128 *)
  0x4f55dabc;       (* arm_SQRDMULH_VEC Q28 Q21 (Q5 :> LANE_H 5) 16 128 *)
  0x4f75d3e6;       (* arm_SQRDMULH_VEC Q6 Q31 (Q5 :> LANE_H 3) 16 128 *)
  0x4e718517;       (* arm_ADD_VEC Q23 Q8 Q17 16 128 *)
  0x4f458aa1;       (* arm_MUL_VEC Q1 Q21 (Q5 :> LANE_H 4) 16 128 *)
  0x6e718510;       (* arm_SUB_VEC Q16 Q8 Q17 16 128 *)
  0x6f474381;       (* arm_MLS_VEC Q1 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6583e8;       (* arm_MUL_VEC Q8 Q31 (Q5 :> LANE_H 2) 16 128 *)
  0x6f4740c8;       (* arm_MLS_VEC Q8 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6e618605;       (* arm_SUB_VEC Q5 Q16 Q1 16 128 *)
  0x4f54d1ac;       (* arm_SQRDMULH_VEC Q12 Q13 (Q4 :> LANE_H 1) 16 128 *)
  0x4e618616;       (* arm_ADD_VEC Q22 Q16 Q1 16 128 *)
  0x3dc00441;       (* arm_LDR Q1 X2 (Immediate_Offset (word 16)) *)
  0x4e856ac0;       (* arm_TRN2 Q0 Q22 Q5 32 128 *)
  0x4f4481b0;       (* arm_MUL_VEC Q16 Q13 (Q4 :> LANE_H 0) 16 128 *)
  0x4e6886e6;       (* arm_ADD_VEC Q6 Q23 Q8 16 128 *)
  0x6e6886f8;       (* arm_SUB_VEC Q24 Q23 Q8 16 128 *)
  0x4f54d153;       (* arm_SQRDMULH_VEC Q19 Q10 (Q4 :> LANE_H 1) 16 128 *)
  0x4e852ad5;       (* arm_TRN1 Q21 Q22 Q5 32 128 *)
  0x4e9868d1;       (* arm_TRN2 Q17 Q6 Q24 32 128 *)
  0x6f474190;       (* arm_MLS_VEC Q16 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9828cb;       (* arm_TRN1 Q11 Q6 Q24 32 128 *)
  0x4ec06a29;       (* arm_TRN2 Q9 Q17 Q0 64 128 *)
  0x4f448148;       (* arm_MUL_VEC Q8 Q10 (Q4 :> LANE_H 0) 16 128 *)
  0x3cc60457;       (* arm_LDR Q23 X2 (Postimmediate_Offset (word 96)) *)
  0x4ed52963;       (* arm_TRN1 Q3 Q11 Q21 64 128 *)
  0x4ed5696e;       (* arm_TRN2 Q14 Q11 Q21 64 128 *)
  0x6e61b526;       (* arm_SQRDMULH_VEC Q6 Q9 Q1 16 128 *)
  0x3dc0140c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 80)) *)
  0x6e61b5d5;       (* arm_SQRDMULH_VEC Q21 Q14 Q1 16 128 *)
  0x4ec02a2d;       (* arm_TRN1 Q13 Q17 Q0 64 128 *)
  0x4e779d2b;       (* arm_MUL_VEC Q11 Q9 Q23 16 128 *)
  0x6e708594;       (* arm_SUB_VEC Q20 Q12 Q16 16 128 *)
  0x6f4740cb;       (* arm_MLS_VEC Q11 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f448a81;       (* arm_MUL_VEC Q1 Q20 (Q4 :> LANE_H 4) 16 128 *)
  0x4e779dda;       (* arm_MUL_VEC Q26 Q14 Q23 16 128 *)
  0x6e6b85b6;       (* arm_SUB_VEC Q22 Q13 Q11 16 128 *)
  0x4e6b85b8;       (* arm_ADD_VEC Q24 Q13 Q11 16 128 *)
  0x4f54da80;       (* arm_SQRDMULH_VEC Q0 Q20 (Q4 :> LANE_H 5) 16 128 *)
  0x6f4742ba;       (* arm_MLS_VEC Q26 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7bb6d9;       (* arm_SQRDMULH_VEC Q25 Q22 Q27 16 128 *)
  0x6e72b71c;       (* arm_SQRDMULH_VEC Q28 Q24 Q18 16 128 *)
  0x4e708585;       (* arm_ADD_VEC Q5 Q12 Q16 16 128 *)
  0x6e7a8466;       (* arm_SUB_VEC Q6 Q3 Q26 16 128 *)
  0x4e7d9ed2;       (* arm_MUL_VEC Q18 Q22 Q29 16 128 *)
  0x6f474332;       (* arm_MLS_VEC Q18 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474001;       (* arm_MLS_VEC Q1 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdc0059;       (* arm_LDR Q25 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4f6480b1;       (* arm_MUL_VEC Q17 Q5 (Q4 :> LANE_H 2) 16 128 *)
  0x6e7284d7;       (* arm_SUB_VEC Q23 Q6 Q18 16 128 *)
  0x4e7284dd;       (* arm_ADD_VEC Q29 Q6 Q18 16 128 *)
  0x4e799f0f;       (* arm_MUL_VEC Q15 Q24 Q25 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x4e976bb4;       (* arm_TRN2 Q20 Q29 Q23 32 128 *)
  0x3dc02c12;       (* arm_LDR Q18 X0 (Immediate_Offset (word 176)) *)
  0x4f74d0be;       (* arm_SQRDMULH_VEC Q30 Q5 (Q4 :> LANE_H 3) 16 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x4e972bb8;       (* arm_TRN1 Q24 Q29 Q23 32 128 *)
  0x3dc00455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 16)) *)
  0x3dc01016;       (* arm_LDR Q22 X0 (Immediate_Offset (word 64)) *)
  0x6f474268;       (* arm_MLS_VEC Q8 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc60446;       (* arm_LDR Q6 X2 (Postimmediate_Offset (word 96)) *)
  0x4e7a846c;       (* arm_ADD_VEC Q12 Q3 Q26 16 128 *)
  0x3dc02802;       (* arm_LDR Q2 X0 (Immediate_Offset (word 160)) *)
  0x4f44824b;       (* arm_MUL_VEC Q11 Q18 (Q4 :> LANE_H 0) 16 128 *)
  0x3dc02419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 144)) *)
  0x6f4743d1;       (* arm_MLS_VEC Q17 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6886cd;       (* arm_SUB_VEC Q13 Q22 Q8 16 128 *)
  0x4e6886d7;       (* arm_ADD_VEC Q23 Q22 Q8 16 128 *)
  0x4f54d249;       (* arm_SQRDMULH_VEC Q9 Q18 (Q4 :> LANE_H 1) 16 128 *)
  0x4e6185ba;       (* arm_ADD_VEC Q26 Q13 Q1 16 128 *)
  0x6e6185bb;       (* arm_SUB_VEC Q27 Q13 Q1 16 128 *)
  0x4f54d053;       (* arm_SQRDMULH_VEC Q19 Q2 (Q4 :> LANE_H 1) 16 128 *)
  0x6e7186f0;       (* arm_SUB_VEC Q16 Q23 Q17 16 128 *)
  0x4f448048;       (* arm_MUL_VEC Q8 Q2 (Q4 :> LANE_H 0) 16 128 *)
  0x4e7186fe;       (* arm_ADD_VEC Q30 Q23 Q17 16 128 *)
  0x4e9b6b4a;       (* arm_TRN2 Q10 Q26 Q27 32 128 *)
  0x6f47412b;       (* arm_MLS_VEC Q11 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4e906bc2;       (* arm_TRN2 Q2 Q30 Q16 32 128 *)
  0x4e902bc0;       (* arm_TRN1 Q0 Q30 Q16 32 128 *)
  0x6f47438f;       (* arm_MLS_VEC Q15 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4eca6857;       (* arm_TRN2 Q23 Q2 Q10 64 128 *)
  0x4eca284e;       (* arm_TRN1 Q14 Q2 Q10 64 128 *)
  0x3cde004a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x6e75b6ed;       (* arm_SQRDMULH_VEC Q13 Q23 Q21 16 128 *)
  0x6e6b8722;       (* arm_SUB_VEC Q2 Q25 Q11 16 128 *)
  0x4e6b8725;       (* arm_ADD_VEC Q5 Q25 Q11 16 128 *)
  0x4e669ef2;       (* arm_MUL_VEC Q18 Q23 Q6 16 128 *)
  0x4e6f8590;       (* arm_ADD_VEC Q16 Q12 Q15 16 128 *)
  0x6e6f8597;       (* arm_SUB_VEC Q23 Q12 Q15 16 128 *)
  0x4f6480b1;       (* arm_MUL_VEC Q17 Q5 (Q4 :> LANE_H 2) 16 128 *)
  0x4e9b2b5f;       (* arm_TRN1 Q31 Q26 Q27 32 128 *)
  0x3cdf004f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f4741b2;       (* arm_MLS_VEC Q18 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4e976a1e;       (* arm_TRN2 Q30 Q16 Q23 32 128 *)
  0x4edf6803;       (* arm_TRN2 Q3 Q0 Q31 64 128 *)
  0x3cdc005b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4ed46bda;       (* arm_TRN2 Q26 Q30 Q20 64 128 *)
  0x4f448841;       (* arm_MUL_VEC Q1 Q2 (Q4 :> LANE_H 4) 16 128 *)
  0x4e972a10;       (* arm_TRN1 Q16 Q16 Q23 32 128 *)
  0x3d800c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 48)) *)
  0x4e669c7a;       (* arm_MUL_VEC Q26 Q3 Q6 16 128 *)
  0x6e7285cd;       (* arm_SUB_VEC Q13 Q14 Q18 16 128 *)
  0x6e75b477;       (* arm_SQRDMULH_VEC Q23 Q3 Q21 16 128 *)
  0x4edf2803;       (* arm_TRN1 Q3 Q0 Q31 64 128 *)
  0x4ed82a0b;       (* arm_TRN1 Q11 Q16 Q24 64 128 *)
  0x6e6fb5b5;       (* arm_SQRDMULH_VEC Q21 Q13 Q15 16 128 *)
  0x3c84040b;       (* arm_STR Q11 X0 (Postimmediate_Offset (word 64)) *)
  0x4e6a9da0;       (* arm_MUL_VEC Q0 Q13 Q10 16 128 *)
  0x3cdd004d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f4742fa;       (* arm_MLS_VEC Q26 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7285d7;       (* arm_ADD_VEC Q23 Q14 Q18 16 128 *)
  0x4ed42bce;       (* arm_TRN1 Q14 Q30 Q20 64 128 *)
  0x6f4742a0;       (* arm_MLS_VEC Q0 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed86a15;       (* arm_TRN2 Q21 Q16 Q24 64 128 *)
  0x3c9d000e;       (* arm_STR Q14 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4f54d85f;       (* arm_SQRDMULH_VEC Q31 Q2 (Q4 :> LANE_H 5) 16 128 *)
  0x3c9e0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x6e6db6fc;       (* arm_SQRDMULH_VEC Q28 Q23 Q13 16 128 *)
  0x6e7a846d;       (* arm_SUB_VEC Q13 Q3 Q26 16 128 *)
  0x4e7b9eef;       (* arm_MUL_VEC Q15 Q23 Q27 16 128 *)
  0x4e6085bd;       (* arm_ADD_VEC Q29 Q13 Q0 16 128 *)
  0x6e6085b7;       (* arm_SUB_VEC Q23 Q13 Q0 16 128 *)
  0x6f4743e1;       (* arm_MLS_VEC Q1 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff704;       (* arm_CBNZ X4 (word 2096864) *)
  0x4f74d0ab;       (* arm_SQRDMULH_VEC Q11 Q5 (Q4 :> LANE_H 3) 16 128 *)
  0x4e972bb9;       (* arm_TRN1 Q25 Q29 Q23 32 128 *)
  0x3dc01018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 64)) *)
  0x4e976bae;       (* arm_TRN2 Q14 Q29 Q23 32 128 *)
  0x4e7a8474;       (* arm_ADD_VEC Q20 Q3 Q26 16 128 *)
  0x6f474268;       (* arm_MLS_VEC Q8 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc00440;       (* arm_LDR Q0 X2 (Immediate_Offset (word 16)) *)
  0x3dc0145e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 80)) *)
  0x3dc00c55;       (* arm_LDR Q21 X2 (Immediate_Offset (word 48)) *)
  0x3cc60444;       (* arm_LDR Q4 X2 (Postimmediate_Offset (word 96)) *)
  0x6f474171;       (* arm_MLS_VEC Q17 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x3cde0053;       (* arm_LDR Q19 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdc0045;       (* arm_LDR Q5 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6f47438f;       (* arm_MLS_VEC Q15 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e688717;       (* arm_SUB_VEC Q23 Q24 Q8 16 128 *)
  0x4e688703;       (* arm_ADD_VEC Q3 Q24 Q8 16 128 *)
  0x4e6186e8;       (* arm_ADD_VEC Q8 Q23 Q1 16 128 *)
  0x6e6186fd;       (* arm_SUB_VEC Q29 Q23 Q1 16 128 *)
  0x4e718469;       (* arm_ADD_VEC Q9 Q3 Q17 16 128 *)
  0x6e718472;       (* arm_SUB_VEC Q18 Q3 Q17 16 128 *)
  0x4e9d691f;       (* arm_TRN2 Q31 Q8 Q29 32 128 *)
  0x4e6f869a;       (* arm_ADD_VEC Q26 Q20 Q15 16 128 *)
  0x4e926930;       (* arm_TRN2 Q16 Q9 Q18 32 128 *)
  0x6e6f868b;       (* arm_SUB_VEC Q11 Q20 Q15 16 128 *)
  0x4edf6a11;       (* arm_TRN2 Q17 Q16 Q31 64 128 *)
  0x4e9d290a;       (* arm_TRN1 Q10 Q8 Q29 32 128 *)
  0x4e922921;       (* arm_TRN1 Q1 Q9 Q18 32 128 *)
  0x4e8b2b46;       (* arm_TRN1 Q6 Q26 Q11 32 128 *)
  0x4edf2a09;       (* arm_TRN1 Q9 Q16 Q31 64 128 *)
  0x6e60b630;       (* arm_SQRDMULH_VEC Q16 Q17 Q0 16 128 *)
  0x4ed968d4;       (* arm_TRN2 Q20 Q6 Q25 64 128 *)
  0x4e649e3c;       (* arm_MUL_VEC Q28 Q17 Q4 16 128 *)
  0x4eca6823;       (* arm_TRN2 Q3 Q1 Q10 64 128 *)
  0x4ed928cd;       (* arm_TRN1 Q13 Q6 Q25 64 128 *)
  0x3d800814;       (* arm_STR Q20 X0 (Immediate_Offset (word 32)) *)
  0x6e60b479;       (* arm_SQRDMULH_VEC Q25 Q3 Q0 16 128 *)
  0x3c84040d;       (* arm_STR Q13 X0 (Postimmediate_Offset (word 64)) *)
  0x4eca283b;       (* arm_TRN1 Q27 Q1 Q10 64 128 *)
  0x6f47421c;       (* arm_MLS_VEC Q28 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4e8b6b5a;       (* arm_TRN2 Q26 Q26 Q11 32 128 *)
  0x4e649c63;       (* arm_MUL_VEC Q3 Q3 Q4 16 128 *)
  0x4ece2b4c;       (* arm_TRN1 Q12 Q26 Q14 64 128 *)
  0x6f474323;       (* arm_MLS_VEC Q3 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7c8531;       (* arm_SUB_VEC Q17 Q9 Q28 16 128 *)
  0x3c9d000c;       (* arm_STR Q12 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4ece6b4d;       (* arm_TRN2 Q13 Q26 Q14 64 128 *)
  0x4e7c852a;       (* arm_ADD_VEC Q10 Q9 Q28 16 128 *)
  0x6e7eb638;       (* arm_SQRDMULH_VEC Q24 Q17 Q30 16 128 *)
  0x3c9f000d;       (* arm_STR Q13 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e75b54d;       (* arm_SQRDMULH_VEC Q13 Q10 Q21 16 128 *)
  0x4e659d40;       (* arm_MUL_VEC Q0 Q10 Q5 16 128 *)
  0x6e638768;       (* arm_SUB_VEC Q8 Q27 Q3 16 128 *)
  0x4e638777;       (* arm_ADD_VEC Q23 Q27 Q3 16 128 *)
  0x4e739e3d;       (* arm_MUL_VEC Q29 Q17 Q19 16 128 *)
  0x6f47431d;       (* arm_MLS_VEC Q29 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741a0;       (* arm_MLS_VEC Q0 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7d8516;       (* arm_SUB_VEC Q22 Q8 Q29 16 128 *)
  0x4e7d8503;       (* arm_ADD_VEC Q3 Q8 Q29 16 128 *)
  0x6e6086f0;       (* arm_SUB_VEC Q16 Q23 Q0 16 128 *)
  0x4e6086ea;       (* arm_ADD_VEC Q10 Q23 Q0 16 128 *)
  0x4e90295f;       (* arm_TRN1 Q31 Q10 Q16 32 128 *)
  0x4e962875;       (* arm_TRN1 Q21 Q3 Q22 32 128 *)
  0x4e966863;       (* arm_TRN2 Q3 Q3 Q22 32 128 *)
  0x4e90694d;       (* arm_TRN2 Q13 Q10 Q16 32 128 *)
  0x4ed56bfa;       (* arm_TRN2 Q26 Q31 Q21 64 128 *)
  0x4ed52bea;       (* arm_TRN1 Q10 Q31 Q21 64 128 *)
  0x4ec369b5;       (* arm_TRN2 Q21 Q13 Q3 64 128 *)
  0x4ec329ad;       (* arm_TRN1 Q13 Q13 Q3 64 128 *)
  0x3d80081a;       (* arm_STR Q26 X0 (Immediate_Offset (word 32)) *)
  0x3c84040a;       (* arm_STR Q10 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9d000d;       (* arm_STR Q13 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9f0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

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
          [(word pc,0x750); (z_12345,160); (z_67,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                ntt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x738) /\
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
            (1--900) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s900" THEN
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
       [(word pc,0x750); (z_12345,160); (z_67,768)] /\
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
