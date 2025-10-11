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
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc01015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 64)) *)
  0x3dc07005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 448)) *)
  0x3dc0441e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 272)) *)
  0x3dc05018;       (* arm_LDR Q24 X0 (Immediate_Offset (word 320)) *)
  0x3dc0200c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 128)) *)
  0x4f50d0a9;       (* arm_SQRDMULH_VEC Q9 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4080b7;       (* arm_MUL_VEC Q23 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d311;       (* arm_SQRDMULH_VEC Q17 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc0300d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 192)) *)
  0x6f474137;       (* arm_MLS_VEC Q23 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408308;       (* arm_MUL_VEC Q8 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474228;       (* arm_MLS_VEC Q8 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7785a9;       (* arm_ADD_VEC Q9 Q13 Q23 16 128 *)
  0x6e7785aa;       (* arm_SUB_VEC Q10 Q13 Q23 16 128 *)
  0x4f4083cb;       (* arm_MUL_VEC Q11 Q30 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc0600d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 384)) *)
  0x4f70d13c;       (* arm_SQRDMULH_VEC Q28 Q9 (Q0 :> LANE_H 3) 16 128 *)
  0x6e6886bd;       (* arm_SUB_VEC Q29 Q21 Q8 16 128 *)
  0x4f60813a;       (* arm_MUL_VEC Q26 Q9 (Q0 :> LANE_H 2) 16 128 *)
  0x4e6886a8;       (* arm_ADD_VEC Q8 Q21 Q8 16 128 *)
  0x4f4081a2;       (* arm_MUL_VEC Q2 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47439a;       (* arm_MLS_VEC Q26 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40895c;       (* arm_MUL_VEC Q28 Q10 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50d957;       (* arm_SQRDMULH_VEC Q23 Q10 (Q0 :> LANE_H 5) 16 128 *)
  0x4e7a8516;       (* arm_ADD_VEC Q22 Q8 Q26 16 128 *)
  0x4f50d1aa;       (* arm_SQRDMULH_VEC Q10 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x4f70dad5;       (* arm_SQRDMULH_VEC Q21 Q22 (Q0 :> LANE_H 7) 16 128 *)
  0x3dc0400d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 256)) *)
  0x4f608ad0;       (* arm_MUL_VEC Q16 Q22 (Q0 :> LANE_H 6) 16 128 *)
  0x6f4742fc;       (* arm_MLS_VEC Q28 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474142;       (* arm_MLS_VEC Q2 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d1b7;       (* arm_SQRDMULH_VEC Q23 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x6e7c87aa;       (* arm_SUB_VEC Q10 Q29 Q28 16 128 *)
  0x4e7c87b1;       (* arm_ADD_VEC Q17 Q29 Q28 16 128 *)
  0x6f4742b0;       (* arm_MLS_VEC Q16 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6e628592;       (* arm_SUB_VEC Q18 Q12 Q2 16 128 *)
  0x3dc0001d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 0)) *)
  0x4f71d22e;       (* arm_SQRDMULH_VEC Q14 Q17 (Q1 :> LANE_H 3) 16 128 *)
  0x4e628596;       (* arm_ADD_VEC Q22 Q12 Q2 16 128 *)
  0x4f50da49;       (* arm_SQRDMULH_VEC Q9 Q18 (Q0 :> LANE_H 5) 16 128 *)
  0x4f4081b5;       (* arm_MUL_VEC Q21 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc0540d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 336)) *)
  0x4f408a45;       (* arm_MUL_VEC Q5 Q18 (Q0 :> LANE_H 4) 16 128 *)
  0x6f474125;       (* arm_MLS_VEC Q5 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4081b2;       (* arm_MUL_VEC Q18 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4742f5;       (* arm_MLS_VEC Q21 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d1a2;       (* arm_SQRDMULH_VEC Q2 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x4f61822d;       (* arm_MUL_VEC Q13 Q17 (Q1 :> LANE_H 2) 16 128 *)
  0x6e7587a4;       (* arm_SUB_VEC Q4 Q29 Q21 16 128 *)
  0x6f4741cd;       (* arm_MLS_VEC Q13 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7587b9;       (* arm_ADD_VEC Q25 Q29 Q21 16 128 *)
  0x4e658486;       (* arm_ADD_VEC Q6 Q4 Q5 16 128 *)
  0x4f70d2cf;       (* arm_SQRDMULH_VEC Q15 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x6e658495;       (* arm_SUB_VEC Q21 Q4 Q5 16 128 *)
  0x6e7a8505;       (* arm_SUB_VEC Q5 Q8 Q26 16 128 *)
  0x4f6082d7;       (* arm_MUL_VEC Q23 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x4e6d84dc;       (* arm_ADD_VEC Q28 Q6 Q13 16 128 *)
  0x6e6d84cd;       (* arm_SUB_VEC Q13 Q6 Q13 16 128 *)
  0x4f4180a4;       (* arm_MUL_VEC Q4 Q5 (Q1 :> LANE_H 0) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x6f4741f7;       (* arm_MLS_VEC Q23 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc06406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 400)) *)
  0x3dc0240f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 144)) *)
  0x3dc00413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 16)) *)
  0x4f418956;       (* arm_MUL_VEC Q22 Q10 (Q1 :> LANE_H 4) 16 128 *)
  0x3dc01418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 80)) *)
  0x3d80500d;       (* arm_STR Q13 X0 (Immediate_Offset (word 320)) *)
  0x4f50d0cd;       (* arm_SQRDMULH_VEC Q13 Q6 (Q0 :> LANE_H 1) 16 128 *)
  0x6e778734;       (* arm_SUB_VEC Q20 Q25 Q23 16 128 *)
  0x4f50d3c3;       (* arm_SQRDMULH_VEC Q3 Q30 (Q0 :> LANE_H 1) 16 128 *)
  0x3d80401c;       (* arm_STR Q28 X0 (Immediate_Offset (word 256)) *)
  0x3dc0481e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 288)) *)
  0x4f4080c8;       (* arm_MUL_VEC Q8 Q6 (Q0 :> LANE_H 0) 16 128 *)
  0x4f51d95b;       (* arm_SQRDMULH_VEC Q27 Q10 (Q1 :> LANE_H 5) 16 128 *)
  0x6f47406b;       (* arm_MLS_VEC Q11 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474052;       (* arm_MLS_VEC Q18 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0581f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 352)) *)
  0x4f51d0aa;       (* arm_SQRDMULH_VEC Q10 Q5 (Q1 :> LANE_H 1) 16 128 *)
  0x6f4741a8;       (* arm_MLS_VEC Q8 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0740d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 464)) *)
  0x6e72870e;       (* arm_SUB_VEC Q14 Q24 Q18 16 128 *)
  0x4e728709;       (* arm_ADD_VEC Q9 Q24 Q18 16 128 *)
  0x4f50d3e2;       (* arm_SQRDMULH_VEC Q2 Q31 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474144;       (* arm_MLS_VEC Q4 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e77872a;       (* arm_ADD_VEC Q10 Q25 Q23 16 128 *)
  0x6e6b8678;       (* arm_SUB_VEC Q24 Q19 Q11 16 128 *)
  0x4e6b8679;       (* arm_ADD_VEC Q25 Q19 Q11 16 128 *)
  0x4f50d1bc;       (* arm_SQRDMULH_VEC Q28 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4083cb;       (* arm_MUL_VEC Q11 Q30 (Q0 :> LANE_H 0) 16 128 *)
  0x4f4081b1;       (* arm_MUL_VEC Q17 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6e70854d;       (* arm_SUB_VEC Q13 Q10 Q16 16 128 *)
  0x6e6885e6;       (* arm_SUB_VEC Q6 Q15 Q8 16 128 *)
  0x6f474391;       (* arm_MLS_VEC Q17 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80100d;       (* arm_STR Q13 X0 (Immediate_Offset (word 64)) *)
  0x6f474376;       (* arm_MLS_VEC Q22 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0340d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 208)) *)
  0x4e64869a;       (* arm_ADD_VEC Q26 Q20 Q4 16 128 *)
  0x4f4083f2;       (* arm_MUL_VEC Q18 Q31 (Q0 :> LANE_H 0) 16 128 *)
  0x4e70855b;       (* arm_ADD_VEC Q27 Q10 Q16 16 128 *)
  0x3d80201a;       (* arm_STR Q26 X0 (Immediate_Offset (word 128)) *)
  0x4f50d8df;       (* arm_SQRDMULH_VEC Q31 Q6 (Q0 :> LANE_H 5) 16 128 *)
  0x4e7686a3;       (* arm_ADD_VEC Q3 Q21 Q22 16 128 *)
  0x3c81041b;       (* arm_STR Q27 X0 (Postimmediate_Offset (word 16)) *)
  0x4f4088da;       (* arm_MUL_VEC Q26 Q6 (Q0 :> LANE_H 4) 16 128 *)
  0x4e7185a6;       (* arm_ADD_VEC Q6 Q13 Q17 16 128 *)
  0x6e7185a5;       (* arm_SUB_VEC Q5 Q13 Q17 16 128 *)
  0x3d805c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 368)) *)
  0x6e7686b1;       (* arm_SUB_VEC Q17 Q21 Q22 16 128 *)
  0x4f70d0ca;       (* arm_SQRDMULH_VEC Q10 Q6 (Q0 :> LANE_H 3) 16 128 *)
  0x6e64868d;       (* arm_SUB_VEC Q13 Q20 Q4 16 128 *)
  0x4e6885f4;       (* arm_ADD_VEC Q20 Q15 Q8 16 128 *)
  0x4f50d8ac;       (* arm_SQRDMULH_VEC Q12 Q5 (Q0 :> LANE_H 5) 16 128 *)
  0x3d802c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 176)) *)
  0x4f6080c8;       (* arm_MUL_VEC Q8 Q6 (Q0 :> LANE_H 2) 16 128 *)
  0x3d806c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 432)) *)
  0x6f474148;       (* arm_MLS_VEC Q8 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4088bd;       (* arm_MUL_VEC Q29 Q5 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47419d;       (* arm_MLS_VEC Q29 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x6e688525;       (* arm_SUB_VEC Q5 Q9 Q8 16 128 *)
  0x4e688523;       (* arm_ADD_VEC Q3 Q9 Q8 16 128 *)
  0x4f70d28f;       (* arm_SQRDMULH_VEC Q15 Q20 (Q0 :> LANE_H 3) 16 128 *)
  0x4f4180a4;       (* arm_MUL_VEC Q4 Q5 (Q1 :> LANE_H 0) 16 128 *)
  0x4e7d85c6;       (* arm_ADD_VEC Q6 Q14 Q29 16 128 *)
  0x4f70d869;       (* arm_SQRDMULH_VEC Q9 Q3 (Q0 :> LANE_H 7) 16 128 *)
  0x4f71d0cc;       (* arm_SQRDMULH_VEC Q12 Q6 (Q1 :> LANE_H 3) 16 128 *)
  0x6e7d85ca;       (* arm_SUB_VEC Q10 Q14 Q29 16 128 *)
  0x4f6180d7;       (* arm_MUL_VEC Q23 Q6 (Q1 :> LANE_H 2) 16 128 *)
  0x6f4743fa;       (* arm_MLS_VEC Q26 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474197;       (* arm_MLS_VEC Q23 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f608870;       (* arm_MUL_VEC Q16 Q3 (Q0 :> LANE_H 6) 16 128 *)
  0x4e7a870d;       (* arm_ADD_VEC Q13 Q24 Q26 16 128 *)
  0x6e7a8715;       (* arm_SUB_VEC Q21 Q24 Q26 16 128 *)
  0x6f474130;       (* arm_MLS_VEC Q16 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7785bc;       (* arm_ADD_VEC Q28 Q13 Q23 16 128 *)
  0x6e7785ad;       (* arm_SUB_VEC Q13 Q13 Q23 16 128 *)
  0x4f608297;       (* arm_MUL_VEC Q23 Q20 (Q0 :> LANE_H 2) 16 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4f51d0a3;       (* arm_SQRDMULH_VEC Q3 Q5 (Q1 :> LANE_H 1) 16 128 *)
  0x6f4741f7;       (* arm_MLS_VEC Q23 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc06405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 400)) *)
  0x4f41895d;       (* arm_MUL_VEC Q29 Q10 (Q1 :> LANE_H 4) 16 128 *)
  0x6f474064;       (* arm_MLS_VEC Q4 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6e778733;       (* arm_SUB_VEC Q19 Q25 Q23 16 128 *)
  0x4f50d0bf;       (* arm_SQRDMULH_VEC Q31 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d3c6;       (* arm_SQRDMULH_VEC Q6 Q30 (Q0 :> LANE_H 1) 16 128 *)
  0x6e648663;       (* arm_SUB_VEC Q3 Q19 Q4 16 128 *)
  0x4f4080a5;       (* arm_MUL_VEC Q5 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x3d803003;       (* arm_STR Q3 X0 (Immediate_Offset (word 192)) *)
  0x4f51d94c;       (* arm_SQRDMULH_VEC Q12 Q10 (Q1 :> LANE_H 5) 16 128 *)
  0x6f474052;       (* arm_MLS_VEC Q18 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc07403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 464)) *)
  0x6f4743e5;       (* arm_MLS_VEC Q5 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d06a;       (* arm_SQRDMULH_VEC Q10 Q3 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4740cb;       (* arm_MLS_VEC Q11 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0241f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 144)) *)
  0x4f40807e;       (* arm_MUL_VEC Q30 Q3 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47415e;       (* arm_MLS_VEC Q30 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6587ea;       (* arm_SUB_VEC Q10 Q31 Q5 16 128 *)
  0x6f47419d;       (* arm_MLS_VEC Q29 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc03406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 208)) *)
  0x4f50d94f;       (* arm_SQRDMULH_VEC Q15 Q10 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408951;       (* arm_MUL_VEC Q17 Q10 (Q0 :> LANE_H 4) 16 128 *)
  0x4e7e84ca;       (* arm_ADD_VEC Q10 Q6 Q30 16 128 *)
  0x6e7e84c6;       (* arm_SUB_VEC Q6 Q6 Q30 16 128 *)
  0x4f70d14c;       (* arm_SQRDMULH_VEC Q12 Q10 (Q0 :> LANE_H 3) 16 128 *)
  0x6e7d86bb;       (* arm_SUB_VEC Q27 Q21 Q29 16 128 *)
  0x4f50d8c3;       (* arm_SQRDMULH_VEC Q3 Q6 (Q0 :> LANE_H 5) 16 128 *)
  0x4f60814a;       (* arm_MUL_VEC Q10 Q10 (Q0 :> LANE_H 2) 16 128 *)
  0x3dc01414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 80)) *)
  0x6f47418a;       (* arm_MLS_VEC Q10 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4088c2;       (* arm_MUL_VEC Q2 Q6 (Q0 :> LANE_H 4) 16 128 *)
  0x4e728686;       (* arm_ADD_VEC Q6 Q20 Q18 16 128 *)
  0x4e6587e5;       (* arm_ADD_VEC Q5 Q31 Q5 16 128 *)
  0x6f474062;       (* arm_MLS_VEC Q2 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6a84df;       (* arm_SUB_VEC Q31 Q6 Q10 16 128 *)
  0x4f70d0ac;       (* arm_SQRDMULH_VEC Q12 Q5 (Q0 :> LANE_H 3) 16 128 *)
  0x6e728696;       (* arm_SUB_VEC Q22 Q20 Q18 16 128 *)
  0x4e6a84c6;       (* arm_ADD_VEC Q6 Q6 Q10 16 128 *)
  0x4f4183f4;       (* arm_MUL_VEC Q20 Q31 (Q1 :> LANE_H 0) 16 128 *)
  0x4e6286de;       (* arm_ADD_VEC Q30 Q22 Q2 16 128 *)
  0x4f70d8c3;       (* arm_SQRDMULH_VEC Q3 Q6 (Q0 :> LANE_H 7) 16 128 *)
  0x4f71d3ca;       (* arm_SQRDMULH_VEC Q10 Q30 (Q1 :> LANE_H 3) 16 128 *)
  0x4f6183c9;       (* arm_MUL_VEC Q9 Q30 (Q1 :> LANE_H 2) 16 128 *)
  0x3dc0041e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 16)) *)
  0x6f4741f1;       (* arm_MLS_VEC Q17 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474149;       (* arm_MLS_VEC Q9 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6088cf;       (* arm_MUL_VEC Q15 Q6 (Q0 :> LANE_H 6) 16 128 *)
  0x4e6b87d8;       (* arm_ADD_VEC Q24 Q30 Q11 16 128 *)
  0x6e6286ca;       (* arm_SUB_VEC Q10 Q22 Q2 16 128 *)
  0x6f47406f;       (* arm_MLS_VEC Q15 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4e648666;       (* arm_ADD_VEC Q6 Q19 Q4 16 128 *)
  0x4e778736;       (* arm_ADD_VEC Q22 Q25 Q23 16 128 *)
  0x4f51d943;       (* arm_SQRDMULH_VEC Q3 Q10 (Q1 :> LANE_H 5) 16 128 *)
  0x3d80500d;       (* arm_STR Q13 X0 (Immediate_Offset (word 320)) *)
  0x6e6b87d3;       (* arm_SUB_VEC Q19 Q30 Q11 16 128 *)
  0x4e7086d9;       (* arm_ADD_VEC Q25 Q22 Q16 16 128 *)
  0x4f6080a5;       (* arm_MUL_VEC Q5 Q5 (Q0 :> LANE_H 2) 16 128 *)
  0x6e7086cd;       (* arm_SUB_VEC Q13 Q22 Q16 16 128 *)
  0x3d80401c;       (* arm_STR Q28 X0 (Immediate_Offset (word 256)) *)
  0x6f474185;       (* arm_MLS_VEC Q5 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80100d;       (* arm_STR Q13 X0 (Immediate_Offset (word 64)) *)
  0x3d802006;       (* arm_STR Q6 X0 (Immediate_Offset (word 128)) *)
  0x4e7d86b5;       (* arm_ADD_VEC Q21 Q21 Q29 16 128 *)
  0x4f51d3ed;       (* arm_SQRDMULH_VEC Q13 Q31 (Q1 :> LANE_H 1) 16 128 *)
  0x3c810419;       (* arm_STR Q25 X0 (Postimmediate_Offset (word 16)) *)
  0x4e71866c;       (* arm_ADD_VEC Q12 Q19 Q17 16 128 *)
  0x6e71867f;       (* arm_SUB_VEC Q31 Q19 Q17 16 128 *)
  0x4f41895e;       (* arm_MUL_VEC Q30 Q10 (Q1 :> LANE_H 4) 16 128 *)
  0x3d805c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 368)) *)
  0x4e658715;       (* arm_ADD_VEC Q21 Q24 Q5 16 128 *)
  0x4e698586;       (* arm_ADD_VEC Q6 Q12 Q9 16 128 *)
  0x6f47407e;       (* arm_MLS_VEC Q30 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x3d806c1b;       (* arm_STR Q27 X0 (Immediate_Offset (word 432)) *)
  0x6e6f86aa;       (* arm_SUB_VEC Q10 Q21 Q15 16 128 *)
  0x6e69858c;       (* arm_SUB_VEC Q12 Q12 Q9 16 128 *)
  0x6f4741b4;       (* arm_MLS_VEC Q20 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804006;       (* arm_STR Q6 X0 (Immediate_Offset (word 256)) *)
  0x3d80100a;       (* arm_STR Q10 X0 (Immediate_Offset (word 64)) *)
  0x6e65870d;       (* arm_SUB_VEC Q13 Q24 Q5 16 128 *)
  0x4e6f86a3;       (* arm_ADD_VEC Q3 Q21 Q15 16 128 *)
  0x3d80500c;       (* arm_STR Q12 X0 (Immediate_Offset (word 320)) *)
  0x6e7e87ea;       (* arm_SUB_VEC Q10 Q31 Q30 16 128 *)
  0x4e7e87f5;       (* arm_ADD_VEC Q21 Q31 Q30 16 128 *)
  0x3c810403;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 16)) *)
  0x4e7485ac;       (* arm_ADD_VEC Q12 Q13 Q20 16 128 *)
  0x6e7485ad;       (* arm_SUB_VEC Q13 Q13 Q20 16 128 *)
  0x3d805c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 368)) *)
  0x3d806c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 432)) *)
  0x3d801c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 112)) *)
  0x3d802c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 176)) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc00802;       (* arm_LDR Q2 X0 (Immediate_Offset (word 32)) *)
  0x3cc1042d;       (* arm_LDR Q13 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc00c1e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 48)) *)
  0x3dc01059;       (* arm_LDR Q25 X2 (Immediate_Offset (word 64)) *)
  0x3dc00005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 0)) *)
  0x3dc01812;       (* arm_LDR Q18 X0 (Immediate_Offset (word 96)) *)
  0x3dc01c0c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 112)) *)
  0x4f5dd051;       (* arm_SQRDMULH_VEC Q17 Q2 (Q13 :> LANE_H 1) 16 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc00417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 16)) *)
  0x4f5dd3d5;       (* arm_SQRDMULH_VEC Q21 Q30 (Q13 :> LANE_H 1) 16 128 *)
  0x3dc00858;       (* arm_LDR Q24 X2 (Immediate_Offset (word 32)) *)
  0x3cc60449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 96)) *)
  0x4f4d83ca;       (* arm_MUL_VEC Q10 Q30 (Q13 :> LANE_H 0) 16 128 *)
  0x4f4d804b;       (* arm_MUL_VEC Q11 Q2 (Q13 :> LANE_H 0) 16 128 *)
  0x6f4742aa;       (* arm_MLS_VEC Q10 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4f54d19d;       (* arm_SQRDMULH_VEC Q29 Q12 (Q4 :> LANE_H 1) 16 128 *)
  0x4f448181;       (* arm_MUL_VEC Q1 Q12 (Q4 :> LANE_H 0) 16 128 *)
  0x4e6a86f5;       (* arm_ADD_VEC Q21 Q23 Q10 16 128 *)
  0x6e6a86ea;       (* arm_SUB_VEC Q10 Q23 Q10 16 128 *)
  0x4f448248;       (* arm_MUL_VEC Q8 Q18 (Q4 :> LANE_H 0) 16 128 *)
  0x4f7dd2b7;       (* arm_SQRDMULH_VEC Q23 Q21 (Q13 :> LANE_H 3) 16 128 *)
  0x4f6d82a2;       (* arm_MUL_VEC Q2 Q21 (Q13 :> LANE_H 2) 16 128 *)
  0x6f4743a1;       (* arm_MLS_VEC Q1 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742e2;       (* arm_MLS_VEC Q2 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdb004f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4f5dd940;       (* arm_SQRDMULH_VEC Q0 Q10 (Q13 :> LANE_H 5) 16 128 *)
  0x6f47422b;       (* arm_MLS_VEC Q11 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0141d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 80)) *)
  0x4f4d8957;       (* arm_MUL_VEC Q23 Q10 (Q13 :> LANE_H 4) 16 128 *)
  0x6f474017;       (* arm_MLS_VEC Q23 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6187b0;       (* arm_SUB_VEC Q16 Q29 Q1 16 128 *)
  0x4e6b84a3;       (* arm_ADD_VEC Q3 Q5 Q11 16 128 *)
  0x6e6b84bf;       (* arm_SUB_VEC Q31 Q5 Q11 16 128 *)
  0x4f54da16;       (* arm_SQRDMULH_VEC Q22 Q16 (Q4 :> LANE_H 5) 16 128 *)
  0x4e62847e;       (* arm_ADD_VEC Q30 Q3 Q2 16 128 *)
  0x6e628460;       (* arm_SUB_VEC Q0 Q3 Q2 16 128 *)
  0x4f54d25c;       (* arm_SQRDMULH_VEC Q28 Q18 (Q4 :> LANE_H 1) 16 128 *)
  0x4e7787f5;       (* arm_ADD_VEC Q21 Q31 Q23 16 128 *)
  0x6e7787f3;       (* arm_SUB_VEC Q19 Q31 Q23 16 128 *)
  0x4f448a1a;       (* arm_MUL_VEC Q26 Q16 (Q4 :> LANE_H 4) 16 128 *)
  0x4e806bc3;       (* arm_TRN2 Q3 Q30 Q0 32 128 *)
  0x3cdf0057;       (* arm_LDR Q23 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e936ab2;       (* arm_TRN2 Q18 Q21 Q19 32 128 *)
  0x6f4742da;       (* arm_MLS_VEC Q26 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e802bcd;       (* arm_TRN1 Q13 Q30 Q0 32 128 *)
  0x6f474388;       (* arm_MLS_VEC Q8 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed2687f;       (* arm_TRN2 Q31 Q3 Q18 64 128 *)
  0x4e932aab;       (* arm_TRN1 Q11 Q21 Q19 32 128 *)
  0x4e6187bb;       (* arm_ADD_VEC Q27 Q29 Q1 16 128 *)
  0x6e6fb7e6;       (* arm_SQRDMULH_VEC Q6 Q31 Q15 16 128 *)
  0x4ecb29a2;       (* arm_TRN1 Q2 Q13 Q11 64 128 *)
  0x4ecb69ad;       (* arm_TRN2 Q13 Q13 Q11 64 128 *)
  0x4e699fe1;       (* arm_MUL_VEC Q1 Q31 Q9 16 128 *)
  0x3dc0100b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 64)) *)
  0x6e6fb5bd;       (* arm_SQRDMULH_VEC Q29 Q13 Q15 16 128 *)
  0x6f4740c1;       (* arm_MLS_VEC Q1 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed22866;       (* arm_TRN1 Q6 Q3 Q18 64 128 *)
  0x4e699db1;       (* arm_MUL_VEC Q17 Q13 Q9 16 128 *)
  0x6e68856d;       (* arm_SUB_VEC Q13 Q11 Q8 16 128 *)
  0x4f74d36a;       (* arm_SQRDMULH_VEC Q10 Q27 (Q4 :> LANE_H 3) 16 128 *)
  0x6e7a85ac;       (* arm_SUB_VEC Q12 Q13 Q26 16 128 *)
  0x6e6184d2;       (* arm_SUB_VEC Q18 Q6 Q1 16 128 *)
  0x6f4743b1;       (* arm_MLS_VEC Q17 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6184de;       (* arm_ADD_VEC Q30 Q6 Q1 16 128 *)
  0x4e7a85a6;       (* arm_ADD_VEC Q6 Q13 Q26 16 128 *)
  0x3cdd004d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6e77b650;       (* arm_SQRDMULH_VEC Q16 Q18 Q23 16 128 *)
  0x4e8c28dc;       (* arm_TRN1 Q28 Q6 Q12 32 128 *)
  0x4e799e57;       (* arm_MUL_VEC Q23 Q18 Q25 16 128 *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0x4e718454;       (* arm_ADD_VEC Q20 Q2 Q17 16 128 *)
  0x4e789fc0;       (* arm_MUL_VEC Q0 Q30 Q24 16 128 *)
  0x6e6db7dd;       (* arm_SQRDMULH_VEC Q29 Q30 Q13 16 128 *)
  0x6e71845e;       (* arm_SUB_VEC Q30 Q2 Q17 16 128 *)
  0x6f474217;       (* arm_MLS_VEC Q23 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000884;       (* arm_SUB X4 X4 (rvalue (word 2)) *)
  0x3dc01453;       (* arm_LDR Q19 X2 (Immediate_Offset (word 80)) *)
  0x6e7787df;       (* arm_SUB_VEC Q31 Q30 Q23 16 128 *)
  0x6f4743a0;       (* arm_MLS_VEC Q0 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4e688570;       (* arm_ADD_VEC Q16 Q11 Q8 16 128 *)
  0x3dc02812;       (* arm_LDR Q18 X0 (Immediate_Offset (word 160)) *)
  0x4e8c68ce;       (* arm_TRN2 Q14 Q6 Q12 32 128 *)
  0x4f64837a;       (* arm_MUL_VEC Q26 Q27 (Q4 :> LANE_H 2) 16 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc01058;       (* arm_LDR Q24 X2 (Immediate_Offset (word 64)) *)
  0x3dc02c15;       (* arm_LDR Q21 X0 (Immediate_Offset (word 176)) *)
  0x6f47415a;       (* arm_MLS_VEC Q26 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7787d7;       (* arm_ADD_VEC Q23 Q30 Q23 16 128 *)
  0x6e60868f;       (* arm_SUB_VEC Q15 Q20 Q0 16 128 *)
  0x3dc02409;       (* arm_LDR Q9 X0 (Immediate_Offset (word 144)) *)
  0x4e60868a;       (* arm_ADD_VEC Q10 Q20 Q0 16 128 *)
  0x4f448248;       (* arm_MUL_VEC Q8 Q18 (Q4 :> LANE_H 0) 16 128 *)
  0x3cc60441;       (* arm_LDR Q1 X2 (Postimmediate_Offset (word 96)) *)
  0x4e9f2afb;       (* arm_TRN1 Q27 Q23 Q31 32 128 *)
  0x4f54d24c;       (* arm_SQRDMULH_VEC Q12 Q18 (Q4 :> LANE_H 1) 16 128 *)
  0x4e8f2945;       (* arm_TRN1 Q5 Q10 Q15 32 128 *)
  0x6e7a861e;       (* arm_SUB_VEC Q30 Q16 Q26 16 128 *)
  0x4edb68ad;       (* arm_TRN2 Q13 Q5 Q27 64 128 *)
  0x4f54d2a2;       (* arm_SQRDMULH_VEC Q2 Q21 (Q4 :> LANE_H 1) 16 128 *)
  0x4e7a861d;       (* arm_ADD_VEC Q29 Q16 Q26 16 128 *)
  0x4f4482a0;       (* arm_MUL_VEC Q0 Q21 (Q4 :> LANE_H 0) 16 128 *)
  0x3d80080d;       (* arm_STR Q13 X0 (Immediate_Offset (word 32)) *)
  0x4e9e2bab;       (* arm_TRN1 Q11 Q29 Q30 32 128 *)
  0x6f474188;       (* arm_MLS_VEC Q8 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9e6bba;       (* arm_TRN2 Q26 Q29 Q30 32 128 *)
  0x4edc6966;       (* arm_TRN2 Q6 Q11 Q28 64 128 *)
  0x6f474040;       (* arm_MLS_VEC Q0 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4ece6b50;       (* arm_TRN2 Q16 Q26 Q14 64 128 *)
  0x4ece2b5a;       (* arm_TRN1 Q26 Q26 Q14 64 128 *)
  0x4edb28b4;       (* arm_TRN1 Q20 Q5 Q27 64 128 *)
  0x6e79b4dd;       (* arm_SQRDMULH_VEC Q29 Q6 Q25 16 128 *)
  0x4e8f694f;       (* arm_TRN2 Q15 Q10 Q15 32 128 *)
  0x6e79b60d;       (* arm_SQRDMULH_VEC Q13 Q16 Q25 16 128 *)
  0x3c840414;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 64)) *)
  0x6e60853e;       (* arm_SUB_VEC Q30 Q9 Q0 16 128 *)
  0x4e60853b;       (* arm_ADD_VEC Q27 Q9 Q0 16 128 *)
  0x4e619cd1;       (* arm_MUL_VEC Q17 Q6 Q1 16 128 *)
  0x4f54dbd6;       (* arm_SQRDMULH_VEC Q22 Q30 (Q4 :> LANE_H 5) 16 128 *)
  0x4e619e12;       (* arm_MUL_VEC Q18 Q16 Q1 16 128 *)
  0x6f4741b2;       (* arm_MLS_VEC Q18 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f448bc2;       (* arm_MUL_VEC Q2 Q30 (Q4 :> LANE_H 4) 16 128 *)
  0x6f4742c2;       (* arm_MLS_VEC Q2 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e9f6af6;       (* arm_TRN2 Q22 Q23 Q31 32 128 *)
  0x6e728743;       (* arm_SUB_VEC Q3 Q26 Q18 16 128 *)
  0x3cdd0059;       (* arm_LDR Q25 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f4743b1;       (* arm_MLS_VEC Q17 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed669ff;       (* arm_TRN2 Q31 Q15 Q22 64 128 *)
  0x4ed629f4;       (* arm_TRN1 Q20 Q15 Q22 64 128 *)
  0x4e728750;       (* arm_ADD_VEC Q16 Q26 Q18 16 128 *)
  0x6e73b47a;       (* arm_SQRDMULH_VEC Q26 Q3 Q19 16 128 *)
  0x4edc2975;       (* arm_TRN1 Q21 Q11 Q28 64 128 *)
  0x3dc0100b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 64)) *)
  0x6e79b61d;       (* arm_SQRDMULH_VEC Q29 Q16 Q25 16 128 *)
  0x3c9d0014;       (* arm_STR Q20 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e7186b4;       (* arm_ADD_VEC Q20 Q21 Q17 16 128 *)
  0x3c9f001f;       (* arm_STR Q31 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e789c77;       (* arm_MUL_VEC Q23 Q3 Q24 16 128 *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0x6e68856d;       (* arm_SUB_VEC Q13 Q11 Q8 16 128 *)
  0x6f474357;       (* arm_MLS_VEC Q23 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdc0041;       (* arm_LDR Q1 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6e6285ac;       (* arm_SUB_VEC Q12 Q13 Q2 16 128 *)
  0x4e6285a6;       (* arm_ADD_VEC Q6 Q13 Q2 16 128 *)
  0x4f74d36a;       (* arm_SQRDMULH_VEC Q10 Q27 (Q4 :> LANE_H 3) 16 128 *)
  0x6e7186be;       (* arm_SUB_VEC Q30 Q21 Q17 16 128 *)
  0x4e619e00;       (* arm_MUL_VEC Q0 Q16 Q1 16 128 *)
  0x4e8c28dc;       (* arm_TRN1 Q28 Q6 Q12 32 128 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fff704;       (* arm_CBNZ X4 (word 2096864) *)
  0x4e688576;       (* arm_ADD_VEC Q22 Q11 Q8 16 128 *)
  0x4f64837b;       (* arm_MUL_VEC Q27 Q27 (Q4 :> LANE_H 2) 16 128 *)
  0x4e8c68d1;       (* arm_TRN2 Q17 Q6 Q12 32 128 *)
  0x3cc6044f;       (* arm_LDR Q15 X2 (Postimmediate_Offset (word 96)) *)
  0x6f47415b;       (* arm_MLS_VEC Q27 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7787c4;       (* arm_ADD_VEC Q4 Q30 Q23 16 128 *)
  0x6e7787d2;       (* arm_SUB_VEC Q18 Q30 Q23 16 128 *)
  0x3cdd0046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f4743a0;       (* arm_MLS_VEC Q0 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdc004c;       (* arm_LDR Q12 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x3cde0058;       (* arm_LDR Q24 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdf0042;       (* arm_LDR Q2 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e922889;       (* arm_TRN1 Q9 Q4 Q18 32 128 *)
  0x4e7b86ca;       (* arm_ADD_VEC Q10 Q22 Q27 16 128 *)
  0x6e7b86cd;       (* arm_SUB_VEC Q13 Q22 Q27 16 128 *)
  0x6e608681;       (* arm_SUB_VEC Q1 Q20 Q0 16 128 *)
  0x4e8d6955;       (* arm_TRN2 Q21 Q10 Q13 32 128 *)
  0x4e60869b;       (* arm_ADD_VEC Q27 Q20 Q0 16 128 *)
  0x4ed16aa3;       (* arm_TRN2 Q3 Q21 Q17 64 128 *)
  0x4e8d294d;       (* arm_TRN1 Q13 Q10 Q13 32 128 *)
  0x4e812b7f;       (* arm_TRN1 Q31 Q27 Q1 32 128 *)
  0x6e79b46a;       (* arm_SQRDMULH_VEC Q10 Q3 Q25 16 128 *)
  0x4edc69a5;       (* arm_TRN2 Q5 Q13 Q28 64 128 *)
  0x4edc29ad;       (* arm_TRN1 Q13 Q13 Q28 64 128 *)
  0x4ed12ab5;       (* arm_TRN1 Q21 Q21 Q17 64 128 *)
  0x6e79b4b1;       (* arm_SQRDMULH_VEC Q17 Q5 Q25 16 128 *)
  0x4ec96bfe;       (* arm_TRN2 Q30 Q31 Q9 64 128 *)
  0x4e6f9c79;       (* arm_MUL_VEC Q25 Q3 Q15 16 128 *)
  0x3d80081e;       (* arm_STR Q30 X0 (Immediate_Offset (word 32)) *)
  0x4e92689e;       (* arm_TRN2 Q30 Q4 Q18 32 128 *)
  0x6f474159;       (* arm_MLS_VEC Q25 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e816b63;       (* arm_TRN2 Q3 Q27 Q1 32 128 *)
  0x4e6f9cb4;       (* arm_MUL_VEC Q20 Q5 Q15 16 128 *)
  0x4ede686a;       (* arm_TRN2 Q10 Q3 Q30 64 128 *)
  0x6f474234;       (* arm_MLS_VEC Q20 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 48)) *)
  0x6e7986b2;       (* arm_SUB_VEC Q18 Q21 Q25 16 128 *)
  0x4e7986aa;       (* arm_ADD_VEC Q10 Q21 Q25 16 128 *)
  0x4ede2863;       (* arm_TRN1 Q3 Q3 Q30 64 128 *)
  0x6e62b65e;       (* arm_SQRDMULH_VEC Q30 Q18 Q2 16 128 *)
  0x4e6c9d4c;       (* arm_MUL_VEC Q12 Q10 Q12 16 128 *)
  0x6e66b546;       (* arm_SQRDMULH_VEC Q6 Q10 Q6 16 128 *)
  0x3d800403;       (* arm_STR Q3 X0 (Immediate_Offset (word 16)) *)
  0x4e7485b5;       (* arm_ADD_VEC Q21 Q13 Q20 16 128 *)
  0x4e789e4a;       (* arm_MUL_VEC Q10 Q18 Q24 16 128 *)
  0x6e7485ad;       (* arm_SUB_VEC Q13 Q13 Q20 16 128 *)
  0x6f4743ca;       (* arm_MLS_VEC Q10 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4740cc;       (* arm_MLS_VEC Q12 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec92bfe;       (* arm_TRN1 Q30 Q31 Q9 64 128 *)
  0x6e6a85a3;       (* arm_SUB_VEC Q3 Q13 Q10 16 128 *)
  0x4e6a85a6;       (* arm_ADD_VEC Q6 Q13 Q10 16 128 *)
  0x4e6c86aa;       (* arm_ADD_VEC Q10 Q21 Q12 16 128 *)
  0x6e6c86b5;       (* arm_SUB_VEC Q21 Q21 Q12 16 128 *)
  0x4e8368cd;       (* arm_TRN2 Q13 Q6 Q3 32 128 *)
  0x4e95294c;       (* arm_TRN1 Q12 Q10 Q21 32 128 *)
  0x4e956955;       (* arm_TRN2 Q21 Q10 Q21 32 128 *)
  0x4e8328c3;       (* arm_TRN1 Q3 Q6 Q3 32 128 *)
  0x3c84041e;       (* arm_STR Q30 X0 (Postimmediate_Offset (word 64)) *)
  0x4ecd6aaa;       (* arm_TRN2 Q10 Q21 Q13 64 128 *)
  0x4ecd2aad;       (* arm_TRN1 Q13 Q21 Q13 64 128 *)
  0x4ec36995;       (* arm_TRN2 Q21 Q12 Q3 64 128 *)
  0x4ec32983;       (* arm_TRN1 Q3 Q12 Q3 64 128 *)
  0x3d800c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 48)) *)
  0x3d80040d;       (* arm_STR Q13 X0 (Immediate_Offset (word 16)) *)
  0x3c840403;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9e0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_NTT_EXEC = ARM_MK_EXEC_RULE mlkem_ntt_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)


let LENGTH_MLKEM_NTT_MC =
  REWRITE_CONV[mlkem_ntt_mc] `LENGTH mlkem_ntt_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_NTT_PREAMBLE_LENGTH = new_definition
  `MLKEM_NTT_PREAMBLE_LENGTH = 20`;;

let MLKEM_NTT_POSTAMBLE_LENGTH = new_definition
  `MLKEM_NTT_POSTAMBLE_LENGTH = 24`;;

let MLKEM_NTT_CORE_START = new_definition
  `MLKEM_NTT_CORE_START = MLKEM_NTT_PREAMBLE_LENGTH`;;

let MLKEM_NTT_CORE_END = new_definition
  `MLKEM_NTT_CORE_END = LENGTH mlkem_ntt_mc - MLKEM_NTT_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_NTT_MC;
              MLKEM_NTT_CORE_START; MLKEM_NTT_CORE_END;
              MLKEM_NTT_PREAMBLE_LENGTH; MLKEM_NTT_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

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
          [(word pc,LENGTH mlkem_ntt_mc); (z_12345,160); (z_67,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                read PC s = word (pc + MLKEM_NTT_CORE_START) /\
                C_ARGUMENTS [a; z_12345; z_67] s /\
                ntt_constants z_12345 z_67 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + MLKEM_NTT_CORE_END) /\
                ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &23594))
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

  MAP_UNTIL_TARGET_PC (fun n -> ARM_STEPS_TAC MLKEM_NTT_EXEC [n] THEN
             (SIMD_SIMPLIFY_TAC [barmul])) 1 THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s904" THEN
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
       [(word pc,LENGTH mlkem_ntt_mc); (z_12345,160); (z_67,768)] /\
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
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  let TWEAK_CONV =
    REWRITE_CONV[ntt_constants] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[fst MLKEM_NTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_NTT_EXEC
   (REWRITE_RULE[fst MLKEM_NTT_EXEC] (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_NTT_CORRECT)))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
