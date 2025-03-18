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
  0x3dc00015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 0)) *)
  0x3dc0101a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 64)) *)
  0x3dc0201d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 128)) *)
  0x3dc03014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 192)) *)
  0x3dc04017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 256)) *)
  0x3dc0700b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 448)) *)
  0x4f4082e2;       (* arm_MUL_VEC Q2 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc05011;       (* arm_LDR Q17 X0 (Immediate_Offset (word 320)) *)
  0x4f40816f;       (* arm_MUL_VEC Q15 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc0600d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 384)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4f50d2ee;       (* arm_SQRDMULH_VEC Q14 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d237;       (* arm_SQRDMULH_VEC Q23 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408231;       (* arm_MUL_VEC Q17 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d1bc;       (* arm_SQRDMULH_VEC Q28 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4741c2;       (* arm_MLS_VEC Q2 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4081ae;       (* arm_MUL_VEC Q14 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4742f1;       (* arm_MLS_VEC Q17 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d177;       (* arm_SQRDMULH_VEC Q23 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x6e6286ab;       (* arm_SUB_VEC Q11 Q21 Q2 16 128 *)
  0x6f47438e;       (* arm_MLS_VEC Q14 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e71875c;       (* arm_SUB_VEC Q28 Q26 Q17 16 128 *)
  0x4e718751;       (* arm_ADD_VEC Q17 Q26 Q17 16 128 *)
  0x4e6286a2;       (* arm_ADD_VEC Q2 Q21 Q2 16 128 *)
  0x6e6e87ad;       (* arm_SUB_VEC Q13 Q29 Q14 16 128 *)
  0x4e6e87ae;       (* arm_ADD_VEC Q14 Q29 Q14 16 128 *)
  0x6f4742ef;       (* arm_MLS_VEC Q15 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d9b7;       (* arm_SQRDMULH_VEC Q23 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x4f4089ad;       (* arm_MUL_VEC Q13 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x4f70d1d5;       (* arm_SQRDMULH_VEC Q21 Q14 (Q0 :> LANE_H 3) 16 128 *)
  0x6e6f869a;       (* arm_SUB_VEC Q26 Q20 Q15 16 128 *)
  0x4e6f868f;       (* arm_ADD_VEC Q15 Q20 Q15 16 128 *)
  0x6f4742ed;       (* arm_MLS_VEC Q13 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50db57;       (* arm_SQRDMULH_VEC Q23 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408b5a;       (* arm_MUL_VEC Q26 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x4f6081ce;       (* arm_MUL_VEC Q14 Q14 (Q0 :> LANE_H 2) 16 128 *)
  0x6e6d857d;       (* arm_SUB_VEC Q29 Q11 Q13 16 128 *)
  0x4e6d856b;       (* arm_ADD_VEC Q11 Q11 Q13 16 128 *)
  0x6f4742fa;       (* arm_MLS_VEC Q26 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d1f7;       (* arm_SQRDMULH_VEC Q23 Q15 (Q0 :> LANE_H 3) 16 128 *)
  0x4f6081ed;       (* arm_MUL_VEC Q13 Q15 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4742ae;       (* arm_MLS_VEC Q14 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a878f;       (* arm_SUB_VEC Q15 Q28 Q26 16 128 *)
  0x4e7a879c;       (* arm_ADD_VEC Q28 Q28 Q26 16 128 *)
  0x6f4742ed;       (* arm_MLS_VEC Q13 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6e8457;       (* arm_SUB_VEC Q23 Q2 Q14 16 128 *)
  0x4e6e844e;       (* arm_ADD_VEC Q14 Q2 Q14 16 128 *)
  0x4f71d382;       (* arm_SQRDMULH_VEC Q2 Q28 (Q1 :> LANE_H 3) 16 128 *)
  0x6e6d8635;       (* arm_SUB_VEC Q21 Q17 Q13 16 128 *)
  0x4e6d8631;       (* arm_ADD_VEC Q17 Q17 Q13 16 128 *)
  0x4f61839c;       (* arm_MUL_VEC Q28 Q28 (Q1 :> LANE_H 2) 16 128 *)
  0x4f51d2ad;       (* arm_SQRDMULH_VEC Q13 Q21 (Q1 :> LANE_H 1) 16 128 *)
  0x4f70da3a;       (* arm_SQRDMULH_VEC Q26 Q17 (Q0 :> LANE_H 7) 16 128 *)
  0x4f608a31;       (* arm_MUL_VEC Q17 Q17 (Q0 :> LANE_H 6) 16 128 *)
  0x4f4182b5;       (* arm_MUL_VEC Q21 Q21 (Q1 :> LANE_H 0) 16 128 *)
  0x6f47405c;       (* arm_MLS_VEC Q28 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d9e2;       (* arm_SQRDMULH_VEC Q2 Q15 (Q1 :> LANE_H 5) 16 128 *)
  0x6f474351;       (* arm_MLS_VEC Q17 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741b5;       (* arm_MLS_VEC Q21 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7c856d;       (* arm_SUB_VEC Q13 Q11 Q28 16 128 *)
  0x4e7c857c;       (* arm_ADD_VEC Q28 Q11 Q28 16 128 *)
  0x6e7185cb;       (* arm_SUB_VEC Q11 Q14 Q17 16 128 *)
  0x4f4189ef;       (* arm_MUL_VEC Q15 Q15 (Q1 :> LANE_H 4) 16 128 *)
  0x4e7185ce;       (* arm_ADD_VEC Q14 Q14 Q17 16 128 *)
  0x6e7586f1;       (* arm_SUB_VEC Q17 Q23 Q21 16 128 *)
  0x4e7586f7;       (* arm_ADD_VEC Q23 Q23 Q21 16 128 *)
  0x6f47404f;       (* arm_MLS_VEC Q15 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x3c81040e;       (* arm_STR Q14 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc00015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 0)) *)
  0x6e6f87ae;       (* arm_SUB_VEC Q14 Q29 Q15 16 128 *)
  0x4e6f87a2;       (* arm_ADD_VEC Q2 Q29 Q15 16 128 *)
  0x3d800c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 48)) *)
  0x3dc0101a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 64)) *)
  0x3d801c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 112)) *)
  0x3dc0201d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 128)) *)
  0x3d802c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 176)) *)
  0x3dc03014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 192)) *)
  0x3d803c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 240)) *)
  0x3dc04017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 256)) *)
  0x3d804c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 304)) *)
  0x3dc05011;       (* arm_LDR Q17 X0 (Immediate_Offset (word 320)) *)
  0x3d805c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 368)) *)
  0x4f4082e2;       (* arm_MUL_VEC Q2 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x3d806c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 432)) *)
  0x3dc0700b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 448)) *)
  0x3dc0600d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 384)) *)
  0x4f40816f;       (* arm_MUL_VEC Q15 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4f50d17b;       (* arm_SQRDMULH_VEC Q27 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4081a8;       (* arm_MUL_VEC Q8 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d1b6;       (* arm_SQRDMULH_VEC Q22 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40822b;       (* arm_MUL_VEC Q11 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47436f;       (* arm_MLS_VEC Q15 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d23c;       (* arm_SQRDMULH_VEC Q28 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4742c8;       (* arm_MLS_VEC Q8 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d2e5;       (* arm_SQRDMULH_VEC Q5 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x4e6f8690;       (* arm_ADD_VEC Q16 Q20 Q15 16 128 *)
  0x6f47438b;       (* arm_MLS_VEC Q11 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6887a6;       (* arm_SUB_VEC Q6 Q29 Q8 16 128 *)
  0x4f70d211;       (* arm_SQRDMULH_VEC Q17 Q16 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608217;       (* arm_MUL_VEC Q23 Q16 (Q0 :> LANE_H 2) 16 128 *)
  0x4f4088cd;       (* arm_MUL_VEC Q13 Q6 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50d8dc;       (* arm_SQRDMULH_VEC Q28 Q6 (Q0 :> LANE_H 5) 16 128 *)
  0x6f4740a2;       (* arm_MLS_VEC Q2 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474237;       (* arm_MLS_VEC Q23 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6b875b;       (* arm_ADD_VEC Q27 Q26 Q11 16 128 *)
  0x6f47438d;       (* arm_MLS_VEC Q13 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6286a9;       (* arm_SUB_VEC Q9 Q21 Q2 16 128 *)
  0x4e6887b2;       (* arm_ADD_VEC Q18 Q29 Q8 16 128 *)
  0x6e77876e;       (* arm_SUB_VEC Q14 Q27 Q23 16 128 *)
  0x4e6d853d;       (* arm_ADD_VEC Q29 Q9 Q13 16 128 *)
  0x6e6d853e;       (* arm_SUB_VEC Q30 Q9 Q13 16 128 *)
  0x4f4181dc;       (* arm_MUL_VEC Q28 Q14 (Q1 :> LANE_H 0) 16 128 *)
  0x4f70d249;       (* arm_SQRDMULH_VEC Q9 Q18 (Q0 :> LANE_H 3) 16 128 *)
  0x4f608256;       (* arm_MUL_VEC Q22 Q18 (Q0 :> LANE_H 2) 16 128 *)
  0x4f51d1d1;       (* arm_SQRDMULH_VEC Q17 Q14 (Q1 :> LANE_H 1) 16 128 *)
  0x6e6f868e;       (* arm_SUB_VEC Q14 Q20 Q15 16 128 *)
  0x4e6286b8;       (* arm_ADD_VEC Q24 Q21 Q2 16 128 *)
  0x6f474136;       (* arm_MLS_VEC Q22 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d9c9;       (* arm_SQRDMULH_VEC Q9 Q14 (Q0 :> LANE_H 5) 16 128 *)
  0x4f4089cd;       (* arm_MUL_VEC Q13 Q14 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47423c;       (* arm_MLS_VEC Q28 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6e768705;       (* arm_SUB_VEC Q5 Q24 Q22 16 128 *)
  0x6e6b8742;       (* arm_SUB_VEC Q2 Q26 Q11 16 128 *)
  0x6f47412d;       (* arm_MLS_VEC Q13 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7c84b1;       (* arm_SUB_VEC Q17 Q5 Q28 16 128 *)
  0x4e7c84ae;       (* arm_ADD_VEC Q14 Q5 Q28 16 128 *)
  0x4e77877c;       (* arm_ADD_VEC Q28 Q27 Q23 16 128 *)
  0x3d803011;       (* arm_STR Q17 X0 (Immediate_Offset (word 192)) *)
  0x4e6d8451;       (* arm_ADD_VEC Q17 Q2 Q13 16 128 *)
  0x3d80200e;       (* arm_STR Q14 X0 (Immediate_Offset (word 128)) *)
  0x6e6d844d;       (* arm_SUB_VEC Q13 Q2 Q13 16 128 *)
  0x4f71d23a;       (* arm_SQRDMULH_VEC Q26 Q17 (Q1 :> LANE_H 3) 16 128 *)
  0x4f61822f;       (* arm_MUL_VEC Q15 Q17 (Q1 :> LANE_H 2) 16 128 *)
  0x4e768705;       (* arm_ADD_VEC Q5 Q24 Q22 16 128 *)
  0x4f51d9b7;       (* arm_SQRDMULH_VEC Q23 Q13 (Q1 :> LANE_H 5) 16 128 *)
  0x4f4189ad;       (* arm_MUL_VEC Q13 Q13 (Q1 :> LANE_H 4) 16 128 *)
  0x6f47434f;       (* arm_MLS_VEC Q15 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70db8e;       (* arm_SQRDMULH_VEC Q14 Q28 (Q0 :> LANE_H 7) 16 128 *)
  0x4f608b91;       (* arm_MUL_VEC Q17 Q28 (Q0 :> LANE_H 6) 16 128 *)
  0x6f4742ed;       (* arm_MLS_VEC Q13 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6f87a6;       (* arm_ADD_VEC Q6 Q29 Q15 16 128 *)
  0x6e6f87bc;       (* arm_SUB_VEC Q28 Q29 Q15 16 128 *)
  0x6f4741d1;       (* arm_MLS_VEC Q17 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804006;       (* arm_STR Q6 X0 (Immediate_Offset (word 256)) *)
  0x4e6d87ce;       (* arm_ADD_VEC Q14 Q30 Q13 16 128 *)
  0x3d80501c;       (* arm_STR Q28 X0 (Immediate_Offset (word 320)) *)
  0x6e6d87d7;       (* arm_SUB_VEC Q23 Q30 Q13 16 128 *)
  0x3d80600e;       (* arm_STR Q14 X0 (Immediate_Offset (word 384)) *)
  0x4e7184a3;       (* arm_ADD_VEC Q3 Q5 Q17 16 128 *)
  0x3d807017;       (* arm_STR Q23 X0 (Immediate_Offset (word 448)) *)
  0x6e7184bc;       (* arm_SUB_VEC Q28 Q5 Q17 16 128 *)
  0x3c810403;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 16)) *)
  0x3d800c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 48)) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3cc10422;       (* arm_LDR Q2 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc00c0e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 48)) *)
  0x3dc00801;       (* arm_LDR Q1 X0 (Immediate_Offset (word 32)) *)
  0x4f4281d1;       (* arm_MUL_VEC Q17 Q14 (Q2 :> LANE_H 0) 16 128 *)
  0x4f52d1ce;       (* arm_SQRDMULH_VEC Q14 Q14 (Q2 :> LANE_H 1) 16 128 *)
  0x4f428028;       (* arm_MUL_VEC Q8 Q1 (Q2 :> LANE_H 0) 16 128 *)
  0x3dc00417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 16)) *)
  0x6f4741d1;       (* arm_MLS_VEC Q17 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f52d021;       (* arm_SQRDMULH_VEC Q1 Q1 (Q2 :> LANE_H 1) 16 128 *)
  0x3cc6045e;       (* arm_LDR Q30 X2 (Postimmediate_Offset (word 96)) *)
  0x6e7186ee;       (* arm_SUB_VEC Q14 Q23 Q17 16 128 *)
  0x4e7186ea;       (* arm_ADD_VEC Q10 Q23 Q17 16 128 *)
  0x6f474028;       (* arm_MLS_VEC Q8 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4f52d9c1;       (* arm_SQRDMULH_VEC Q1 Q14 (Q2 :> LANE_H 5) 16 128 *)
  0x4f4289ce;       (* arm_MUL_VEC Q14 Q14 (Q2 :> LANE_H 4) 16 128 *)
  0x3dc0001b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 0)) *)
  0x4f628157;       (* arm_MUL_VEC Q23 Q10 (Q2 :> LANE_H 2) 16 128 *)
  0x6f47402e;       (* arm_MLS_VEC Q14 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x6e688761;       (* arm_SUB_VEC Q1 Q27 Q8 16 128 *)
  0x3cdc005c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4e6e842c;       (* arm_ADD_VEC Q12 Q1 Q14 16 128 *)
  0x4f72d155;       (* arm_SQRDMULH_VEC Q21 Q10 (Q2 :> LANE_H 3) 16 128 *)
  0x6e6e8425;       (* arm_SUB_VEC Q5 Q1 Q14 16 128 *)
  0x3cdf004d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x3dc01c13;       (* arm_LDR Q19 X0 (Immediate_Offset (word 112)) *)
  0x3cc10421;       (* arm_LDR Q1 X1 (Postimmediate_Offset (word 16)) *)
  0x6f4742b7;       (* arm_MLS_VEC Q23 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e688766;       (* arm_ADD_VEC Q6 Q27 Q8 16 128 *)
  0x4f418264;       (* arm_MUL_VEC Q4 Q19 (Q1 :> LANE_H 0) 16 128 *)
  0x4f51d273;       (* arm_SQRDMULH_VEC Q19 Q19 (Q1 :> LANE_H 1) 16 128 *)
  0x3dc01419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 80)) *)
  0x4e85298b;       (* arm_TRN1 Q11 Q12 Q5 32 128 *)
  0x6f474264;       (* arm_MLS_VEC Q4 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7784c0;       (* arm_SUB_VEC Q0 Q6 Q23 16 128 *)
  0x3cdb0050;       (* arm_LDR Q16 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x6e648738;       (* arm_SUB_VEC Q24 Q25 Q4 16 128 *)
  0x4e7784da;       (* arm_ADD_VEC Q26 Q6 Q23 16 128 *)
  0x4e648724;       (* arm_ADD_VEC Q4 Q25 Q4 16 128 *)
  0x4f51db17;       (* arm_SQRDMULH_VEC Q23 Q24 (Q1 :> LANE_H 5) 16 128 *)
  0x4f418b14;       (* arm_MUL_VEC Q20 Q24 (Q1 :> LANE_H 4) 16 128 *)
  0x4f71d095;       (* arm_SQRDMULH_VEC Q21 Q4 (Q1 :> LANE_H 3) 16 128 *)
  0x4e802b5b;       (* arm_TRN1 Q27 Q26 Q0 32 128 *)
  0x4e856999;       (* arm_TRN2 Q25 Q12 Q5 32 128 *)
  0x6f4742f4;       (* arm_MLS_VEC Q20 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f618097;       (* arm_MUL_VEC Q23 Q4 (Q1 :> LANE_H 2) 16 128 *)
  0x3dc0181f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 96)) *)
  0x4e806b4c;       (* arm_TRN2 Q12 Q26 Q0 32 128 *)
  0x4ecb6b73;       (* arm_TRN2 Q19 Q27 Q11 64 128 *)
  0x4f4183e8;       (* arm_MUL_VEC Q8 Q31 (Q1 :> LANE_H 0) 16 128 *)
  0x4f51d3e1;       (* arm_SQRDMULH_VEC Q1 Q31 (Q1 :> LANE_H 1) 16 128 *)
  0x4ed9698a;       (* arm_TRN2 Q10 Q12 Q25 64 128 *)
  0x6e70b660;       (* arm_SQRDMULH_VEC Q0 Q19 Q16 16 128 *)
  0x6e70b552;       (* arm_SQRDMULH_VEC Q18 Q10 Q16 16 128 *)
  0x4ecb2b70;       (* arm_TRN1 Q16 Q27 Q11 64 128 *)
  0x4ed92982;       (* arm_TRN1 Q2 Q12 Q25 64 128 *)
  0x4e7e9d4c;       (* arm_MUL_VEC Q12 Q10 Q30 16 128 *)
  0x4e7e9e6a;       (* arm_MUL_VEC Q10 Q19 Q30 16 128 *)
  0x6f474028;       (* arm_MLS_VEC Q8 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdd004e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f47400a;       (* arm_MLS_VEC Q10 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47424c;       (* arm_MLS_VEC Q12 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0101b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 64)) *)
  0x4e6a8609;       (* arm_ADD_VEC Q9 Q16 Q10 16 128 *)
  0x6e6a8610;       (* arm_SUB_VEC Q16 Q16 Q10 16 128 *)
  0x6e6c8459;       (* arm_SUB_VEC Q25 Q2 Q12 16 128 *)
  0x4e6c845e;       (* arm_ADD_VEC Q30 Q2 Q12 16 128 *)
  0x6e68876a;       (* arm_SUB_VEC Q10 Q27 Q8 16 128 *)
  0x6e6db736;       (* arm_SQRDMULH_VEC Q22 Q25 Q13 16 128 *)
  0x6e6eb7cd;       (* arm_SQRDMULH_VEC Q13 Q30 Q14 16 128 *)
  0x3cde004e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e74854c;       (* arm_ADD_VEC Q12 Q10 Q20 16 128 *)
  0x4e7c9fc5;       (* arm_MUL_VEC Q5 Q30 Q28 16 128 *)
  0x4e6e9f3a;       (* arm_MUL_VEC Q26 Q25 Q14 16 128 *)
  0x3cc6045e;       (* arm_LDR Q30 X2 (Postimmediate_Offset (word 96)) *)
  0x6f4741a5;       (* arm_MLS_VEC Q5 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742da;       (* arm_MLS_VEC Q26 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdc005c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4e65852d;       (* arm_ADD_VEC Q13 Q9 Q5 16 128 *)
  0x6e658529;       (* arm_SUB_VEC Q9 Q9 Q5 16 128 *)
  0x6e7a8605;       (* arm_SUB_VEC Q5 Q16 Q26 16 128 *)
  0x4e7a8619;       (* arm_ADD_VEC Q25 Q16 Q26 16 128 *)
  0x4e8929af;       (* arm_TRN1 Q15 Q13 Q9 32 128 *)
  0x4e8969a3;       (* arm_TRN2 Q3 Q13 Q9 32 128 *)
  0x4e852b2d;       (* arm_TRN1 Q13 Q25 Q5 32 128 *)
  0x4e856b3f;       (* arm_TRN2 Q31 Q25 Q5 32 128 *)
  0x6e748545;       (* arm_SUB_VEC Q5 Q10 Q20 16 128 *)
  0x4ecd29e2;       (* arm_TRN1 Q2 Q15 Q13 64 128 *)
  0x4ecd69e9;       (* arm_TRN2 Q9 Q15 Q13 64 128 *)
  0x3c840402;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 64)) *)
  0x4edf287d;       (* arm_TRN1 Q29 Q3 Q31 64 128 *)
  0x3c9e0009;       (* arm_STR Q9 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x4edf6869;       (* arm_TRN2 Q9 Q3 Q31 64 128 *)
  0x3c9d001d;       (* arm_STR Q29 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cdf004d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9f0009;       (* arm_STR Q9 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff704;       (* arm_CBNZ X4 (word 2096864) *)
  0x6f4742b7;       (* arm_MLS_VEC Q23 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e68876e;       (* arm_ADD_VEC Q14 Q27 Q8 16 128 *)
  0x3cde0041;       (* arm_LDR Q1 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e7785d1;       (* arm_ADD_VEC Q17 Q14 Q23 16 128 *)
  0x6e7785d7;       (* arm_SUB_VEC Q23 Q14 Q23 16 128 *)
  0x4e85698b;       (* arm_TRN2 Q11 Q12 Q5 32 128 *)
  0x4e85299b;       (* arm_TRN1 Q27 Q12 Q5 32 128 *)
  0x4e976a22;       (* arm_TRN2 Q2 Q17 Q23 32 128 *)
  0x3cdb005a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4ecb684e;       (* arm_TRN2 Q14 Q2 Q11 64 128 *)
  0x4e972a2f;       (* arm_TRN1 Q15 Q17 Q23 32 128 *)
  0x4e7e9dc5;       (* arm_MUL_VEC Q5 Q14 Q30 16 128 *)
  0x6e7ab5d7;       (* arm_SQRDMULH_VEC Q23 Q14 Q26 16 128 *)
  0x4edb69f1;       (* arm_TRN2 Q17 Q15 Q27 64 128 *)
  0x4ecb284e;       (* arm_TRN1 Q14 Q2 Q11 64 128 *)
  0x4e7e9e35;       (* arm_MUL_VEC Q21 Q17 Q30 16 128 *)
  0x6f4742e5;       (* arm_MLS_VEC Q5 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7ab631;       (* arm_SQRDMULH_VEC Q17 Q17 Q26 16 128 *)
  0x3cdd0042;       (* arm_LDR Q2 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6e6585d7;       (* arm_SUB_VEC Q23 Q14 Q5 16 128 *)
  0x4e6585ce;       (* arm_ADD_VEC Q14 Q14 Q5 16 128 *)
  0x6f474235;       (* arm_MLS_VEC Q21 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4e619ee1;       (* arm_MUL_VEC Q1 Q23 Q1 16 128 *)
  0x6e6db6f1;       (* arm_SQRDMULH_VEC Q17 Q23 Q13 16 128 *)
  0x4e7c9dd7;       (* arm_MUL_VEC Q23 Q14 Q28 16 128 *)
  0x6e62b5ce;       (* arm_SQRDMULH_VEC Q14 Q14 Q2 16 128 *)
  0x4edb29fc;       (* arm_TRN1 Q28 Q15 Q27 64 128 *)
  0x6f474221;       (* arm_MLS_VEC Q1 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6e75878b;       (* arm_SUB_VEC Q11 Q28 Q21 16 128 *)
  0x6f4741d7;       (* arm_MLS_VEC Q23 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4e758791;       (* arm_ADD_VEC Q17 Q28 Q21 16 128 *)
  0x6e61856e;       (* arm_SUB_VEC Q14 Q11 Q1 16 128 *)
  0x4e618561;       (* arm_ADD_VEC Q1 Q11 Q1 16 128 *)
  0x6e77863c;       (* arm_SUB_VEC Q28 Q17 Q23 16 128 *)
  0x4e778622;       (* arm_ADD_VEC Q2 Q17 Q23 16 128 *)
  0x4e8e2837;       (* arm_TRN1 Q23 Q1 Q14 32 128 *)
  0x4e8e682e;       (* arm_TRN2 Q14 Q1 Q14 32 128 *)
  0x4e9c6851;       (* arm_TRN2 Q17 Q2 Q28 32 128 *)
  0x4e9c285c;       (* arm_TRN1 Q28 Q2 Q28 32 128 *)
  0x4ece6a21;       (* arm_TRN2 Q1 Q17 Q14 64 128 *)
  0x4ece2a2e;       (* arm_TRN1 Q14 Q17 Q14 64 128 *)
  0x3d800c01;       (* arm_STR Q1 X0 (Immediate_Offset (word 48)) *)
  0x4ed76b81;       (* arm_TRN2 Q1 Q28 Q23 64 128 *)
  0x3d80040e;       (* arm_STR Q14 X0 (Immediate_Offset (word 16)) *)
  0x4ed72b8e;       (* arm_TRN1 Q14 Q28 Q23 64 128 *)
  0x3d800801;       (* arm_STR Q1 X0 (Immediate_Offset (word 32)) *)
  0x3c84040e;       (* arm_STR Q14 X0 (Postimmediate_Offset (word 64)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NTT_EXEC = ARM_MK_EXEC_RULE mlkem_ntt_mc;;

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

let ntt_zetas_layer01234 = define
 `ntt_zetas_layer01234:int list =
   [-- &1600; -- &15749; -- &749; -- &7373; -- &40; -- &394; -- &687; -- &6762;
    &630; &6201; -- &1432; -- &14095; &848; &8347; &0; &0; &1062; &10453; &296;
    &2914; -- &882; -- &8682; &0; &0; -- &1410; -- &13879; &1339; &13180; &1476;
    &14529; &0; &0; &193; &1900; -- &283; -- &2786; &56; &551; &0; &0; &797;
    &7845; -- &1089; -- &10719; &1333; &13121; &0; &0; -- &543; -- &5345;
    &1426; &14036; -- &1235; -- &12156; &0; &0; -- &69; -- &679; &535; &5266;
    -- &447; -- &4400; &0; &0; &569; &5601; -- &936; -- &9213; -- &450;
    -- &4429; &0; &0; -- &1583; -- &15582; -- &1355; -- &13338; &821;
    &8081; &0; &0]`;;

let ntt_zetas_layer56 = define
`ntt_zetas_layer56:int list =
  [&289; &289; &331; &331; -- &76; -- &76; -- &1573; -- &1573; &2845;
   &2845; &3258; &3258; -- &748; -- &748; -- &15483; -- &15483; &17; &17;
   &583; &583; &1637; &1637; -- &1041; -- &1041; &167; &167; &5739;
   &5739; &16113; &16113; -- &10247; -- &10247; -- &568; -- &568;
   -- &680; -- &680; &723; &723; &1100; &1100; -- &5591; -- &5591; -- &6693;
   -- &6693; &7117; &7117; &10828; &10828; &1197; &1197; -- &1025;
   -- &1025; -- &1052; -- &1052; -- &1274; -- &1274; &11782; &11782;
   -- &10089; -- &10089; -- &10355; -- &10355; -- &12540; -- &12540; &1409;
   &1409; -- &48; -- &48; &756; &756; -- &314; -- &314; &13869; &13869;
   -- &472; -- &472; &7441; &7441; -- &3091; -- &3091; -- &667; -- &667;
   &233; &233; -- &1173; -- &1173; -- &279; -- &279; -- &6565; -- &6565;
   &2293; &2293; -- &11546; -- &11546; -- &2746; -- &2746; &650; &650;
   -- &1352; -- &1352; -- &816; -- &816; &632; &632; &6398; &6398;
   -- &13308; -- &13308; -- &8032; -- &8032; &6221; &6221; -- &1626;
   -- &1626; -- &540; -- &540; -- &1482; -- &1482; &1461; &1461; -- &16005;
   -- &16005; -- &5315; -- &5315; -- &14588; -- &14588; &14381; &14381;
   &1651; &1651; -- &1540; -- &1540; &952; &952; -- &642; -- &642;
   &16251; &16251; -- &15159; -- &15159; &9371; &9371; -- &6319;
   -- &6319; -- &464; -- &464; &33; &33; &1320; &1320; -- &1414; -- &1414;
   -- &4567; -- &4567; &325; &325; &12993; &12993; -- &13918; -- &13918;
   &939; &939; -- &892; -- &892; &733; &733; &268; &268; &9243; &9243;
   -- &8780; -- &8780; &7215; &7215; &2638; &2638; -- &1021; -- &1021;
   -- &941; -- &941; -- &992; -- &992; &641; &641; -- &10050; -- &10050;
   -- &9262; -- &9262; -- &9764; -- &9764; &6309; &6309; -- &1010; -- &1010;
   &1435; &1435; &807; &807; &452; &452; -- &9942; -- &9942; &14125;
   &14125; &7943; &7943; &4449; &4449; &1584; &1584; -- &1292; -- &1292;
   &375; &375; -- &1239; -- &1239; &15592; &15592; -- &12717; -- &12717;
   &3691; &3691; -- &12196; -- &12196; -- &1031; -- &1031; -- &109;
   -- &109; -- &780; -- &780; &1645; &1645; -- &10148; -- &10148; -- &1073;
   -- &1073; -- &7678; -- &7678; &16192; &16192; &1438; &1438; -- &461;
   -- &461; &1534; &1534; -- &927; -- &927; &14155; &14155; -- &4538;
   -- &4538; &15099; &15099; -- &9125; -- &9125; &1063; &1063; -- &556;
   -- &556; -- &1230; -- &1230; -- &863; -- &863; &10463; &10463; -- &5473;
   -- &5473; -- &12107; -- &12107; -- &8495; -- &8495; &319; &319; &757;
   &757; &561; &561; -- &735; -- &735; &3140; &3140; &7451; &7451; &5522;
   &5522; -- &7235; -- &7235; -- &682; -- &682; -- &712; -- &712; &1481;
   &1481; &648; &648; -- &6713; -- &6713; -- &7008; -- &7008; &14578;
   &14578; &6378; &6378; -- &525; -- &525; &403; &403; &1143; &1143;
   -- &554; -- &554; -- &5168; -- &5168; &3967; &3967; &11251; &11251;
   -- &5453; -- &5453; &1092; &1092; &1026; &1026; -- &1179; -- &1179; &886;
   &886; &10749; &10749; &10099; &10099; -- &11605; -- &11605; &8721;
   &8721; -- &855; -- &855; -- &219; -- &219; &1227; &1227; &910; &910;
   -- &8416; -- &8416; -- &2156; -- &2156; &12078; &12078; &8957; &8957;
   -- &1607; -- &1607; -- &1455; -- &1455; -- &1219; -- &1219; &885;
   &885; -- &15818; -- &15818; -- &14322; -- &14322; -- &11999;
   -- &11999; &8711; &8711; &1212; &1212; &1029; &1029; -- &394; -- &394;
   -- &1175; -- &1175; &11930; &11930; &10129; &10129; -- &3878; -- &3878;
   -- &11566; -- &11566]`;;

let ntt_constants = define
 `ntt_constants z_01234 z_56 s <=>
        (!i. i < 80
             ==> read(memory :> bytes16(word_add z_01234 (word(2 * i)))) s =
                 iword(EL i ntt_zetas_layer01234)) /\
        (!i. i < 384
             ==> read(memory :> bytes16(word_add z_56 (word(2 * i)))) s =
                 iword(EL i ntt_zetas_layer56))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NTT_CORRECT = prove
 (`!a z_01234 z_56 x pc.
      ALL (nonoverlapping (a,512))
          [(word pc,0x504); (z_01234,160); (z_56,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                ntt_constants z_01234 z_56 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x4ec) /\
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
   [`a:int64`; `z_01234:int64`; `z_56:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  REWRITE_TAC[ntt_constants] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  REWRITE_TAC[ntt_zetas_layer01234; ntt_zetas_layer56] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Manually restructure to match the 128-bit loads. It would be nicer
   *** if the simulation machinery did this automatically.
   ***)

  MEMORY_128_FROM_16_TAC "a" 32 THEN
  MEMORY_128_FROM_16_TAC "z_01234" 10 THEN
  MEMORY_128_FROM_16_TAC "z_56" 48 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  REPEAT STRIP_TAC THEN

  (*** Ghost up initial contents of Q7 since it isn't fully initialized ***)

  ABBREV_TAC `v7_init:int128 = read Q7 s0` THEN

  (*** Simulate all the way to the end, in effect unrolling loops ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_NTT_EXEC [n] THEN
             (SIMD_SIMPLIFY_TAC [barmul]))
            (1--904) THEN
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

let MLKEM_NTT_SUBROUTINE_CORRECT = prove
 (`!a z_01234 z_56 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x504); (z_01234,160); (z_56,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                ntt_constants z_01234 z_56 s /\
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
