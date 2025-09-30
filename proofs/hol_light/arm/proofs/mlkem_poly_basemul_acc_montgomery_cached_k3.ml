(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o";;
 ****)


let poly_basemul_acc_montgomery_cached_k3_mc = define_assert_from_elf
    "poly_basemul_acc_montgomery_cached_k3_mc" "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o"
(*** BYTECODE START ***)
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x5281a02e;       (* arm_MOV W14 (rvalue (word 3329)) *)
  0x4e020dc0;       (* arm_DUP_GEN Q0 X14 16 128 *)
  0x52819fee;       (* arm_MOV W14 (rvalue (word 3327)) *)
  0x4e020dc2;       (* arm_DUP_GEN Q2 X14 16 128 *)
  0x91080024;       (* arm_ADD X4 X1 (rvalue (word 512)) *)
  0x91080045;       (* arm_ADD X5 X2 (rvalue (word 512)) *)
  0x91040066;       (* arm_ADD X6 X3 (rvalue (word 256)) *)
  0x91100027;       (* arm_ADD X7 X1 (rvalue (word 1024)) *)
  0x91100048;       (* arm_ADD X8 X2 (rvalue (word 1024)) *)
  0x91080069;       (* arm_ADD X9 X3 (rvalue (word 512)) *)
  0xd280020d;       (* arm_MOV X13 (rvalue (word 16)) *)
  0x3dc00447;       (* arm_LDR Q7 X2 (Immediate_Offset (word 16)) *)
  0x3cc20454;       (* arm_LDR Q20 X2 (Postimmediate_Offset (word 32)) *)
  0x3dc0042f;       (* arm_LDR Q15 X1 (Immediate_Offset (word 16)) *)
  0x4e471a88;       (* arm_UZP1 Q8 Q20 Q7 16 *)
  0x4e475a87;       (* arm_UZP2 Q7 Q20 Q7 16 *)
  0x4cdf7474;       (* arm_LDR Q20 X3 (Postimmediate_Offset (word 16)) *)
  0x3cc2043e;       (* arm_LDR Q30 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc2048b;       (* arm_LDR Q11 X4 (Postimmediate_Offset (word 32)) *)
  0x4e4f1bd0;       (* arm_UZP1 Q16 Q30 Q15 16 *)
  0x4e4f5bcf;       (* arm_UZP2 Q15 Q30 Q15 16 *)
  0x0e67c21e;       (* arm_SMULL_VEC Q30 Q16 Q7 16 *)
  0x4e67c207;       (* arm_SMULL2_VEC Q7 Q16 Q7 16 *)
  0x0e68c209;       (* arm_SMULL_VEC Q9 Q16 Q8 16 *)
  0x4e68c210;       (* arm_SMULL2_VEC Q16 Q16 Q8 16 *)
  0x0e6881fe;       (* arm_SMLAL_VEC Q30 Q15 Q8 16 *)
  0x4e6881e7;       (* arm_SMLAL2_VEC Q7 Q15 Q8 16 *)
  0x0e7481e9;       (* arm_SMLAL_VEC Q9 Q15 Q20 16 *)
  0x4e7481f0;       (* arm_SMLAL2_VEC Q16 Q15 Q20 16 *)
  0x3cdf0094;       (* arm_LDR Q20 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204af;       (* arm_LDR Q15 X5 (Postimmediate_Offset (word 32)) *)
  0x4e541968;       (* arm_UZP1 Q8 Q11 Q20 16 *)
  0x4e545974;       (* arm_UZP2 Q20 Q11 Q20 16 *)
  0x3cdf00ab;       (* arm_LDR Q11 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf74db;       (* arm_LDR Q27 X6 (Postimmediate_Offset (word 16)) *)
  0x4e4b19ea;       (* arm_UZP1 Q10 Q15 Q11 16 *)
  0x4e4b59ef;       (* arm_UZP2 Q15 Q15 Q11 16 *)
  0x0e6a8109;       (* arm_SMLAL_VEC Q9 Q8 Q10 16 *)
  0x4e6a8110;       (* arm_SMLAL2_VEC Q16 Q8 Q10 16 *)
  0x0e6f811e;       (* arm_SMLAL_VEC Q30 Q8 Q15 16 *)
  0x4e6f8107;       (* arm_SMLAL2_VEC Q7 Q8 Q15 16 *)
  0x0e7b8289;       (* arm_SMLAL_VEC Q9 Q20 Q27 16 *)
  0x4e7b8290;       (* arm_SMLAL2_VEC Q16 Q20 Q27 16 *)
  0x0e6a829e;       (* arm_SMLAL_VEC Q30 Q20 Q10 16 *)
  0x4e6a8287;       (* arm_SMLAL2_VEC Q7 Q20 Q10 16 *)
  0x3cc204f4;       (* arm_LDR Q20 X7 (Postimmediate_Offset (word 32)) *)
  0x3cdf00ef;       (* arm_LDR Q15 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20508;       (* arm_LDR Q8 X8 (Postimmediate_Offset (word 32)) *)
  0x4e4f1a8b;       (* arm_UZP1 Q11 Q20 Q15 16 *)
  0x4e4f5a94;       (* arm_UZP2 Q20 Q20 Q15 16 *)
  0x3cdf010f;       (* arm_LDR Q15 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf753b;       (* arm_LDR Q27 X9 (Postimmediate_Offset (word 16)) *)
  0x4e4f190a;       (* arm_UZP1 Q10 Q8 Q15 16 *)
  0x4e4f590f;       (* arm_UZP2 Q15 Q8 Q15 16 *)
  0x0e6a8169;       (* arm_SMLAL_VEC Q9 Q11 Q10 16 *)
  0x4e6a8170;       (* arm_SMLAL2_VEC Q16 Q11 Q10 16 *)
  0x0e6f817e;       (* arm_SMLAL_VEC Q30 Q11 Q15 16 *)
  0x4e6f8167;       (* arm_SMLAL2_VEC Q7 Q11 Q15 16 *)
  0x0e7b8289;       (* arm_SMLAL_VEC Q9 Q20 Q27 16 *)
  0x4e7b8290;       (* arm_SMLAL2_VEC Q16 Q20 Q27 16 *)
  0x0e6a829e;       (* arm_SMLAL_VEC Q30 Q20 Q10 16 *)
  0x4e6a8287;       (* arm_SMLAL2_VEC Q7 Q20 Q10 16 *)
  0x3cc2044f;       (* arm_LDR Q15 X2 (Postimmediate_Offset (word 32)) *)
  0x4e501934;       (* arm_UZP1 Q20 Q9 Q16 16 *)
  0x4e471bc8;       (* arm_UZP1 Q8 Q30 Q7 16 *)
  0x4e629e94;       (* arm_MUL_VEC Q20 Q20 Q2 16 128 *)
  0x4e629d08;       (* arm_MUL_VEC Q8 Q8 Q2 16 128 *)
  0x3cc20495;       (* arm_LDR Q21 X4 (Postimmediate_Offset (word 32)) *)
  0x0e608289;       (* arm_SMLAL_VEC Q9 Q20 Q0 16 *)
  0x4e608290;       (* arm_SMLAL2_VEC Q16 Q20 Q0 16 *)
  0x0e60811e;       (* arm_SMLAL_VEC Q30 Q8 Q0 16 *)
  0x4e608107;       (* arm_SMLAL2_VEC Q7 Q8 Q0 16 *)
  0x3cdf0086;       (* arm_LDR Q6 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e50593b;       (* arm_UZP2 Q27 Q9 Q16 16 *)
  0x4e475bca;       (* arm_UZP2 Q10 Q30 Q7 16 *)
  0x3cdf0050;       (* arm_LDR Q16 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0043e;       (* arm_LDR Q30 X1 (Immediate_Offset (word 16)) *)
  0x4cdf7469;       (* arm_LDR Q9 X3 (Postimmediate_Offset (word 16)) *)
  0x3cc204a1;       (* arm_LDR Q1 X5 (Postimmediate_Offset (word 32)) *)
  0x3cdf00ac;       (* arm_LDR Q12 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf74d8;       (* arm_LDR Q24 X6 (Postimmediate_Offset (word 16)) *)
  0x3cc204f3;       (* arm_LDR Q19 X7 (Postimmediate_Offset (word 32)) *)
  0x3cdf00ff;       (* arm_LDR Q31 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20511;       (* arm_LDR Q17 X8 (Postimmediate_Offset (word 32)) *)
  0x3cdf0112;       (* arm_LDR Q18 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf7539;       (* arm_LDR Q25 X9 (Postimmediate_Offset (word 16)) *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x3cc20434;       (* arm_LDR Q20 X1 (Postimmediate_Offset (word 32)) *)
  0x4e5019e7;       (* arm_UZP1 Q7 Q15 Q16 16 *)
  0x4e5059ef;       (* arm_UZP2 Q15 Q15 Q16 16 *)
  0x4e5e1a88;       (* arm_UZP1 Q8 Q20 Q30 16 *)
  0x4e5e5a94;       (* arm_UZP2 Q20 Q20 Q30 16 *)
  0x0e6fc11e;       (* arm_SMULL_VEC Q30 Q8 Q15 16 *)
  0x4e6fc10f;       (* arm_SMULL2_VEC Q15 Q8 Q15 16 *)
  0x0e67c10b;       (* arm_SMULL_VEC Q11 Q8 Q7 16 *)
  0x4e67c108;       (* arm_SMULL2_VEC Q8 Q8 Q7 16 *)
  0x0e67829e;       (* arm_SMLAL_VEC Q30 Q20 Q7 16 *)
  0x4e67828f;       (* arm_SMLAL2_VEC Q15 Q20 Q7 16 *)
  0x0e69828b;       (* arm_SMLAL_VEC Q11 Q20 Q9 16 *)
  0x4e698288;       (* arm_SMLAL2_VEC Q8 Q20 Q9 16 *)
  0x4e461aa7;       (* arm_UZP1 Q7 Q21 Q6 16 *)
  0x4e465ab4;       (* arm_UZP2 Q20 Q21 Q6 16 *)
  0x4e4c1830;       (* arm_UZP1 Q16 Q1 Q12 16 *)
  0x4e4c5829;       (* arm_UZP2 Q9 Q1 Q12 16 *)
  0x0e7080eb;       (* arm_SMLAL_VEC Q11 Q7 Q16 16 *)
  0x4e7080e8;       (* arm_SMLAL2_VEC Q8 Q7 Q16 16 *)
  0x0e6980fe;       (* arm_SMLAL_VEC Q30 Q7 Q9 16 *)
  0x4e6980ef;       (* arm_SMLAL2_VEC Q15 Q7 Q9 16 *)
  0x0e78828b;       (* arm_SMLAL_VEC Q11 Q20 Q24 16 *)
  0x4e788288;       (* arm_SMLAL2_VEC Q8 Q20 Q24 16 *)
  0x0e70829e;       (* arm_SMLAL_VEC Q30 Q20 Q16 16 *)
  0x4e70828f;       (* arm_SMLAL2_VEC Q15 Q20 Q16 16 *)
  0x4e5f1a67;       (* arm_UZP1 Q7 Q19 Q31 16 *)
  0x4e5f5a74;       (* arm_UZP2 Q20 Q19 Q31 16 *)
  0x4e521a30;       (* arm_UZP1 Q16 Q17 Q18 16 *)
  0x4e525a29;       (* arm_UZP2 Q9 Q17 Q18 16 *)
  0x0e7080eb;       (* arm_SMLAL_VEC Q11 Q7 Q16 16 *)
  0x4e7080e8;       (* arm_SMLAL2_VEC Q8 Q7 Q16 16 *)
  0x0e6980fe;       (* arm_SMLAL_VEC Q30 Q7 Q9 16 *)
  0x4e6980ef;       (* arm_SMLAL2_VEC Q15 Q7 Q9 16 *)
  0x0e79828b;       (* arm_SMLAL_VEC Q11 Q20 Q25 16 *)
  0x4e798288;       (* arm_SMLAL2_VEC Q8 Q20 Q25 16 *)
  0x0e70829e;       (* arm_SMLAL_VEC Q30 Q20 Q16 16 *)
  0x4e70828f;       (* arm_SMLAL2_VEC Q15 Q20 Q16 16 *)
  0x3dc00450;       (* arm_LDR Q16 X2 (Immediate_Offset (word 16)) *)
  0x4e481967;       (* arm_UZP1 Q7 Q11 Q8 16 *)
  0x4e4f1bd4;       (* arm_UZP1 Q20 Q30 Q15 16 *)
  0x4e629ce7;       (* arm_MUL_VEC Q7 Q7 Q2 16 128 *)
  0x4e629e94;       (* arm_MUL_VEC Q20 Q20 Q2 16 128 *)
  0x4e4a7b69;       (* arm_ZIP2 Q9 Q27 Q10 16 128 *)
  0x4e4a3b7b;       (* arm_ZIP1 Q27 Q27 Q10 16 128 *)
  0x0e6080eb;       (* arm_SMLAL_VEC Q11 Q7 Q0 16 *)
  0x4e6080e8;       (* arm_SMLAL2_VEC Q8 Q7 Q0 16 *)
  0x0e60829e;       (* arm_SMLAL_VEC Q30 Q20 Q0 16 *)
  0x4e60828f;       (* arm_SMLAL2_VEC Q15 Q20 Q0 16 *)
  0x3c82041b;       (* arm_STR Q27 X0 (Postimmediate_Offset (word 32)) *)
  0x4e48597b;       (* arm_UZP2 Q27 Q11 Q8 16 *)
  0x3c9f0009;       (* arm_STR Q9 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4f5bca;       (* arm_UZP2 Q10 Q30 Q15 16 *)
  0x3dc0043e;       (* arm_LDR Q30 X1 (Immediate_Offset (word 16)) *)
  0x3cc2044f;       (* arm_LDR Q15 X2 (Postimmediate_Offset (word 32)) *)
  0x4cdf7469;       (* arm_LDR Q9 X3 (Postimmediate_Offset (word 16)) *)
  0x3cc20495;       (* arm_LDR Q21 X4 (Postimmediate_Offset (word 32)) *)
  0x3cdf0086;       (* arm_LDR Q6 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204a1;       (* arm_LDR Q1 X5 (Postimmediate_Offset (word 32)) *)
  0x3cdf00ac;       (* arm_LDR Q12 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf74d8;       (* arm_LDR Q24 X6 (Postimmediate_Offset (word 16)) *)
  0x3cc204f3;       (* arm_LDR Q19 X7 (Postimmediate_Offset (word 32)) *)
  0x3cdf00ff;       (* arm_LDR Q31 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20511;       (* arm_LDR Q17 X8 (Postimmediate_Offset (word 32)) *)
  0x3cdf0112;       (* arm_LDR Q18 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf7539;       (* arm_LDR Q25 X9 (Postimmediate_Offset (word 16)) *)
  0xd10005ad;       (* arm_SUB X13 X13 (rvalue (word 1)) *)
  0xb5fff7cd;       (* arm_CBNZ X13 (word 2096888) *)
  0x3cc20427;       (* arm_LDR Q7 X1 (Postimmediate_Offset (word 32)) *)
  0x4e5019f4;       (* arm_UZP1 Q20 Q15 Q16 16 *)
  0x4e5059ef;       (* arm_UZP2 Q15 Q15 Q16 16 *)
  0x4e5e18f7;       (* arm_UZP1 Q23 Q7 Q30 16 *)
  0x4e5e58eb;       (* arm_UZP2 Q11 Q7 Q30 16 *)
  0x4e74c2e8;       (* arm_SMULL2_VEC Q8 Q23 Q20 16 *)
  0x0e74c2e5;       (* arm_SMULL_VEC Q5 Q23 Q20 16 *)
  0x4e6fc2fe;       (* arm_SMULL2_VEC Q30 Q23 Q15 16 *)
  0x4e4c183c;       (* arm_UZP1 Q28 Q1 Q12 16 *)
  0x4e698168;       (* arm_SMLAL2_VEC Q8 Q11 Q9 16 *)
  0x0e698165;       (* arm_SMLAL_VEC Q5 Q11 Q9 16 *)
  0x4e461aa3;       (* arm_UZP1 Q3 Q21 Q6 16 *)
  0x0e6fc2f0;       (* arm_SMULL_VEC Q16 Q23 Q15 16 *)
  0x4e7c8068;       (* arm_SMLAL2_VEC Q8 Q3 Q28 16 *)
  0x0e7c8065;       (* arm_SMLAL_VEC Q5 Q3 Q28 16 *)
  0x4e465abd;       (* arm_UZP2 Q29 Q21 Q6 16 *)
  0x4e521a27;       (* arm_UZP1 Q7 Q17 Q18 16 *)
  0x4e7883a8;       (* arm_SMLAL2_VEC Q8 Q29 Q24 16 *)
  0x4e5f1a6e;       (* arm_UZP1 Q14 Q19 Q31 16 *)
  0x0e748170;       (* arm_SMLAL_VEC Q16 Q11 Q20 16 *)
  0x4e74817e;       (* arm_SMLAL2_VEC Q30 Q11 Q20 16 *)
  0x4e6781c8;       (* arm_SMLAL2_VEC Q8 Q14 Q7 16 *)
  0x4e4c5834;       (* arm_UZP2 Q20 Q1 Q12 16 *)
  0x4e5f5a75;       (* arm_UZP2 Q21 Q19 Q31 16 *)
  0x4e74807e;       (* arm_SMLAL2_VEC Q30 Q3 Q20 16 *)
  0x0e748070;       (* arm_SMLAL_VEC Q16 Q3 Q20 16 *)
  0x0e7883a5;       (* arm_SMLAL_VEC Q5 Q29 Q24 16 *)
  0x4e525a29;       (* arm_UZP2 Q9 Q17 Q18 16 *)
  0x4e7c83be;       (* arm_SMLAL2_VEC Q30 Q29 Q28 16 *)
  0x0e7c83b0;       (* arm_SMLAL_VEC Q16 Q29 Q28 16 *)
  0x0e6781c5;       (* arm_SMLAL_VEC Q5 Q14 Q7 16 *)
  0x4e7982a8;       (* arm_SMLAL2_VEC Q8 Q21 Q25 16 *)
  0x4e6981de;       (* arm_SMLAL2_VEC Q30 Q14 Q9 16 *)
  0x0e6981d0;       (* arm_SMLAL_VEC Q16 Q14 Q9 16 *)
  0x0e7982a5;       (* arm_SMLAL_VEC Q5 Q21 Q25 16 *)
  0x4e4a3b74;       (* arm_ZIP1 Q20 Q27 Q10 16 128 *)
  0x4e6782be;       (* arm_SMLAL2_VEC Q30 Q21 Q7 16 *)
  0x0e6782b0;       (* arm_SMLAL_VEC Q16 Q21 Q7 16 *)
  0x4e4818a7;       (* arm_UZP1 Q7 Q5 Q8 16 *)
  0x3c820414;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 32)) *)
  0x4e629cef;       (* arm_MUL_VEC Q15 Q7 Q2 16 128 *)
  0x4e5e1a07;       (* arm_UZP1 Q7 Q16 Q30 16 *)
  0x4e4a7b7f;       (* arm_ZIP2 Q31 Q27 Q10 16 128 *)
  0x4e629cf4;       (* arm_MUL_VEC Q20 Q7 Q2 16 128 *)
  0x0e6081e5;       (* arm_SMLAL_VEC Q5 Q15 Q0 16 *)
  0x4e6081e8;       (* arm_SMLAL2_VEC Q8 Q15 Q0 16 *)
  0x3c9f001f;       (* arm_STR Q31 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e60829e;       (* arm_SMLAL2_VEC Q30 Q20 Q0 16 *)
  0x0e608290;       (* arm_SMLAL_VEC Q16 Q20 Q0 16 *)
  0x4e4858af;       (* arm_UZP2 Q15 Q5 Q8 16 *)
  0x4e5e5a14;       (* arm_UZP2 Q20 Q16 Q30 16 *)
  0x4e5439e7;       (* arm_ZIP1 Q7 Q15 Q20 16 128 *)
  0x4e5479f4;       (* arm_ZIP2 Q20 Q15 Q20 16 128 *)
  0x3c820407;       (* arm_STR Q7 X0 (Postimmediate_Offset (word 32)) *)
  0x3c9f0014;       (* arm_STR Q20 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let pmull = define
`pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc3 = define
  `pmull_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int) =
              pmull x20 x21 y20 y21 + pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc3 = define
  `pmul_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc3 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21) rem &3329`;;

let basemul3_even = define
 `basemul3_even x0 y0 y0t x1 y1 y1t x2 y2 y2t = \i.
    pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)
 `;;

let basemul3_odd = define
`basemul3_odd x0 y0 x1 y1 x2 y2 = \i.
  pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
            (y0 (2 * i + 1)) (y0 (2 * i))
            (x1 (2 * i)) (x1 (2 * i + 1))
            (y1 (2 * i + 1)) (y1 (2 * i))
            (x2 (2 * i)) (x2 (2 * i + 1))
            (y2 (2 * i + 1)) (y2 (2 * i))
`;;

 let poly_basemul_acc_montgomery_cached_k3_EXEC = ARM_MK_EXEC_RULE poly_basemul_acc_montgomery_cached_k3_mc;;

 (* ------------------------------------------------------------------------- *)
 (* Hacky tweaking conversion to write away non-free state component reads.   *)
 (* ------------------------------------------------------------------------- *)

 let lemma = prove
  (`!base size s n.
         n + 2 <= size
         ==> read(memory :> bytes16(word_add base (word n))) s =
             word((read (memory :> bytes(base,size)) s DIV 2 EXP (8 * n)))`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
   SPEC_TAC(`read memory s`,`m:int64->byte`) THEN GEN_TAC THEN
   REWRITE_TAC[READ_BYTES_DIV] THEN
   REWRITE_TAC[bytes16; READ_COMPONENT_COMPOSE; asword; through; read] THEN
   ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_16] THEN
   REWRITE_TAC[ARITH_RULE `16 = 8 * 2`; READ_BYTES_MOD] THEN
   ASM_SIMP_TAC[ARITH_RULE `n + 2 <= size ==> MIN (size - n) 2 = MIN 2 2`]);;

 let BOUNDED_QUANT_READ_MEM = prove
  (`(!x base s.
      (!i. i < n
           ==> read(memory :> bytes16(word_add base (word(2 * i)))) s =
               x i) <=>
      (!i. i < n
           ==> word((read(memory :> bytes(base,2 * n)) s DIV 2 EXP (16 * i))) =
               x i)) /\
    (!x p base s.
      (!i. i < n
           ==> (ival(read(memory :> bytes16(word_add base (word(2 * i)))) s) ==
                x i) (mod p)) <=>
      (!i. i < n
           ==> (ival(word((read(memory :> bytes(base,2 * n)) s DIV 2 EXP (16 * i))):int16) ==
                x i) (mod p))) /\
    (!x p c base s.
      (!i. i < n /\ c i
           ==> (ival(read(memory :> bytes16(word_add base (word(2 * i)))) s) ==
                x i) (mod p)) <=>
      (!i. i < n /\ c i
           ==> (ival(word((read(memory :> bytes(base,2 * n)) s DIV 2 EXP (16 * i))):int16) ==
                x i) (mod p)))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`base:int64`; `2 * n`] lemma) THEN
   SIMP_TAC[ARITH_RULE `2 * i + 2 <= 2 * n <=> i < n`] THEN
   REWRITE_TAC[ARITH_RULE `8 * 2 * i = 16 * i`]);;

 let even_odd_split_lemma = prove
  (`(!i. i < 128 ==> P (4 * i) i /\ Q(4 * i + 2) i) <=>
    (!i. i < 256 /\ EVEN i ==> P(2 * i) (i DIV 2)) /\
    (!i. i < 256 /\ ODD i ==> Q(2 * i) (i DIV 2))`,
   REWRITE_TAC[IMP_CONJ] THEN
   CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   CONV_TAC CONJ_ACI_RULE);;

 let TWEAK_CONV =
   REWRITE_CONV[even_odd_split_lemma] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_RULE
     `word_add x (word(a + b)) = word_add (word_add x (word a)) (word b)`] THENC
   REWRITE_CONV[BOUNDED_QUANT_READ_MEM] THENC
   NUM_REDUCE_CONV;;

 let poly_basemul_acc_montgomery_cached_k3_GOAL = `forall srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc.
      ALL (nonoverlapping (dst, 512))
          [(word pc, LENGTH poly_basemul_acc_montgomery_cached_k3_mc); (srcA, 1536); (srcB, 1536); (srcBt, 768)]
      ==>
      ensures arm
        (\s. aligned_bytes_loaded s (word pc) poly_basemul_acc_montgomery_cached_k3_mc /\
             read PC s = word (pc + 20)  /\
             C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
             (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (2 * i)))) s = x0 i)        /\
             (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (2 * i)))) s = y0 i)        /\
             (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (2 * i)))) s = y0t i)       /\
             (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (512 + 2 * i)))) s = x1 i)  /\
             (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (512 + 2 * i)))) s = y1 i)  /\
             (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
             (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (1024 + 2 * i)))) s = x2 i)  /\
             (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (1024 + 2 * i)))) s = y2 i)  /\
             (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (512  + 2 * i)))) s = y2t i)
        )
        (\s. read PC s = word (pc + 856) /\
             ((!i. i < 256 ==> abs(ival(x0 i)) <= &2 pow 12 /\ abs(ival(x1 i)) <= &2 pow 12
                                                            /\ abs(ival(x2 i)) <= &2 pow 12)
               ==>
              (!i. i < 128 ==> (ival(read(memory :> bytes16(word_add dst (word (4 * i)))) s) ==
                                   basemul3_even (ival o x0) (ival o y0) (ival o y0t)
                                                 (ival o x1) (ival o y1) (ival o y1t)
                                                 (ival o x2) (ival o y2) (ival o y2t) i) (mod &3329)  /\
                              (ival(read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s) ==
                                   basemul3_odd (ival o x0) (ival o y0)
                                                (ival o x1) (ival o y1)
                                                (ival o x2) (ival o y2) i) (mod &3329))))
        // Register and memory footprint
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
         MAYCHANGE [memory :> bytes(dst, 512)])
    `;;

  (* ------------------------------------------------------------------------- *)
  (* Proof                                                                     *)
  (* ------------------------------------------------------------------------- *)

 let poly_basemul_acc_montgomery_cached_k3_SPEC = prove (poly_basemul_acc_montgomery_cached_k3_GOAL,
       REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
        MODIFIABLE_SIMD_REGS;
        NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst poly_basemul_acc_montgomery_cached_k3_EXEC] THEN
      REPEAT STRIP_TAC THEN

      (* Split quantified assumptions into separate cases *)
      CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
      CONV_TAC((ONCE_DEPTH_CONV NUM_MULT_CONV) THENC (ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN

      (* Initialize symbolic execution *)
      ENSURES_INIT_TAC "s0" THEN

      (* Rewrite memory-read assumptions from 16-bit granularity
       * to 128-bit granularity. *)
      MEMORY_128_FROM_16_TAC "srcA" 96 THEN
      MEMORY_128_FROM_16_TAC "srcB" 96 THEN
      MEMORY_128_FROM_16_TAC "srcBt" 48 THEN
      ASM_REWRITE_TAC [WORD_ADD_0] THEN
      (* Forget original shape of assumption *)
      DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcA) s = x`] THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcB) s = x`] THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcBt) s = x`] THEN

      (* Symbolic execution
         Note that we simplify eagerly after every step.
         This reduces the proof time *)
      REPEAT STRIP_TAC THEN
      MAP_EVERY (fun n -> ARM_STEPS_TAC poly_basemul_acc_montgomery_cached_k3_EXEC [n] THEN
                 (SIMD_SIMPLIFY_TAC [montred])) (1--1080) THEN

      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN
      ASM_REWRITE_TAC [] THEN

      (* Reverse restructuring *)
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        CONV_RULE (SIMD_SIMPLIFY_CONV []) o
        CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
        check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

      (* Split quantified post-condition into separate cases *)
      CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV
               THENC (TRY_CONV (ONCE_DEPTH_CONV NUM_ADD_CONV))) THEN
      CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC [WORD_ADD_0] THEN

      (* Forget all state-related assumptions, but keep bounds at least *)
      DISCARD_STATE_TAC "s1080" THEN

     (* Split into one congruence goals per index. *)
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[basemul3_even; basemul3_odd;
                 pmul_acc3; pmull_acc3; pmull; o_THM] THEN
     CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN

     (* Solve the congruence goals *)

    ASSUM_LIST((fun ths -> W(MP_TAC o CONJUNCT1 o GEN_CONGBOUND_RULE ths o
      rand o lhand o rator o snd))) THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC INT_RING
  );;

 (* NOTE: This needs to be kept in sync with the CBMC spec in
  * mlkem/native/aarch64/src/arith_native_aarch64.h *)
 let poly_basemul_acc_montgomery_cached_k3_SPEC' = prove(
    `forall srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc returnaddress stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
         [(dst, 512); (word_sub stackpointer (word 64),64)]
         [(word pc, LENGTH poly_basemul_acc_montgomery_cached_k3_mc); (srcA, 1536); (srcB, 1536); (srcBt, 768)] /\
       nonoverlapping (dst,512) (word_sub stackpointer (word 64),64)
       ==>
       ensures arm
       (\s. // Assert that poly_basemul_acc_montgomery_cached_k3 is loaded at PC
         aligned_bytes_loaded s (word pc) poly_basemul_acc_montgomery_cached_k3_mc /\
         read PC s = word pc /\
         read SP s = stackpointer /\
         read X30 s = returnaddress /\
         C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
         // Give names to in-memory data to be
         // able to refer to them in the post-condition
         (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (2 * i)))) s = x0 i) /\
         (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (2 * i)))) s = y0 i) /\
         (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (2 * i)))) s = y0t i) /\
         (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (512 + 2 * i)))) s = x1 i) /\
         (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (512 + 2 * i)))) s = y1 i) /\
         (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
         (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (1024 + 2 * i)))) s = x2 i) /\
         (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (1024 + 2 * i)))) s = y2 i) /\
         (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (512  + 2 * i)))) s = y2t i)
       )
       (\s. read PC s = returnaddress /\
             ((!i. i < 256 ==> abs(ival(x0 i)) <= &2 pow 12 /\ abs(ival(x1 i)) <= &2 pow 12
                                                            /\ abs(ival(x2 i)) <= &2 pow 12)
               ==>
              (!i. i < 128 ==> (ival(read(memory :> bytes16(word_add dst (word (4 * i)))) s) ==
                                   basemul3_even (ival o x0) (ival o y0) (ival o y0t)
                                                 (ival o x1) (ival o y1) (ival o y1t)
                                                 (ival o x2) (ival o y2) (ival o y2t) i) (mod &3329)  /\
                              (ival(read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s) ==
                                   basemul3_odd (ival o x0) (ival o y0)
                                                (ival o x1) (ival o y1)
                                                (ival o x2) (ival o y2) i) (mod &3329))))
       // Register and memory footprint
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst, 512);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`,
   REWRITE_TAC[fst poly_basemul_acc_montgomery_cached_k3_EXEC] THEN
   CONV_TAC TWEAK_CONV THEN
   ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) poly_basemul_acc_montgomery_cached_k3_EXEC
      (REWRITE_RULE[fst poly_basemul_acc_montgomery_cached_k3_EXEC] (CONV_RULE TWEAK_CONV poly_basemul_acc_montgomery_cached_k3_SPEC))
       `[D8; D9; D10; D11; D12; D13; D14; D15]` 64  THEN
    WORD_ARITH_TAC)
 ;;
