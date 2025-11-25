(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
needs "arm/proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o";;
 ****)


let poly_basemul_acc_montgomery_cached_k3_mc = define_assert_from_elf
    "poly_basemul_acc_montgomery_cached_k3_mc" "arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o"
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
  0x3cc204e6;       (* arm_LDR Q6 X7 (Postimmediate_Offset (word 32)) *)
  0x3dc00453;       (* arm_LDR Q19 X2 (Immediate_Offset (word 16)) *)
  0x3cc20437;       (* arm_LDR Q23 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf002e;       (* arm_LDR Q14 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20451;       (* arm_LDR Q17 X2 (Postimmediate_Offset (word 32)) *)
  0x3dc0048b;       (* arm_LDR Q11 X4 (Immediate_Offset (word 16)) *)
  0x3cdf00fc;       (* arm_LDR Q28 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf747e;       (* arm_LDR Q30 X3 (Postimmediate_Offset (word 16)) *)
  0x3cc2049a;       (* arm_LDR Q26 X4 (Postimmediate_Offset (word 32)) *)
  0x3dc00510;       (* arm_LDR Q16 X8 (Immediate_Offset (word 16)) *)
  0x4e4e1ae8;       (* arm_UZP1 Q8 Q23 Q14 16 *)
  0x3dc004b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 16)) *)
  0x3cc204b2;       (* arm_LDR Q18 X5 (Postimmediate_Offset (word 32)) *)
  0x4e531a34;       (* arm_UZP1 Q20 Q17 Q19 16 *)
  0x4e4e5af8;       (* arm_UZP2 Q24 Q23 Q14 16 *)
  0x3cc2051f;       (* arm_LDR Q31 X8 (Postimmediate_Offset (word 32)) *)
  0x4e74c104;       (* arm_SMULL2_VEC Q4 Q8 Q20 16 *)
  0x4e4b1b59;       (* arm_UZP1 Q25 Q26 Q11 16 *)
  0x0e74c10d;       (* arm_SMULL_VEC Q13 Q8 Q20 16 *)
  0x4cdf74d7;       (* arm_LDR Q23 X6 (Postimmediate_Offset (word 16)) *)
  0x4e561a41;       (* arm_UZP1 Q1 Q18 Q22 16 *)
  0x0e7e830d;       (* arm_SMLAL_VEC Q13 Q24 Q30 16 *)
  0x4e7e8304;       (* arm_SMLAL2_VEC Q4 Q24 Q30 16 *)
  0x4e4b5b45;       (* arm_UZP2 Q5 Q26 Q11 16 *)
  0x4e618324;       (* arm_SMLAL2_VEC Q4 Q25 Q1 16 *)
  0x4e5c18dd;       (* arm_UZP1 Q29 Q6 Q28 16 *)
  0x4e7780a4;       (* arm_SMLAL2_VEC Q4 Q5 Q23 16 *)
  0x4cdf7527;       (* arm_LDR Q7 X9 (Postimmediate_Offset (word 16)) *)
  0x0e61832d;       (* arm_SMLAL_VEC Q13 Q25 Q1 16 *)
  0x4e535a31;       (* arm_UZP2 Q17 Q17 Q19 16 *)
  0x4e501bfb;       (* arm_UZP1 Q27 Q31 Q16 16 *)
  0x0e7780ad;       (* arm_SMLAL_VEC Q13 Q5 Q23 16 *)
  0x4e565a56;       (* arm_UZP2 Q22 Q18 Q22 16 *)
  0x0e71c112;       (* arm_SMULL_VEC Q18 Q8 Q17 16 *)
  0x4e5c58dc;       (* arm_UZP2 Q28 Q6 Q28 16 *)
  0x0e7b83ad;       (* arm_SMLAL_VEC Q13 Q29 Q27 16 *)
  0x4e7b83a4;       (* arm_SMLAL2_VEC Q4 Q29 Q27 16 *)
  0x4e505bfa;       (* arm_UZP2 Q26 Q31 Q16 16 *)
  0x4e678384;       (* arm_SMLAL2_VEC Q4 Q28 Q7 16 *)
  0x3dc004e3;       (* arm_LDR Q3 X7 (Immediate_Offset (word 16)) *)
  0x0e67838d;       (* arm_SMLAL_VEC Q13 Q28 Q7 16 *)
  0x3cc20427;       (* arm_LDR Q7 X1 (Postimmediate_Offset (word 32)) *)
  0x0e748312;       (* arm_SMLAL_VEC Q18 Q24 Q20 16 *)
  0x3cc2044f;       (* arm_LDR Q15 X2 (Postimmediate_Offset (word 32)) *)
  0x0e768332;       (* arm_SMLAL_VEC Q18 Q25 Q22 16 *)
  0x4e71c108;       (* arm_SMULL2_VEC Q8 Q8 Q17 16 *)
  0x3cdf0031;       (* arm_LDR Q17 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4419b7;       (* arm_UZP1 Q23 Q13 Q4 16 *)
  0x0e6180b2;       (* arm_SMLAL_VEC Q18 Q5 Q1 16 *)
  0x4e748308;       (* arm_SMLAL2_VEC Q8 Q24 Q20 16 *)
  0x4cdf7470;       (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  0x4e629ef7;       (* arm_MUL_VEC Q23 Q23 Q2 16 128 *)
  0x3dc004b3;       (* arm_LDR Q19 X5 (Immediate_Offset (word 16)) *)
  0x3dc0048e;       (* arm_LDR Q14 X4 (Immediate_Offset (word 16)) *)
  0x3cc2048b;       (* arm_LDR Q11 X4 (Postimmediate_Offset (word 32)) *)
  0x3cdf0054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e768328;       (* arm_SMLAL2_VEC Q8 Q25 Q22 16 *)
  0x4e6180a8;       (* arm_SMLAL2_VEC Q8 Q5 Q1 16 *)
  0x3cc204b6;       (* arm_LDR Q22 X5 (Postimmediate_Offset (word 32)) *)
  0x4e5118e1;       (* arm_UZP1 Q1 Q7 Q17 16 *)
  0x0e7a83b2;       (* arm_SMLAL_VEC Q18 Q29 Q26 16 *)
  0x0e6082ed;       (* arm_SMLAL_VEC Q13 Q23 Q0 16 *)
  0x4e4e597f;       (* arm_UZP2 Q31 Q11 Q14 16 *)
  0x4e5419f5;       (* arm_UZP1 Q21 Q15 Q20 16 *)
  0x4e6082e4;       (* arm_SMLAL2_VEC Q4 Q23 Q0 16 *)
  0x4cdf74c9;       (* arm_LDR Q9 X6 (Postimmediate_Offset (word 16)) *)
  0x0e7b8392;       (* arm_SMLAL_VEC Q18 Q28 Q27 16 *)
  0x4e7a83a8;       (* arm_SMLAL2_VEC Q8 Q29 Q26 16 *)
  0x3cc204f9;       (* arm_LDR Q25 X7 (Postimmediate_Offset (word 32)) *)
  0x0e75c03a;       (* arm_SMULL_VEC Q26 Q1 Q21 16 *)
  0x4e531ad8;       (* arm_UZP1 Q24 Q22 Q19 16 *)
  0x4e7b8388;       (* arm_SMLAL2_VEC Q8 Q28 Q27 16 *)
  0x4e5158fc;       (* arm_UZP2 Q28 Q7 Q17 16 *)
  0x4e4e197d;       (* arm_UZP1 Q29 Q11 Q14 16 *)
  0x4e75c037;       (* arm_SMULL2_VEC Q23 Q1 Q21 16 *)
  0x3cc2051b;       (* arm_LDR Q27 X8 (Postimmediate_Offset (word 32)) *)
  0x4e708397;       (* arm_SMLAL2_VEC Q23 Q28 Q16 16 *)
  0x3cdf010b;       (* arm_LDR Q11 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7883b7;       (* arm_SMLAL2_VEC Q23 Q29 Q24 16 *)
  0x4e4459a7;       (* arm_UZP2 Q7 Q13 Q4 16 *)
  0x4e535ad3;       (* arm_UZP2 Q19 Q22 Q19 16 *)
  0x4cdf7524;       (* arm_LDR Q4 X9 (Postimmediate_Offset (word 16)) *)
  0x4e6983f7;       (* arm_SMLAL2_VEC Q23 Q31 Q9 16 *)
  0x4e431b2d;       (* arm_UZP1 Q13 Q25 Q3 16 *)
  0x4e481a4e;       (* arm_UZP1 Q14 Q18 Q8 16 *)
  0x0e70839a;       (* arm_SMLAL_VEC Q26 Q28 Q16 16 *)
  0x4e4b5b71;       (* arm_UZP2 Q17 Q27 Q11 16 *)
  0x4e5459f4;       (* arm_UZP2 Q20 Q15 Q20 16 *)
  0x4e629dce;       (* arm_MUL_VEC Q14 Q14 Q2 16 128 *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x4e4b1b66;       (* arm_UZP1 Q6 Q27 Q11 16 *)
  0x0e7883ba;       (* arm_SMLAL_VEC Q26 Q29 Q24 16 *)
  0x4e435b30;       (* arm_UZP2 Q16 Q25 Q3 16 *)
  0x0e6983fa;       (* arm_SMLAL_VEC Q26 Q31 Q9 16 *)
  0x3dc004e3;       (* arm_LDR Q3 X7 (Immediate_Offset (word 16)) *)
  0x0e6681ba;       (* arm_SMLAL_VEC Q26 Q13 Q6 16 *)
  0x4e6081c8;       (* arm_SMLAL2_VEC Q8 Q14 Q0 16 *)
  0x3cc2051b;       (* arm_LDR Q27 X8 (Postimmediate_Offset (word 32)) *)
  0x0e6081d2;       (* arm_SMLAL_VEC Q18 Q14 Q0 16 *)
  0x3cc204f9;       (* arm_LDR Q25 X7 (Postimmediate_Offset (word 32)) *)
  0x4e6681b7;       (* arm_SMLAL2_VEC Q23 Q13 Q6 16 *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x4e648217;       (* arm_SMLAL2_VEC Q23 Q16 Q4 16 *)
  0x0e64821a;       (* arm_SMLAL_VEC Q26 Q16 Q4 16 *)
  0x3cdf0036;       (* arm_LDR Q22 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e485a5e;       (* arm_UZP2 Q30 Q18 Q8 16 *)
  0x0e74c032;       (* arm_SMULL_VEC Q18 Q1 Q20 16 *)
  0x0e758392;       (* arm_SMLAL_VEC Q18 Q28 Q21 16 *)
  0x3cc2044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 32)) *)
  0x0e7383b2;       (* arm_SMLAL_VEC Q18 Q29 Q19 16 *)
  0x4e5e38e5;       (* arm_ZIP1 Q5 Q7 Q30 16 128 *)
  0x4e571b44;       (* arm_UZP1 Q4 Q26 Q23 16 *)
  0x4e74c028;       (* arm_SMULL2_VEC Q8 Q1 Q20 16 *)
  0x4e5e78ea;       (* arm_ZIP2 Q10 Q7 Q30 16 128 *)
  0x0e7883f2;       (* arm_SMLAL_VEC Q18 Q31 Q24 16 *)
  0x4e629c8c;       (* arm_MUL_VEC Q12 Q4 Q2 16 128 *)
  0x3dc004a4;       (* arm_LDR Q4 X5 (Immediate_Offset (word 16)) *)
  0x3dc00494;       (* arm_LDR Q20 X4 (Immediate_Offset (word 16)) *)
  0x3cc20481;       (* arm_LDR Q1 X4 (Postimmediate_Offset (word 32)) *)
  0x3cdf005e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e758388;       (* arm_SMLAL2_VEC Q8 Q28 Q21 16 *)
  0x4e7383a8;       (* arm_SMLAL2_VEC Q8 Q29 Q19 16 *)
  0x3cc204b3;       (* arm_LDR Q19 X5 (Postimmediate_Offset (word 32)) *)
  0x4e7883e8;       (* arm_SMLAL2_VEC Q8 Q31 Q24 16 *)
  0x4cdf746f;       (* arm_LDR Q15 X3 (Postimmediate_Offset (word 16)) *)
  0x4e54583f;       (* arm_UZP2 Q31 Q1 Q20 16 *)
  0x0e60819a;       (* arm_SMLAL_VEC Q26 Q12 Q0 16 *)
  0x4e608197;       (* arm_SMLAL2_VEC Q23 Q12 Q0 16 *)
  0x4e5e19d5;       (* arm_UZP1 Q21 Q14 Q30 16 *)
  0x4e54183d;       (* arm_UZP1 Q29 Q1 Q20 16 *)
  0x4e561961;       (* arm_UZP1 Q1 Q11 Q22 16 *)
  0x4e7181a8;       (* arm_SMLAL2_VEC Q8 Q13 Q17 16 *)
  0x4cdf74c9;       (* arm_LDR Q9 X6 (Postimmediate_Offset (word 16)) *)
  0x0e7181b2;       (* arm_SMLAL_VEC Q18 Q13 Q17 16 *)
  0x4e441a78;       (* arm_UZP1 Q24 Q19 Q4 16 *)
  0x4e575b47;       (* arm_UZP2 Q7 Q26 Q23 16 *)
  0x0e75c03a;       (* arm_SMULL_VEC Q26 Q1 Q21 16 *)
  0x0e668212;       (* arm_SMLAL_VEC Q18 Q16 Q6 16 *)
  0x4e445a73;       (* arm_UZP2 Q19 Q19 Q4 16 *)
  0x4e668208;       (* arm_SMLAL2_VEC Q8 Q16 Q6 16 *)
  0x4e56597c;       (* arm_UZP2 Q28 Q11 Q22 16 *)
  0x4e75c037;       (* arm_SMULL2_VEC Q23 Q1 Q21 16 *)
  0x4e431b2d;       (* arm_UZP1 Q13 Q25 Q3 16 *)
  0x4e6f8397;       (* arm_SMLAL2_VEC Q23 Q28 Q15 16 *)
  0x3cdf010b;       (* arm_LDR Q11 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7883b7;       (* arm_SMLAL2_VEC Q23 Q29 Q24 16 *)
  0x4cdf7524;       (* arm_LDR Q4 X9 (Postimmediate_Offset (word 16)) *)
  0x4e6983f7;       (* arm_SMLAL2_VEC Q23 Q31 Q9 16 *)
  0x4e481a4c;       (* arm_UZP1 Q12 Q18 Q8 16 *)
  0x4e5e59d4;       (* arm_UZP2 Q20 Q14 Q30 16 *)
  0x0e6f839a;       (* arm_SMLAL_VEC Q26 Q28 Q15 16 *)
  0x3c820405;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 32)) *)
  0x4e629d8e;       (* arm_MUL_VEC Q14 Q12 Q2 16 128 *)
  0x3c9f000a;       (* arm_STR Q10 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4b5b71;       (* arm_UZP2 Q17 Q27 Q11 16 *)
  0xf10005ad;       (* arm_SUBS X13 X13 (rvalue (word 1)) *)
  0xb5fff7cd;       (* arm_CBNZ X13 (word 2096888) *)
  0x4e435b23;       (* arm_UZP2 Q3 Q25 Q3 16 *)
  0x4e74c030;       (* arm_SMULL2_VEC Q16 Q1 Q20 16 *)
  0x0e74c039;       (* arm_SMULL_VEC Q25 Q1 Q20 16 *)
  0x4e4b1b76;       (* arm_UZP1 Q22 Q27 Q11 16 *)
  0x4e758390;       (* arm_SMLAL2_VEC Q16 Q28 Q21 16 *)
  0x0e758399;       (* arm_SMLAL_VEC Q25 Q28 Q21 16 *)
  0x4e7383b0;       (* arm_SMLAL2_VEC Q16 Q29 Q19 16 *)
  0x0e7383b9;       (* arm_SMLAL_VEC Q25 Q29 Q19 16 *)
  0x4e7883f0;       (* arm_SMLAL2_VEC Q16 Q31 Q24 16 *)
  0x0e7883f9;       (* arm_SMLAL_VEC Q25 Q31 Q24 16 *)
  0x0e7181b9;       (* arm_SMLAL_VEC Q25 Q13 Q17 16 *)
  0x4e7181b0;       (* arm_SMLAL2_VEC Q16 Q13 Q17 16 *)
  0x4e768070;       (* arm_SMLAL2_VEC Q16 Q3 Q22 16 *)
  0x0e768079;       (* arm_SMLAL_VEC Q25 Q3 Q22 16 *)
  0x4e7681b7;       (* arm_SMLAL2_VEC Q23 Q13 Q22 16 *)
  0x0e7883ba;       (* arm_SMLAL_VEC Q26 Q29 Q24 16 *)
  0x0e6983fa;       (* arm_SMLAL_VEC Q26 Q31 Q9 16 *)
  0x0e7681ba;       (* arm_SMLAL_VEC Q26 Q13 Q22 16 *)
  0x4e501b2a;       (* arm_UZP1 Q10 Q25 Q16 16 *)
  0x4e648077;       (* arm_SMLAL2_VEC Q23 Q3 Q4 16 *)
  0x0e64807a;       (* arm_SMLAL_VEC Q26 Q3 Q4 16 *)
  0x4e629d4d;       (* arm_MUL_VEC Q13 Q10 Q2 16 128 *)
  0x0e6081d2;       (* arm_SMLAL_VEC Q18 Q14 Q0 16 *)
  0x4e6081c8;       (* arm_SMLAL2_VEC Q8 Q14 Q0 16 *)
  0x4e571b43;       (* arm_UZP1 Q3 Q26 Q23 16 *)
  0x4e629c78;       (* arm_MUL_VEC Q24 Q3 Q2 16 128 *)
  0x4e485a51;       (* arm_UZP2 Q17 Q18 Q8 16 *)
  0x0e6081b9;       (* arm_SMLAL_VEC Q25 Q13 Q0 16 *)
  0x4e6081b0;       (* arm_SMLAL2_VEC Q16 Q13 Q0 16 *)
  0x4e5138f5;       (* arm_ZIP1 Q21 Q7 Q17 16 128 *)
  0x4e5178f4;       (* arm_ZIP2 Q20 Q7 Q17 16 128 *)
  0x4e608317;       (* arm_SMLAL2_VEC Q23 Q24 Q0 16 *)
  0x3c820415;       (* arm_STR Q21 X0 (Postimmediate_Offset (word 32)) *)
  0x0e60831a;       (* arm_SMLAL_VEC Q26 Q24 Q0 16 *)
  0x4e505b2d;       (* arm_UZP2 Q13 Q25 Q16 16 *)
  0x3c9f0014;       (* arm_STR Q20 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e575b57;       (* arm_UZP2 Q23 Q26 Q23 16 *)
  0x4e4d3af2;       (* arm_ZIP1 Q18 Q23 Q13 16 128 *)
  0x4e4d7aed;       (* arm_ZIP2 Q13 Q23 Q13 16 128 *)
  0x3c820412;       (* arm_STR Q18 X0 (Postimmediate_Offset (word 32)) *)
  0x3c9f000d;       (* arm_STR Q13 X0 (Immediate_Offset (word 18446744073709551600)) *)
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
 (* Code length constants                                                     *)
 (* ------------------------------------------------------------------------- *)

 let LENGTH_POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_MC =
   REWRITE_CONV[poly_basemul_acc_montgomery_cached_k3_mc] `LENGTH poly_basemul_acc_montgomery_cached_k3_mc`
   |> CONV_RULE (RAND_CONV LENGTH_CONV);;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_PREAMBLE_LENGTH = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_PREAMBLE_LENGTH = 20`;;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_POSTAMBLE_LENGTH = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_POSTAMBLE_LENGTH = 24`;;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_START = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_START = POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_PREAMBLE_LENGTH`;;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_END = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_END = LENGTH poly_basemul_acc_montgomery_cached_k3_mc - POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_POSTAMBLE_LENGTH`;;

 let LENGTH_SIMPLIFY_CONV =
   REWRITE_CONV[LENGTH_POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_MC;
               POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_START; POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_END;
               POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_PREAMBLE_LENGTH; POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_POSTAMBLE_LENGTH] THENC
   NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

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
             read PC s = word (pc + POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_START)  /\
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
        (\s. read PC s = word (pc + POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K3_CORE_END) /\
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
       CONV_TAC LENGTH_SIMPLIFY_CONV THEN
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
      MAP_UNTIL_TARGET_PC (fun n -> ARM_STEPS_TAC poly_basemul_acc_montgomery_cached_k3_EXEC [n] THEN
                 (SIMD_SIMPLIFY_TAC [montred])) 1 THEN

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
      (REWRITE_RULE[fst poly_basemul_acc_montgomery_cached_k3_EXEC] (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV poly_basemul_acc_montgomery_cached_k3_SPEC)))
       `[D8; D9; D10; D11; D12; D13; D14; D15]` 64  THEN
    WORD_ARITH_TAC)
 ;;
