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
  0x3dc0042d;       (* arm_LDR Q13 X1 (Immediate_Offset (word 16)) *)
  0x3cc20421;       (* arm_LDR Q1 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc20443;       (* arm_LDR Q3 X2 (Postimmediate_Offset (word 32)) *)
  0x3cdf004b;       (* arm_LDR Q11 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20491;       (* arm_LDR Q17 X4 (Postimmediate_Offset (word 32)) *)
  0x4cdf7472;       (* arm_LDR Q18 X3 (Postimmediate_Offset (word 16)) *)
  0x3cc204bb;       (* arm_LDR Q27 X5 (Postimmediate_Offset (word 32)) *)
  0x3cdf00ae;       (* arm_LDR Q14 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4d583e;       (* arm_UZP2 Q30 Q1 Q13 16 *)
  0x3dc00509;       (* arm_LDR Q9 X8 (Immediate_Offset (word 16)) *)
  0x4e4b1874;       (* arm_UZP1 Q20 Q3 Q11 16 *)
  0x4e4d1821;       (* arm_UZP1 Q1 Q1 Q13 16 *)
  0x3cdf009d;       (* arm_LDR Q29 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204e8;       (* arm_LDR Q8 X7 (Postimmediate_Offset (word 32)) *)
  0x0e74c03a;       (* arm_SMULL_VEC Q26 Q1 Q20 16 *)
  0x3cdf00f5;       (* arm_LDR Q21 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e7283da;       (* arm_SMLAL_VEC Q26 Q30 Q18 16 *)
  0x4cdf74c7;       (* arm_LDR Q7 X6 (Postimmediate_Offset (word 16)) *)
  0x4e74c037;       (* arm_SMULL2_VEC Q23 Q1 Q20 16 *)
  0x4e4e1b78;       (* arm_UZP1 Q24 Q27 Q14 16 *)
  0x4e5d5a36;       (* arm_UZP2 Q22 Q17 Q29 16 *)
  0x4e5d1a33;       (* arm_UZP1 Q19 Q17 Q29 16 *)
  0x4e7283d7;       (* arm_SMLAL2_VEC Q23 Q30 Q18 16 *)
  0x3cc2051f;       (* arm_LDR Q31 X8 (Postimmediate_Offset (word 32)) *)
  0x4e4b586d;       (* arm_UZP2 Q13 Q3 Q11 16 *)
  0x4e788277;       (* arm_SMLAL2_VEC Q23 Q19 Q24 16 *)
  0x4cdf7525;       (* arm_LDR Q5 X9 (Postimmediate_Offset (word 16)) *)
  0x0e78827a;       (* arm_SMLAL_VEC Q26 Q19 Q24 16 *)
  0x4e55190f;       (* arm_UZP1 Q15 Q8 Q21 16 *)
  0x0e6dc032;       (* arm_SMULL_VEC Q18 Q1 Q13 16 *)
  0x0e6782da;       (* arm_SMLAL_VEC Q26 Q22 Q7 16 *)
  0x4e491bea;       (* arm_UZP1 Q10 Q31 Q9 16 *)
  0x4e6782d7;       (* arm_SMLAL2_VEC Q23 Q22 Q7 16 *)
  0x4e555910;       (* arm_UZP2 Q16 Q8 Q21 16 *)
  0x4e6a81f7;       (* arm_SMLAL2_VEC Q23 Q15 Q10 16 *)
  0x4e4e5b64;       (* arm_UZP2 Q4 Q27 Q14 16 *)
  0x4e658217;       (* arm_SMLAL2_VEC Q23 Q16 Q5 16 *)
  0x4cdf7479;       (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  0x0e6a81fa;       (* arm_SMLAL_VEC Q26 Q15 Q10 16 *)
  0x3cc20495;       (* arm_LDR Q21 X4 (Postimmediate_Offset (word 32)) *)
  0x3dc004ec;       (* arm_LDR Q12 X7 (Immediate_Offset (word 16)) *)
  0x0e65821a;       (* arm_SMLAL_VEC Q26 Q16 Q5 16 *)
  0x4e495bf1;       (* arm_UZP2 Q17 Q31 Q9 16 *)
  0x0e7483d2;       (* arm_SMLAL_VEC Q18 Q30 Q20 16 *)
  0x3dc0043c;       (* arm_LDR Q28 X1 (Immediate_Offset (word 16)) *)
  0x0e648272;       (* arm_SMLAL_VEC Q18 Q19 Q4 16 *)
  0x0e7882d2;       (* arm_SMLAL_VEC Q18 Q22 Q24 16 *)
  0x0e7181f2;       (* arm_SMLAL_VEC Q18 Q15 Q17 16 *)
  0x4e571b5d;       (* arm_UZP1 Q29 Q26 Q23 16 *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x4e6dc028;       (* arm_SMULL2_VEC Q8 Q1 Q13 16 *)
  0x3cdf008d;       (* arm_LDR Q13 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e629fa6;       (* arm_MUL_VEC Q6 Q29 Q2 16 128 *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x3dc0051d;       (* arm_LDR Q29 X8 (Immediate_Offset (word 16)) *)
  0x3cc204a3;       (* arm_LDR Q3 X5 (Postimmediate_Offset (word 32)) *)
  0x3cc20507;       (* arm_LDR Q7 X8 (Postimmediate_Offset (word 32)) *)
  0x4e7483c8;       (* arm_SMLAL2_VEC Q8 Q30 Q20 16 *)
  0x3cc2044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 32)) *)
  0x0e6a8212;       (* arm_SMLAL_VEC Q18 Q16 Q10 16 *)
  0x4e5c597e;       (* arm_UZP2 Q30 Q11 Q28 16 *)
  0x4e648268;       (* arm_SMLAL2_VEC Q8 Q19 Q4 16 *)
  0x4e6080d7;       (* arm_SMLAL2_VEC Q23 Q6 Q0 16 *)
  0x3cdf0045;       (* arm_LDR Q5 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4d1ab3;       (* arm_UZP1 Q19 Q21 Q13 16 *)
  0x4e7882c8;       (* arm_SMLAL2_VEC Q8 Q22 Q24 16 *)
  0x0e6080da;       (* arm_SMLAL_VEC Q26 Q6 Q0 16 *)
  0x3cdf00b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e5c1961;       (* arm_UZP1 Q1 Q11 Q28 16 *)
  0x4e7181e8;       (* arm_SMLAL2_VEC Q8 Q15 Q17 16 *)
  0x4e6a8208;       (* arm_SMLAL2_VEC Q8 Q16 Q10 16 *)
  0x4e4519d4;       (* arm_UZP1 Q20 Q14 Q5 16 *)
  0x3cc204fb;       (* arm_LDR Q27 X7 (Postimmediate_Offset (word 32)) *)
  0x4cdf74c9;       (* arm_LDR Q9 X6 (Postimmediate_Offset (word 16)) *)
  0x4e575b46;       (* arm_UZP2 Q6 Q26 Q23 16 *)
  0x0e74c03a;       (* arm_SMULL_VEC Q26 Q1 Q20 16 *)
  0x4e561878;       (* arm_UZP1 Q24 Q3 Q22 16 *)
  0x4e74c037;       (* arm_SMULL2_VEC Q23 Q1 Q20 16 *)
  0x0e7983da;       (* arm_SMLAL_VEC Q26 Q30 Q25 16 *)
  0x4e481a5f;       (* arm_UZP1 Q31 Q18 Q8 16 *)
  0x0e78827a;       (* arm_SMLAL_VEC Q26 Q19 Q24 16 *)
  0x4e565864;       (* arm_UZP2 Q4 Q3 Q22 16 *)
  0x4e4d5ab6;       (* arm_UZP2 Q22 Q21 Q13 16 *)
  0x4e629feb;       (* arm_MUL_VEC Q11 Q31 Q2 16 128 *)
  0x4e4c1b6f;       (* arm_UZP1 Q15 Q27 Q12 16 *)
  0x4e7983d7;       (* arm_SMLAL2_VEC Q23 Q30 Q25 16 *)
  0x4e4c5b70;       (* arm_UZP2 Q16 Q27 Q12 16 *)
  0x0e6982da;       (* arm_SMLAL_VEC Q26 Q22 Q9 16 *)
  0x4e5d18ea;       (* arm_UZP1 Q10 Q7 Q29 16 *)
  0x4cdf753f;       (* arm_LDR Q31 X9 (Postimmediate_Offset (word 16)) *)
  0x4e788277;       (* arm_SMLAL2_VEC Q23 Q19 Q24 16 *)
  0x4e608168;       (* arm_SMLAL2_VEC Q8 Q11 Q0 16 *)
  0x4e4559cd;       (* arm_UZP2 Q13 Q14 Q5 16 *)
  0x0e608172;       (* arm_SMLAL_VEC Q18 Q11 Q0 16 *)
  0x3dc0043c;       (* arm_LDR Q28 X1 (Immediate_Offset (word 16)) *)
  0x4e6982d7;       (* arm_SMLAL2_VEC Q23 Q22 Q9 16 *)
  0x4e5d58f1;       (* arm_UZP2 Q17 Q7 Q29 16 *)
  0x4cdf7479;       (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  0x0e6a81fa;       (* arm_SMLAL_VEC Q26 Q15 Q10 16 *)
  0x4e6a81f7;       (* arm_SMLAL2_VEC Q23 Q15 Q10 16 *)
  0x3cc20495;       (* arm_LDR Q21 X4 (Postimmediate_Offset (word 32)) *)
  0x4e485a5d;       (* arm_UZP2 Q29 Q18 Q8 16 *)
  0x0e7f821a;       (* arm_SMLAL_VEC Q26 Q16 Q31 16 *)
  0x4e7f8217;       (* arm_SMLAL2_VEC Q23 Q16 Q31 16 *)
  0x3dc004ec;       (* arm_LDR Q12 X7 (Immediate_Offset (word 16)) *)
  0x0e6dc032;       (* arm_SMULL_VEC Q18 Q1 Q13 16 *)
  0x4e5d38c8;       (* arm_ZIP1 Q8 Q6 Q29 16 128 *)
  0x4e5d78c9;       (* arm_ZIP2 Q9 Q6 Q29 16 128 *)
  0x0e7483d2;       (* arm_SMLAL_VEC Q18 Q30 Q20 16 *)
  0x3c820408;       (* arm_STR Q8 X0 (Postimmediate_Offset (word 32)) *)
  0x0e648272;       (* arm_SMLAL_VEC Q18 Q19 Q4 16 *)
  0x3c9f0009;       (* arm_STR Q9 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e7882d2;       (* arm_SMLAL_VEC Q18 Q22 Q24 16 *)
  0x4e571b5d;       (* arm_UZP1 Q29 Q26 Q23 16 *)
  0x0e7181f2;       (* arm_SMLAL_VEC Q18 Q15 Q17 16 *)
  0xf10005ad;       (* arm_SUBS X13 X13 (rvalue (word 1)) *)
  0xb5fff7cd;       (* arm_CBNZ X13 (word 2096888) *)
  0x3cc204ff;       (* arm_LDR Q31 X7 (Postimmediate_Offset (word 32)) *)
  0x4e6dc028;       (* arm_SMULL2_VEC Q8 Q1 Q13 16 *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x4e7483c8;       (* arm_SMLAL2_VEC Q8 Q30 Q20 16 *)
  0x4e648268;       (* arm_SMLAL2_VEC Q8 Q19 Q4 16 *)
  0x3cc20449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 32)) *)
  0x4e7882c8;       (* arm_SMLAL2_VEC Q8 Q22 Q24 16 *)
  0x3cdf0047;       (* arm_LDR Q7 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7181e8;       (* arm_SMLAL2_VEC Q8 Q15 Q17 16 *)
  0x4cdf74ce;       (* arm_LDR Q14 X6 (Postimmediate_Offset (word 16)) *)
  0x0e6a8212;       (* arm_SMLAL_VEC Q18 Q16 Q10 16 *)
  0x4e5c1963;       (* arm_UZP1 Q3 Q11 Q28 16 *)
  0x4e5c5978;       (* arm_UZP2 Q24 Q11 Q28 16 *)
  0x4e629fa1;       (* arm_MUL_VEC Q1 Q29 Q2 16 128 *)
  0x4e47592d;       (* arm_UZP2 Q13 Q9 Q7 16 *)
  0x3cc204a4;       (* arm_LDR Q4 X5 (Postimmediate_Offset (word 32)) *)
  0x4e47193b;       (* arm_UZP1 Q27 Q9 Q7 16 *)
  0x4e6a8208;       (* arm_SMLAL2_VEC Q8 Q16 Q10 16 *)
  0x3cdf00a9;       (* arm_LDR Q9 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e6dc07e;       (* arm_SMULL2_VEC Q30 Q3 Q13 16 *)
  0x0e6dc074;       (* arm_SMULL_VEC Q20 Q3 Q13 16 *)
  0x3cdf008d;       (* arm_LDR Q13 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7bc071;       (* arm_SMULL2_VEC Q17 Q3 Q27 16 *)
  0x3dc00510;       (* arm_LDR Q16 X8 (Immediate_Offset (word 16)) *)
  0x4e798311;       (* arm_SMLAL2_VEC Q17 Q24 Q25 16 *)
  0x0e7b8314;       (* arm_SMLAL_VEC Q20 Q24 Q27 16 *)
  0x4e49588f;       (* arm_UZP2 Q15 Q4 Q9 16 *)
  0x0e7bc06b;       (* arm_SMULL_VEC Q11 Q3 Q27 16 *)
  0x4e491883;       (* arm_UZP1 Q3 Q4 Q9 16 *)
  0x0e79830b;       (* arm_SMLAL_VEC Q11 Q24 Q25 16 *)
  0x4e4d1aa6;       (* arm_UZP1 Q6 Q21 Q13 16 *)
  0x4e7b831e;       (* arm_SMLAL2_VEC Q30 Q24 Q27 16 *)
  0x4e4d5aad;       (* arm_UZP2 Q13 Q21 Q13 16 *)
  0x4e6380d1;       (* arm_SMLAL2_VEC Q17 Q6 Q3 16 *)
  0x3cc20507;       (* arm_LDR Q7 X8 (Postimmediate_Offset (word 32)) *)
  0x4e6f80de;       (* arm_SMLAL2_VEC Q30 Q6 Q15 16 *)
  0x4cdf7539;       (* arm_LDR Q25 X9 (Postimmediate_Offset (word 16)) *)
  0x0e6f80d4;       (* arm_SMLAL_VEC Q20 Q6 Q15 16 *)
  0x4e481a4f;       (* arm_UZP1 Q15 Q18 Q8 16 *)
  0x4e6381be;       (* arm_SMLAL2_VEC Q30 Q13 Q3 16 *)
  0x4e4c1be4;       (* arm_UZP1 Q4 Q31 Q12 16 *)
  0x0e6380cb;       (* arm_SMLAL_VEC Q11 Q6 Q3 16 *)
  0x4e5018f3;       (* arm_UZP1 Q19 Q7 Q16 16 *)
  0x0e6381b4;       (* arm_SMLAL_VEC Q20 Q13 Q3 16 *)
  0x4e4c5bfb;       (* arm_UZP2 Q27 Q31 Q12 16 *)
  0x4e5058f6;       (* arm_UZP2 Q22 Q7 Q16 16 *)
  0x4e6e81b1;       (* arm_SMLAL2_VEC Q17 Q13 Q14 16 *)
  0x4e738091;       (* arm_SMLAL2_VEC Q17 Q4 Q19 16 *)
  0x4e76809e;       (* arm_SMLAL2_VEC Q30 Q4 Q22 16 *)
  0x0e768094;       (* arm_SMLAL_VEC Q20 Q4 Q22 16 *)
  0x0e6e81ab;       (* arm_SMLAL_VEC Q11 Q13 Q14 16 *)
  0x4e629df6;       (* arm_MUL_VEC Q22 Q15 Q2 16 128 *)
  0x4e73837e;       (* arm_SMLAL2_VEC Q30 Q27 Q19 16 *)
  0x0e738374;       (* arm_SMLAL_VEC Q20 Q27 Q19 16 *)
  0x0e73808b;       (* arm_SMLAL_VEC Q11 Q4 Q19 16 *)
  0x0e79836b;       (* arm_SMLAL_VEC Q11 Q27 Q25 16 *)
  0x4e798371;       (* arm_SMLAL2_VEC Q17 Q27 Q25 16 *)
  0x0e6082d2;       (* arm_SMLAL_VEC Q18 Q22 Q0 16 *)
  0x4e5e1a87;       (* arm_UZP1 Q7 Q20 Q30 16 *)
  0x4e6082c8;       (* arm_SMLAL2_VEC Q8 Q22 Q0 16 *)
  0x4e629ce3;       (* arm_MUL_VEC Q3 Q7 Q2 16 128 *)
  0x4e51196c;       (* arm_UZP1 Q12 Q11 Q17 16 *)
  0x0e60803a;       (* arm_SMLAL_VEC Q26 Q1 Q0 16 *)
  0x4e485a4f;       (* arm_UZP2 Q15 Q18 Q8 16 *)
  0x4e629d93;       (* arm_MUL_VEC Q19 Q12 Q2 16 128 *)
  0x0e608074;       (* arm_SMLAL_VEC Q20 Q3 Q0 16 *)
  0x4e60807e;       (* arm_SMLAL2_VEC Q30 Q3 Q0 16 *)
  0x4e608037;       (* arm_SMLAL2_VEC Q23 Q1 Q0 16 *)
  0x4e608271;       (* arm_SMLAL2_VEC Q17 Q19 Q0 16 *)
  0x0e60826b;       (* arm_SMLAL_VEC Q11 Q19 Q0 16 *)
  0x4e5e5a88;       (* arm_UZP2 Q8 Q20 Q30 16 *)
  0x4e575b44;       (* arm_UZP2 Q4 Q26 Q23 16 *)
  0x4e51596d;       (* arm_UZP2 Q13 Q11 Q17 16 *)
  0x4e4f789a;       (* arm_ZIP2 Q26 Q4 Q15 16 128 *)
  0x4e4f388e;       (* arm_ZIP1 Q14 Q4 Q15 16 128 *)
  0x4e4839b7;       (* arm_ZIP1 Q23 Q13 Q8 16 128 *)
  0x4e4879ad;       (* arm_ZIP2 Q13 Q13 Q8 16 128 *)
  0x3d80041a;       (* arm_STR Q26 X0 (Immediate_Offset (word 16)) *)
  0x3c82040e;       (* arm_STR Q14 X0 (Postimmediate_Offset (word 32)) *)
  0x3c820417;       (* arm_STR Q23 X0 (Postimmediate_Offset (word 32)) *)
  0x3c9f000d;       (* arm_STR Q13 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

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
