(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o";;
 ****)

let poly_basemul_acc_montgomery_cached_k4_mc = define_assert_from_elf
  "poly_basemul_acc_montgomery_cached_k4_mc" "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o"
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
  0x9118002a;       (* arm_ADD X10 X1 (rvalue (word 1536)) *)
  0x9118004b;       (* arm_ADD X11 X2 (rvalue (word 1536)) *)
  0x910c006c;       (* arm_ADD X12 X3 (rvalue (word 768)) *)
  0xd280020d;       (* arm_MOV X13 (rvalue (word 16)) *)
  0x3dc0042a;       (* arm_LDR Q10 X1 (Immediate_Offset (word 16)) *)
  0x3cc2043a;       (* arm_LDR Q26 X1 (Postimmediate_Offset (word 32)) *)
  0x3dc0044d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 16)) *)
  0x3cc2048b;       (* arm_LDR Q11 X4 (Postimmediate_Offset (word 32)) *)
  0x3cc2044c;       (* arm_LDR Q12 X2 (Postimmediate_Offset (word 32)) *)
  0x4cdf74c6;       (* arm_LDR Q6 X6 (Postimmediate_Offset (word 16)) *)
  0x3cdf0083;       (* arm_LDR Q3 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc2051f;       (* arm_LDR Q31 X8 (Postimmediate_Offset (word 32)) *)
  0x4cdf7475;       (* arm_LDR Q21 X3 (Postimmediate_Offset (word 16)) *)
  0x4e4a5b41;       (* arm_UZP2 Q1 Q26 Q10 16 *)
  0x4e4a1b59;       (* arm_UZP1 Q25 Q26 Q10 16 *)
  0x3cc204be;       (* arm_LDR Q30 X5 (Postimmediate_Offset (word 32)) *)
  0x3cdf00bb;       (* arm_LDR Q27 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4d1985;       (* arm_UZP1 Q5 Q12 Q13 16 *)
  0x4e431969;       (* arm_UZP1 Q9 Q11 Q3 16 *)
  0x3dc004f4;       (* arm_LDR Q20 X7 (Immediate_Offset (word 16)) *)
  0x3cc204ea;       (* arm_LDR Q10 X7 (Postimmediate_Offset (word 32)) *)
  0x4e65c331;       (* arm_SMULL2_VEC Q17 Q25 Q5 16 *)
  0x3cdf011d;       (* arm_LDR Q29 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e65c32e;       (* arm_SMULL_VEC Q14 Q25 Q5 16 *)
  0x4e5b1bdc;       (* arm_UZP1 Q28 Q30 Q27 16 *)
  0x0e75802e;       (* arm_SMLAL_VEC Q14 Q1 Q21 16 *)
  0x4e758031;       (* arm_SMLAL2_VEC Q17 Q1 Q21 16 *)
  0x4e435978;       (* arm_UZP2 Q24 Q11 Q3 16 *)
  0x0e7c812e;       (* arm_SMLAL_VEC Q14 Q9 Q28 16 *)
  0x4e541952;       (* arm_UZP1 Q18 Q10 Q20 16 *)
  0x4e5d1bfa;       (* arm_UZP1 Q26 Q31 Q29 16 *)
  0x4e7c8131;       (* arm_SMLAL2_VEC Q17 Q9 Q28 16 *)
  0x4e668311;       (* arm_SMLAL2_VEC Q17 Q24 Q6 16 *)
  0x4e545954;       (* arm_UZP2 Q20 Q10 Q20 16 *)
  0x0e66830e;       (* arm_SMLAL_VEC Q14 Q24 Q6 16 *)
  0x4e4d598d;       (* arm_UZP2 Q13 Q12 Q13 16 *)
  0x3cc20573;       (* arm_LDR Q19 X11 (Postimmediate_Offset (word 32)) *)
  0x0e7a824e;       (* arm_SMLAL_VEC Q14 Q18 Q26 16 *)
  0x4cdf7527;       (* arm_LDR Q7 X9 (Postimmediate_Offset (word 16)) *)
  0x0e6dc32b;       (* arm_SMULL_VEC Q11 Q25 Q13 16 *)
  0x3dc00543;       (* arm_LDR Q3 X10 (Immediate_Offset (word 16)) *)
  0x4e6dc32f;       (* arm_SMULL2_VEC Q15 Q25 Q13 16 *)
  0x0e65802b;       (* arm_SMLAL_VEC Q11 Q1 Q5 16 *)
  0x3cdf0175;       (* arm_LDR Q21 X11 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc2054c;       (* arm_LDR Q12 X10 (Postimmediate_Offset (word 32)) *)
  0x4e65802f;       (* arm_SMLAL2_VEC Q15 Q1 Q5 16 *)
  0x4e5b5bc4;       (* arm_UZP2 Q4 Q30 Q27 16 *)
  0x4e7a8251;       (* arm_SMLAL2_VEC Q17 Q18 Q26 16 *)
  0x4e5d5bfe;       (* arm_UZP2 Q30 Q31 Q29 16 *)
  0x0e67828e;       (* arm_SMLAL_VEC Q14 Q20 Q7 16 *)
  0x0e64812b;       (* arm_SMLAL_VEC Q11 Q9 Q4 16 *)
  0x4e551a77;       (* arm_UZP1 Q23 Q19 Q21 16 *)
  0x4cdf758d;       (* arm_LDR Q13 X12 (Postimmediate_Offset (word 16)) *)
  0x0e7c830b;       (* arm_SMLAL_VEC Q11 Q24 Q28 16 *)
  0x4e64812f;       (* arm_SMLAL2_VEC Q15 Q9 Q4 16 *)
  0x4e431999;       (* arm_UZP1 Q25 Q12 Q3 16 *)
  0x0e7e824b;       (* arm_SMLAL_VEC Q11 Q18 Q30 16 *)
  0x4e43598c;       (* arm_UZP2 Q12 Q12 Q3 16 *)
  0x3cc20450;       (* arm_LDR Q16 X2 (Postimmediate_Offset (word 32)) *)
  0x0e77832e;       (* arm_SMLAL_VEC Q14 Q25 Q23 16 *)
  0x3dc0042a;       (* arm_LDR Q10 X1 (Immediate_Offset (word 16)) *)
  0x0e6d818e;       (* arm_SMLAL_VEC Q14 Q12 Q13 16 *)
  0x3cdf0043;       (* arm_LDR Q3 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e678291;       (* arm_SMLAL2_VEC Q17 Q20 Q7 16 *)
  0x4e778331;       (* arm_SMLAL2_VEC Q17 Q25 Q23 16 *)
  0x3cc20421;       (* arm_LDR Q1 X1 (Postimmediate_Offset (word 32)) *)
  0x4e6d8191;       (* arm_SMLAL2_VEC Q17 Q12 Q13 16 *)
  0x4e555a75;       (* arm_UZP2 Q21 Q19 Q21 16 *)
  0x3cc20516;       (* arm_LDR Q22 X8 (Postimmediate_Offset (word 32)) *)
  0x0e7a828b;       (* arm_SMLAL_VEC Q11 Q20 Q26 16 *)
  0x0e75832b;       (* arm_SMLAL_VEC Q11 Q25 Q21 16 *)
  0x4e435a1b;       (* arm_UZP2 Q27 Q16 Q3 16 *)
  0x0e77818b;       (* arm_SMLAL_VEC Q11 Q12 Q23 16 *)
  0x3cc2048d;       (* arm_LDR Q13 X4 (Postimmediate_Offset (word 32)) *)
  0x4e7c830f;       (* arm_SMLAL2_VEC Q15 Q24 Q28 16 *)
  0x4e5119df;       (* arm_UZP1 Q31 Q14 Q17 16 *)
  0x4e7e824f;       (* arm_SMLAL2_VEC Q15 Q18 Q30 16 *)
  0x4e431a10;       (* arm_UZP1 Q16 Q16 Q3 16 *)
  0x4e4a1833;       (* arm_UZP1 Q19 Q1 Q10 16 *)
  0x4e629fe7;       (* arm_MUL_VEC Q7 Q31 Q2 16 128 *)
  0x4e4a5824;       (* arm_UZP2 Q4 Q1 Q10 16 *)
  0x3cdf009f;       (* arm_LDR Q31 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204bd;       (* arm_LDR Q29 X5 (Postimmediate_Offset (word 32)) *)
  0x4e7bc268;       (* arm_SMULL2_VEC Q8 Q19 Q27 16 *)
  0x4cdf7465;       (* arm_LDR Q5 X3 (Postimmediate_Offset (word 16)) *)
  0x4e708088;       (* arm_SMLAL2_VEC Q8 Q4 Q16 16 *)
  0x4cdf7589;       (* arm_LDR Q9 X12 (Postimmediate_Offset (word 16)) *)
  0x4e7a828f;       (* arm_SMLAL2_VEC Q15 Q20 Q26 16 *)
  0x3cdf00b8;       (* arm_LDR Q24 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e6080ee;       (* arm_SMLAL_VEC Q14 Q7 Q0 16 *)
  0x4e5f19a1;       (* arm_UZP1 Q1 Q13 Q31 16 *)
  0x4e6080f1;       (* arm_SMLAL2_VEC Q17 Q7 Q0 16 *)
  0x4cdf74de;       (* arm_LDR Q30 X6 (Postimmediate_Offset (word 16)) *)
  0x4e75832f;       (* arm_SMLAL2_VEC Q15 Q25 Q21 16 *)
  0x3dc004e6;       (* arm_LDR Q6 X7 (Immediate_Offset (word 16)) *)
  0x4e77818f;       (* arm_SMLAL2_VEC Q15 Q12 Q23 16 *)
  0x3cc204e7;       (* arm_LDR Q7 X7 (Postimmediate_Offset (word 32)) *)
  0x0e7bc272;       (* arm_SMULL_VEC Q18 Q19 Q27 16 *)
  0x3cdf0115;       (* arm_LDR Q21 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e70c27a;       (* arm_SMULL_VEC Q26 Q19 Q16 16 *)
  0x4e70c277;       (* arm_SMULL2_VEC Q23 Q19 Q16 16 *)
  0x4e581baa;       (* arm_UZP1 Q10 Q29 Q24 16 *)
  0x4e4f197c;       (* arm_UZP1 Q28 Q11 Q15 16 *)
  0x0e65809a;       (* arm_SMLAL_VEC Q26 Q4 Q5 16 *)
  0x4e5159d3;       (* arm_UZP2 Q19 Q14 Q17 16 *)
  0x0e6a803a;       (* arm_SMLAL_VEC Q26 Q1 Q10 16 *)
  0x4e5f59b9;       (* arm_UZP2 Q25 Q13 Q31 16 *)
  0x4e629f8d;       (* arm_MUL_VEC Q13 Q28 Q2 16 128 *)
  0x4e4618ff;       (* arm_UZP1 Q31 Q7 Q6 16 *)
  0x3dc00554;       (* arm_LDR Q20 X10 (Immediate_Offset (word 16)) *)
  0x4e658097;       (* arm_SMLAL2_VEC Q23 Q4 Q5 16 *)
  0x4e551adc;       (* arm_UZP1 Q28 Q22 Q21 16 *)
  0x3dc0056c;       (* arm_LDR Q12 X11 (Immediate_Offset (word 16)) *)
  0x0e7e833a;       (* arm_SMLAL_VEC Q26 Q25 Q30 16 *)
  0x3cc2056e;       (* arm_LDR Q14 X11 (Postimmediate_Offset (word 32)) *)
  0x0e7c83fa;       (* arm_SMLAL_VEC Q26 Q31 Q28 16 *)
  0x4cdf7523;       (* arm_LDR Q3 X9 (Postimmediate_Offset (word 16)) *)
  0x0e6081ab;       (* arm_SMLAL_VEC Q11 Q13 Q0 16 *)
  0x3cc20545;       (* arm_LDR Q5 X10 (Postimmediate_Offset (word 32)) *)
  0x4e6081af;       (* arm_SMLAL2_VEC Q15 Q13 Q0 16 *)
  0x4e4658e7;       (* arm_UZP2 Q7 Q7 Q6 16 *)
  0x4e6a8037;       (* arm_SMLAL2_VEC Q23 Q1 Q10 16 *)
  0x4e4c19cd;       (* arm_UZP1 Q13 Q14 Q12 16 *)
  0x4e7e8337;       (* arm_SMLAL2_VEC Q23 Q25 Q30 16 *)
  0x0e6380fa;       (* arm_SMLAL_VEC Q26 Q7 Q3 16 *)
  0x4e555ad1;       (* arm_UZP2 Q17 Q22 Q21 16 *)
  0x4e7c83f7;       (* arm_SMLAL2_VEC Q23 Q31 Q28 16 *)
  0x4e585bbe;       (* arm_UZP2 Q30 Q29 Q24 16 *)
  0x4e5458bd;       (* arm_UZP2 Q29 Q5 Q20 16 *)
  0x0e708092;       (* arm_SMLAL_VEC Q18 Q4 Q16 16 *)
  0x4e5418b5;       (* arm_UZP1 Q21 Q5 Q20 16 *)
  0x0e7e8032;       (* arm_SMLAL_VEC Q18 Q1 Q30 16 *)
  0x4e6380f7;       (* arm_SMLAL2_VEC Q23 Q7 Q3 16 *)
  0x4e4f597b;       (* arm_UZP2 Q27 Q11 Q15 16 *)
  0x4e4c59cf;       (* arm_UZP2 Q15 Q14 Q12 16 *)
  0x0e6d82ba;       (* arm_SMLAL_VEC Q26 Q21 Q13 16 *)
  0x4e5b7a66;       (* arm_ZIP2 Q6 Q19 Q27 16 128 *)
  0x0e6a8332;       (* arm_SMLAL_VEC Q18 Q25 Q10 16 *)
  0x4e5b3a70;       (* arm_ZIP1 Q16 Q19 Q27 16 128 *)
  0x0e6983ba;       (* arm_SMLAL_VEC Q26 Q29 Q9 16 *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x4e6d82b7;       (* arm_SMLAL2_VEC Q23 Q21 Q13 16 *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x4e6983b7;       (* arm_SMLAL2_VEC Q23 Q29 Q9 16 *)
  0x3cc20498;       (* arm_LDR Q24 X4 (Postimmediate_Offset (word 32)) *)
  0x0e7183f2;       (* arm_SMLAL_VEC Q18 Q31 Q17 16 *)
  0x3cdf0036;       (* arm_LDR Q22 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc004fb;       (* arm_LDR Q27 X7 (Immediate_Offset (word 16)) *)
  0x0e7c80f2;       (* arm_SMLAL_VEC Q18 Q7 Q28 16 *)
  0x3cc2044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 32)) *)
  0x0e6f82b2;       (* arm_SMLAL_VEC Q18 Q21 Q15 16 *)
  0x0e6d83b2;       (* arm_SMLAL_VEC Q18 Q29 Q13 16 *)
  0x4e571b44;       (* arm_UZP1 Q4 Q26 Q23 16 *)
  0x4e7e8028;       (* arm_SMLAL2_VEC Q8 Q1 Q30 16 *)
  0x4e561973;       (* arm_UZP1 Q19 Q11 Q22 16 *)
  0x4e629c84;       (* arm_MUL_VEC Q4 Q4 Q2 16 128 *)
  0x4e565965;       (* arm_UZP2 Q5 Q11 Q22 16 *)
  0x3cdf008b;       (* arm_LDR Q11 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204a3;       (* arm_LDR Q3 X5 (Postimmediate_Offset (word 32)) *)
  0x4e6a8328;       (* arm_SMLAL2_VEC Q8 Q25 Q10 16 *)
  0x4cdf7476;       (* arm_LDR Q22 X3 (Postimmediate_Offset (word 16)) *)
  0x3cdf005e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7183e8;       (* arm_SMLAL2_VEC Q8 Q31 Q17 16 *)
  0x4e7c80e8;       (* arm_SMLAL2_VEC Q8 Q7 Q28 16 *)
  0x3cdf00b1;       (* arm_LDR Q17 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e60809a;       (* arm_SMLAL_VEC Q26 Q4 Q0 16 *)
  0x4e4b1b01;       (* arm_UZP1 Q1 Q24 Q11 16 *)
  0x4e608097;       (* arm_SMLAL2_VEC Q23 Q4 Q0 16 *)
  0x4cdf74d4;       (* arm_LDR Q20 X6 (Postimmediate_Offset (word 16)) *)
  0x4e6f82a8;       (* arm_SMLAL2_VEC Q8 Q21 Q15 16 *)
  0x4e5e19cc;       (* arm_UZP1 Q12 Q14 Q30 16 *)
  0x4e6d83a8;       (* arm_SMLAL2_VEC Q8 Q29 Q13 16 *)
  0x3cc204ed;       (* arm_LDR Q13 X7 (Postimmediate_Offset (word 32)) *)
  0x3cc20509;       (* arm_LDR Q9 X8 (Postimmediate_Offset (word 32)) *)
  0x3cdf0115;       (* arm_LDR Q21 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e575b44;       (* arm_UZP2 Q4 Q26 Q23 16 *)
  0x0e6cc27a;       (* arm_SMULL_VEC Q26 Q19 Q12 16 *)
  0x4e6cc277;       (* arm_SMULL2_VEC Q23 Q19 Q12 16 *)
  0x4e51186a;       (* arm_UZP1 Q10 Q3 Q17 16 *)
  0x4e481a47;       (* arm_UZP1 Q7 Q18 Q8 16 *)
  0x0e7680ba;       (* arm_SMLAL_VEC Q26 Q5 Q22 16 *)
  0x4e4b5b19;       (* arm_UZP2 Q25 Q24 Q11 16 *)
  0x0e6a803a;       (* arm_SMLAL_VEC Q26 Q1 Q10 16 *)
  0x4e5b19bf;       (* arm_UZP1 Q31 Q13 Q27 16 *)
  0x4e629cfd;       (* arm_MUL_VEC Q29 Q7 Q2 16 128 *)
  0x3dc00558;       (* arm_LDR Q24 X10 (Immediate_Offset (word 16)) *)
  0x4e5e59ce;       (* arm_UZP2 Q14 Q14 Q30 16 *)
  0x4e7680b7;       (* arm_SMLAL2_VEC Q23 Q5 Q22 16 *)
  0x4e55193c;       (* arm_UZP1 Q28 Q9 Q21 16 *)
  0x0e74833a;       (* arm_SMLAL_VEC Q26 Q25 Q20 16 *)
  0x4e51587e;       (* arm_UZP2 Q30 Q3 Q17 16 *)
  0x3cc2054f;       (* arm_LDR Q15 X10 (Postimmediate_Offset (word 32)) *)
  0x0e7c83fa;       (* arm_SMLAL_VEC Q26 Q31 Q28 16 *)
  0x4cdf7523;       (* arm_LDR Q3 X9 (Postimmediate_Offset (word 16)) *)
  0x0e6083b2;       (* arm_SMLAL_VEC Q18 Q29 Q0 16 *)
  0x4e5b59a7;       (* arm_UZP2 Q7 Q13 Q27 16 *)
  0x4e6083a8;       (* arm_SMLAL2_VEC Q8 Q29 Q0 16 *)
  0x3cc2057b;       (* arm_LDR Q27 X11 (Postimmediate_Offset (word 32)) *)
  0x4e6a8037;       (* arm_SMLAL2_VEC Q23 Q1 Q10 16 *)
  0x4e555931;       (* arm_UZP2 Q17 Q9 Q21 16 *)
  0x4e748337;       (* arm_SMLAL2_VEC Q23 Q25 Q20 16 *)
  0x0e6380fa;       (* arm_SMLAL_VEC Q26 Q7 Q3 16 *)
  0x3cdf0174;       (* arm_LDR Q20 X11 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e485a4b;       (* arm_UZP2 Q11 Q18 Q8 16 *)
  0x4e6ec268;       (* arm_SMULL2_VEC Q8 Q19 Q14 16 *)
  0x3c820410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 32)) *)
  0x0e6ec272;       (* arm_SMULL_VEC Q18 Q19 Q14 16 *)
  0x4e5819f5;       (* arm_UZP1 Q21 Q15 Q24 16 *)
  0x0e6c80b2;       (* arm_SMLAL_VEC Q18 Q5 Q12 16 *)
  0x4e6c80a8;       (* arm_SMLAL2_VEC Q8 Q5 Q12 16 *)
  0x4e541b6d;       (* arm_UZP1 Q13 Q27 Q20 16 *)
  0x0e7e8032;       (* arm_SMLAL_VEC Q18 Q1 Q30 16 *)
  0x4cdf7589;       (* arm_LDR Q9 X12 (Postimmediate_Offset (word 16)) *)
  0x4e7c83f7;       (* arm_SMLAL2_VEC Q23 Q31 Q28 16 *)
  0x4e5859fd;       (* arm_UZP2 Q29 Q15 Q24 16 *)
  0x4e545b6f;       (* arm_UZP2 Q15 Q27 Q20 16 *)
  0x0e6d82ba;       (* arm_SMLAL_VEC Q26 Q21 Q13 16 *)
  0x0e6a8332;       (* arm_SMLAL_VEC Q18 Q25 Q10 16 *)
  0x3c9f0006;       (* arm_STR Q6 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4b3890;       (* arm_ZIP1 Q16 Q4 Q11 16 128 *)
  0x0e6983ba;       (* arm_SMLAL_VEC Q26 Q29 Q9 16 *)
  0x4e6380f7;       (* arm_SMLAL2_VEC Q23 Q7 Q3 16 *)
  0x4e4b7886;       (* arm_ZIP2 Q6 Q4 Q11 16 128 *)
  0xf10005ad;       (* arm_SUBS X13 X13 (rvalue (word 1)) *)
  0xb5fff5ad;       (* arm_CBNZ X13 (word 2096820) *)
  0x3d800406;       (* arm_STR Q6 X0 (Immediate_Offset (word 16)) *)
  0x4e6d82b7;       (* arm_SMLAL2_VEC Q23 Q21 Q13 16 *)
  0x4e7e8028;       (* arm_SMLAL2_VEC Q8 Q1 Q30 16 *)
  0x3c820410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 32)) *)
  0x4e6a8328;       (* arm_SMLAL2_VEC Q8 Q25 Q10 16 *)
  0x0e7183f2;       (* arm_SMLAL_VEC Q18 Q31 Q17 16 *)
  0x4e6983b7;       (* arm_SMLAL2_VEC Q23 Q29 Q9 16 *)
  0x4e7183e8;       (* arm_SMLAL2_VEC Q8 Q31 Q17 16 *)
  0x4e7c80e8;       (* arm_SMLAL2_VEC Q8 Q7 Q28 16 *)
  0x0e7c80f2;       (* arm_SMLAL_VEC Q18 Q7 Q28 16 *)
  0x0e6f82b2;       (* arm_SMLAL_VEC Q18 Q21 Q15 16 *)
  0x4e6f82a8;       (* arm_SMLAL2_VEC Q8 Q21 Q15 16 *)
  0x0e6d83b2;       (* arm_SMLAL_VEC Q18 Q29 Q13 16 *)
  0x4e6d83a8;       (* arm_SMLAL2_VEC Q8 Q29 Q13 16 *)
  0x4e571b4d;       (* arm_UZP1 Q13 Q26 Q23 16 *)
  0x4e629dad;       (* arm_MUL_VEC Q13 Q13 Q2 16 128 *)
  0x4e481a4a;       (* arm_UZP1 Q10 Q18 Q8 16 *)
  0x4e629d4a;       (* arm_MUL_VEC Q10 Q10 Q2 16 128 *)
  0x0e6081ba;       (* arm_SMLAL_VEC Q26 Q13 Q0 16 *)
  0x4e6081b7;       (* arm_SMLAL2_VEC Q23 Q13 Q0 16 *)
  0x0e608152;       (* arm_SMLAL_VEC Q18 Q10 Q0 16 *)
  0x4e608148;       (* arm_SMLAL2_VEC Q8 Q10 Q0 16 *)
  0x4e575b55;       (* arm_UZP2 Q21 Q26 Q23 16 *)
  0x4e485a4d;       (* arm_UZP2 Q13 Q18 Q8 16 *)
  0x4e4d7ab4;       (* arm_ZIP2 Q20 Q21 Q13 16 128 *)
  0x4e4d3aad;       (* arm_ZIP1 Q13 Q21 Q13 16 128 *)
  0x3c82040d;       (* arm_STR Q13 X0 (Postimmediate_Offset (word 32)) *)
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

let pmull_acc4 = define
  `pmull_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int)
              (x30: int) (x31 : int) (y30 : int) (y31 : int) =
              pmull x30 x31 y30 y31 + pmull x20 x21 y20 y21 + pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc4 = define
  `pmul_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int)
             (x30: int) (x31 : int) (y30 : int) (y31 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc4 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21 x30 x31 y30 y31) rem &3329`;;

let basemul4_even = define
 `basemul4_even x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t = \i.
    pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)
              (x3 (2 * i)) (x3 (2 * i + 1))
              (y3 (2 * i)) (y3t i)
 `;;

let basemul4_odd = define
`basemul4_odd x0 y0 x1 y1 x2 y2 x3 y3 = \i.
  pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
            (y0 (2 * i + 1)) (y0 (2 * i))
            (x1 (2 * i)) (x1 (2 * i + 1))
            (y1 (2 * i + 1)) (y1 (2 * i))
            (x2 (2 * i)) (x2 (2 * i + 1))
            (y2 (2 * i + 1)) (y2 (2 * i))
            (x3 (2 * i)) (x3 (2 * i + 1))
            (y3 (2 * i + 1)) (y3 (2 * i))
`;;

  let poly_basemul_acc_montgomery_cached_k4_EXEC = ARM_MK_EXEC_RULE poly_basemul_acc_montgomery_cached_k4_mc;;


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

  let poly_basemul_acc_montgomery_cached_k4_GOAL = `forall srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc.
       ALL (nonoverlapping (dst, 512))
           [(word pc, LENGTH poly_basemul_acc_montgomery_cached_k4_mc); (srcA, 2048); (srcB, 2048); (srcBt, 1024)]
       ==>
       ensures arm
         (\s. aligned_bytes_loaded s (word pc) poly_basemul_acc_montgomery_cached_k4_mc /\
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
              (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (512  + 2 * i)))) s = y2t i) /\
              (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (1536 + 2 * i)))) s = x3 i)  /\
              (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (1536 + 2 * i)))) s = y3 i)  /\
              (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (768  + 2 * i)))) s = y3t i)
         )
         (\s. read PC s = word (pc + 1072) /\
             ((!i. i < 256 ==> abs(ival(x0 i)) <= &2 pow 12 /\ abs(ival(x1 i)) <= &2 pow 12
                                                            /\ abs(ival(x2 i)) <= &2 pow 12
                                                            /\ abs(ival(x3 i)) <= &2 pow 12)
               ==>
               (!i. i < 128 ==> (ival(read(memory :> bytes16(word_add dst (word (4 * i)))) s) ==
                                   basemul4_even (ival o x0) (ival o y0) (ival o y0t)
                                                 (ival o x1) (ival o y1) (ival o y1t)
                                                 (ival o x2) (ival o y2) (ival o y2t)
                                                 (ival o x3) (ival o y3) (ival o y3t) i) (mod &3329) /\
                              (ival(read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s) ==
                                   basemul4_odd (ival o x0) (ival o y0)
                                                (ival o x1) (ival o y1)
                                                (ival o x2) (ival o y2)
                                                (ival o x3) (ival o y3) i) (mod &3329))))
         // Register and memory footprint
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
          MAYCHANGE [memory :> bytes(dst, 512)])
     `;;

   (* ------------------------------------------------------------------------- *)
   (* Proof                                                                     *)
   (* ------------------------------------------------------------------------- *)

  let poly_basemul_acc_montgomery_cached_k4_SPEC = prove(poly_basemul_acc_montgomery_cached_k4_GOAL,
        REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
         MODIFIABLE_SIMD_REGS;
         NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst poly_basemul_acc_montgomery_cached_k4_EXEC] THEN
       REPEAT STRIP_TAC THEN

       (* Split quantified assumptions into separate cases *)
       CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
       CONV_TAC((ONCE_DEPTH_CONV NUM_MULT_CONV) THENC (ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN

       (* Initialize symbolic execution *)
       ENSURES_INIT_TAC "s0" THEN

       (* Rewrite memory-read assumptions from 16-bit granularity
        * to 128-bit granularity. *)
       MEMORY_128_FROM_16_TAC "srcA" 128 THEN
       MEMORY_128_FROM_16_TAC "srcB" 128 THEN
       MEMORY_128_FROM_16_TAC "srcBt" 64 THEN
       ASM_REWRITE_TAC [WORD_ADD_0] THEN
       (* Forget original shape of assumption *)
       DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcA) s = x`] THEN
       DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcB) s = x`] THEN
       DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcBt) s = x`] THEN

       (* Symbolic execution
          Note that we simplify eagerly after every step.
          This reduces the proof time *)
       REPEAT STRIP_TAC THEN
       MAP_EVERY (fun n -> ARM_STEPS_TAC poly_basemul_acc_montgomery_cached_k4_EXEC [n] THEN
                  (SIMD_SIMPLIFY_TAC [montred])) (1--1355) THEN

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
      DISCARD_STATE_TAC "s1355" THEN

     (* Split into one congruence goals per index. *)
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[basemul4_even; basemul4_odd;
                 pmul_acc4; pmull_acc4; pmull; o_THM] THEN
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
  let poly_basemul_acc_montgomery_cached_k4_SPEC' = prove(
     `forall srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc returnaddress stackpointer.
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping
          [(dst, 512); (word_sub stackpointer (word 64),64)]
          [(word pc, LENGTH poly_basemul_acc_montgomery_cached_k4_mc); (srcA, 2048); (srcB, 2048); (srcBt, 1024)] /\
        nonoverlapping (dst,512) (word_sub stackpointer (word 64),64)
        ==>
        ensures arm
        (\s. // Assert that poly_basemul_acc_montgomery_cached_k4 is loaded at PC
          aligned_bytes_loaded s (word pc) poly_basemul_acc_montgomery_cached_k4_mc /\
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
          (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (512  + 2 * i)))) s = y2t i) /\
          (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (1536 + 2 * i)))) s = x3 i)  /\
          (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (1536 + 2 * i)))) s = y3 i)  /\
          (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (768  + 2 * i)))) s = y3t i)
        )
        (\s. read PC s = returnaddress /\
             ((!i. i < 256 ==> abs(ival(x0 i)) <= &2 pow 12 /\ abs(ival(x1 i)) <= &2 pow 12
                                                            /\ abs(ival(x2 i)) <= &2 pow 12
                                                            /\ abs(ival(x3 i)) <= &2 pow 12)
               ==>
               (!i. i < 128 ==> (ival(read(memory :> bytes16(word_add dst (word (4 * i)))) s) ==
                                   basemul4_even (ival o x0) (ival o y0) (ival o y0t)
                                                 (ival o x1) (ival o y1) (ival o y1t)
                                                 (ival o x2) (ival o y2) (ival o y2t)
                                                 (ival o x3) (ival o y3) (ival o y3t) i) (mod &3329) /\
                              (ival(read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s) ==
                                   basemul4_odd (ival o x0) (ival o y0)
                                                (ival o x1) (ival o y1)
                                                (ival o x2) (ival o y2)
                                                (ival o x3) (ival o y3) i) (mod &3329)))
        )
        // Register and memory footprint
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(word_sub stackpointer (word 64),64)])`,
    REWRITE_TAC[fst poly_basemul_acc_montgomery_cached_k4_EXEC] THEN
    CONV_TAC TWEAK_CONV THEN
    ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) poly_basemul_acc_montgomery_cached_k4_EXEC
       (REWRITE_RULE[fst poly_basemul_acc_montgomery_cached_k4_EXEC] (CONV_RULE TWEAK_CONV poly_basemul_acc_montgomery_cached_k4_SPEC))
        `[D8; D9; D10; D11; D12; D13; D14; D15]` 64  THEN
     WORD_ARITH_TAC)
  ;;
