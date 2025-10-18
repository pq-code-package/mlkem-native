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
  0x3cc2043c;       (* arm_LDR Q28 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0025;       (* arm_LDR Q5 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc2045f;       (* arm_LDR Q31 X2 (Postimmediate_Offset (word 32)) *)
  0x3cdf005b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204a7;       (* arm_LDR Q7 X5 (Postimmediate_Offset (word 32)) *)
  0x3cc2048a;       (* arm_LDR Q10 X4 (Postimmediate_Offset (word 32)) *)
  0x3cdf00b2;       (* arm_LDR Q18 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cdf0089;       (* arm_LDR Q9 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e451b8b;       (* arm_UZP1 Q11 Q28 Q5 16 *)
  0x4e455b93;       (* arm_UZP2 Q19 Q28 Q5 16 *)
  0x4e5b5be4;       (* arm_UZP2 Q4 Q31 Q27 16 *)
  0x4e5b1be1;       (* arm_UZP1 Q1 Q31 Q27 16 *)
  0x3cc204fd;       (* arm_LDR Q29 X7 (Postimmediate_Offset (word 32)) *)
  0x3dc0051c;       (* arm_LDR Q28 X8 (Immediate_Offset (word 16)) *)
  0x4e491958;       (* arm_UZP1 Q24 Q10 Q9 16 *)
  0x4e5218f1;       (* arm_UZP1 Q17 Q7 Q18 16 *)
  0x4e5258e7;       (* arm_UZP2 Q7 Q7 Q18 16 *)
  0x3cc20515;       (* arm_LDR Q21 X8 (Postimmediate_Offset (word 32)) *)
  0x4e49595b;       (* arm_UZP2 Q27 Q10 Q9 16 *)
  0x3cdf00e6;       (* arm_LDR Q6 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e64c172;       (* arm_SMULL_VEC Q18 Q11 Q4 16 *)
  0x4cdf7469;       (* arm_LDR Q9 X3 (Postimmediate_Offset (word 16)) *)
  0x4e64c168;       (* arm_SMULL2_VEC Q8 Q11 Q4 16 *)
  0x3cc20570;       (* arm_LDR Q16 X11 (Postimmediate_Offset (word 32)) *)
  0x4e618268;       (* arm_SMLAL2_VEC Q8 Q19 Q1 16 *)
  0x3cdf016e;       (* arm_LDR Q14 X11 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e618272;       (* arm_SMLAL_VEC Q18 Q19 Q1 16 *)
  0x4e5c1aaa;       (* arm_UZP1 Q10 Q21 Q28 16 *)
  0x0e678312;       (* arm_SMLAL_VEC Q18 Q24 Q7 16 *)
  0x3cc20544;       (* arm_LDR Q4 X10 (Postimmediate_Offset (word 32)) *)
  0x4e678308;       (* arm_SMLAL2_VEC Q8 Q24 Q7 16 *)
  0x4cdf74cc;       (* arm_LDR Q12 X6 (Postimmediate_Offset (word 16)) *)
  0x4e61c177;       (* arm_SMULL2_VEC Q23 Q11 Q1 16 *)
  0x4e465bad;       (* arm_UZP2 Q13 Q29 Q6 16 *)
  0x0e61c17a;       (* arm_SMULL_VEC Q26 Q11 Q1 16 *)
  0x4e461bbd;       (* arm_UZP1 Q29 Q29 Q6 16 *)
  0x0e69827a;       (* arm_SMLAL_VEC Q26 Q19 Q9 16 *)
  0x3cdf014f;       (* arm_LDR Q15 X10 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e698277;       (* arm_SMLAL2_VEC Q23 Q19 Q9 16 *)
  0x4e5c5aa9;       (* arm_UZP2 Q9 Q21 Q28 16 *)
  0x0e718372;       (* arm_SMLAL_VEC Q18 Q27 Q17 16 *)
  0x4e4e5a06;       (* arm_UZP2 Q6 Q16 Q14 16 *)
  0x4e4e1a15;       (* arm_UZP1 Q21 Q16 Q14 16 *)
  0x4e718368;       (* arm_SMLAL2_VEC Q8 Q27 Q17 16 *)
  0x4e6983a8;       (* arm_SMLAL2_VEC Q8 Q29 Q9 16 *)
  0x4e4f189e;       (* arm_UZP1 Q30 Q4 Q15 16 *)
  0x4e4f5890;       (* arm_UZP2 Q16 Q4 Q15 16 *)
  0x0e6983b2;       (* arm_SMLAL_VEC Q18 Q29 Q9 16 *)
  0x4e6a81a8;       (* arm_SMLAL2_VEC Q8 Q13 Q10 16 *)
  0x4cdf752f;       (* arm_LDR Q15 X9 (Postimmediate_Offset (word 16)) *)
  0x0e6a81b2;       (* arm_SMLAL_VEC Q18 Q13 Q10 16 *)
  0x3cc2048b;       (* arm_LDR Q11 X4 (Postimmediate_Offset (word 32)) *)
  0x0e6683d2;       (* arm_SMLAL_VEC Q18 Q30 Q6 16 *)
  0x3cc20447;       (* arm_LDR Q7 X2 (Postimmediate_Offset (word 32)) *)
  0x4e6683c8;       (* arm_SMLAL2_VEC Q8 Q30 Q6 16 *)
  0x4cdf7589;       (* arm_LDR Q9 X12 (Postimmediate_Offset (word 16)) *)
  0x4e718317;       (* arm_SMLAL2_VEC Q23 Q24 Q17 16 *)
  0x3cdf0044;       (* arm_LDR Q4 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e71831a;       (* arm_SMLAL_VEC Q26 Q24 Q17 16 *)
  0x3cdf0099;       (* arm_LDR Q25 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e758208;       (* arm_SMLAL2_VEC Q8 Q16 Q21 16 *)
  0x3cc204a5;       (* arm_LDR Q5 X5 (Postimmediate_Offset (word 32)) *)
  0x0e758212;       (* arm_SMLAL_VEC Q18 Q16 Q21 16 *)
  0x3cdf00b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e6c837a;       (* arm_SMLAL_VEC Q26 Q27 Q12 16 *)
  0x3dc00433;       (* arm_LDR Q19 X1 (Immediate_Offset (word 16)) *)
  0x0e6a83ba;       (* arm_SMLAL_VEC Q26 Q29 Q10 16 *)
  0x4cdf7474;       (* arm_LDR Q20 X3 (Postimmediate_Offset (word 16)) *)
  0x0e6f81ba;       (* arm_SMLAL_VEC Q26 Q13 Q15 16 *)
  0x4e4418f8;       (* arm_UZP1 Q24 Q7 Q4 16 *)
  0x4e6c8377;       (* arm_SMLAL2_VEC Q23 Q27 Q12 16 *)
  0x4e481a5c;       (* arm_UZP1 Q28 Q18 Q8 16 *)
  0x0e7583da;       (* arm_SMLAL_VEC Q26 Q30 Q21 16 *)
  0x4e59597b;       (* arm_UZP2 Q27 Q11 Q25 16 *)
  0x4e6a83b7;       (* arm_SMLAL2_VEC Q23 Q29 Q10 16 *)
  0x4e4458ff;       (* arm_UZP2 Q31 Q7 Q4 16 *)
  0x4e6f81b7;       (* arm_SMLAL2_VEC Q23 Q13 Q15 16 *)
  0x4e5618ae;       (* arm_UZP1 Q14 Q5 Q22 16 *)
  0x4e591971;       (* arm_UZP1 Q17 Q11 Q25 16 *)
  0x0e69821a;       (* arm_SMLAL_VEC Q26 Q16 Q9 16 *)
  0x4e629f9d;       (* arm_MUL_VEC Q29 Q28 Q2 16 128 *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x4e7583d7;       (* arm_SMLAL2_VEC Q23 Q30 Q21 16 *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x4e5658af;       (* arm_UZP2 Q15 Q5 Q22 16 *)
  0x0e6083b2;       (* arm_SMLAL_VEC Q18 Q29 Q0 16 *)
  0x3cc204ec;       (* arm_LDR Q12 X7 (Postimmediate_Offset (word 32)) *)
  0x4e6083a8;       (* arm_SMLAL2_VEC Q8 Q29 Q0 16 *)
  0x3cdf00e3;       (* arm_LDR Q3 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20515;       (* arm_LDR Q21 X8 (Postimmediate_Offset (word 32)) *)
  0x4e53197d;       (* arm_UZP1 Q29 Q11 Q19 16 *)
  0x3cdf010d;       (* arm_LDR Q13 X8 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e535965;       (* arm_UZP2 Q5 Q11 Q19 16 *)
  0x4e698217;       (* arm_SMLAL2_VEC Q23 Q16 Q9 16 *)
  0x4e485a5c;       (* arm_UZP2 Q28 Q18 Q8 16 *)
  0x4e7fc3a8;       (* arm_SMULL2_VEC Q8 Q29 Q31 16 *)
  0x4e7880a8;       (* arm_SMLAL2_VEC Q8 Q5 Q24 16 *)
  0x4e431987;       (* arm_UZP1 Q7 Q12 Q3 16 *)
  0x4e6f8228;       (* arm_SMLAL2_VEC Q8 Q17 Q15 16 *)
  0x4e4d5aab;       (* arm_UZP2 Q11 Q21 Q13 16 *)
  0x4e571b44;       (* arm_UZP1 Q4 Q26 Q23 16 *)
  0x4e6e8368;       (* arm_SMLAL2_VEC Q8 Q27 Q14 16 *)
  0x4e6b80e8;       (* arm_SMLAL2_VEC Q8 Q7 Q11 16 *)
  0x4e629c86;       (* arm_MUL_VEC Q6 Q4 Q2 16 128 *)
  0x3cc20573;       (* arm_LDR Q19 X11 (Postimmediate_Offset (word 32)) *)
  0x4e435999;       (* arm_UZP2 Q25 Q12 Q3 16 *)
  0x3cc2054c;       (* arm_LDR Q12 X10 (Postimmediate_Offset (word 32)) *)
  0x0e7fc3b2;       (* arm_SMULL_VEC Q18 Q29 Q31 16 *)
  0x3cdf0143;       (* arm_LDR Q3 X10 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e7880b2;       (* arm_SMLAL_VEC Q18 Q5 Q24 16 *)
  0x4e4d1aa4;       (* arm_UZP1 Q4 Q21 Q13 16 *)
  0x0e6f8232;       (* arm_SMLAL_VEC Q18 Q17 Q15 16 *)
  0x3cdf016d;       (* arm_LDR Q13 X11 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf74c1;       (* arm_LDR Q1 X6 (Postimmediate_Offset (word 16)) *)
  0x0e6080da;       (* arm_SMLAL_VEC Q26 Q6 Q0 16 *)
  0x4e6080d7;       (* arm_SMLAL2_VEC Q23 Q6 Q0 16 *)
  0x4cdf752a;       (* arm_LDR Q10 X9 (Postimmediate_Offset (word 16)) *)
  0x0e6e8372;       (* arm_SMLAL_VEC Q18 Q27 Q14 16 *)
  0x4e43199e;       (* arm_UZP1 Q30 Q12 Q3 16 *)
  0x4e648328;       (* arm_SMLAL2_VEC Q8 Q25 Q4 16 *)
  0x4e4d5a7f;       (* arm_UZP2 Q31 Q19 Q13 16 *)
  0x0e6b80f2;       (* arm_SMLAL_VEC Q18 Q7 Q11 16 *)
  0x4cdf7589;       (* arm_LDR Q9 X12 (Postimmediate_Offset (word 16)) *)
  0x0e648332;       (* arm_SMLAL_VEC Q18 Q25 Q4 16 *)
  0x4e4d1a75;       (* arm_UZP1 Q21 Q19 Q13 16 *)
  0x4e435990;       (* arm_UZP2 Q16 Q12 Q3 16 *)
  0x0e7f83d2;       (* arm_SMLAL_VEC Q18 Q30 Q31 16 *)
  0x4e7f83c8;       (* arm_SMLAL2_VEC Q8 Q30 Q31 16 *)
  0x4e575b5f;       (* arm_UZP2 Q31 Q26 Q23 16 *)
  0x4e758208;       (* arm_SMLAL2_VEC Q8 Q16 Q21 16 *)
  0x0e758212;       (* arm_SMLAL_VEC Q18 Q16 Q21 16 *)
  0x4e5c3bef;       (* arm_ZIP1 Q15 Q31 Q28 16 128 *)
  0x3dc00433;       (* arm_LDR Q19 X1 (Immediate_Offset (word 16)) *)
  0x4e78c3b7;       (* arm_SMULL2_VEC Q23 Q29 Q24 16 *)
  0x0e78c3ba;       (* arm_SMULL_VEC Q26 Q29 Q24 16 *)
  0x3dc00443;       (* arm_LDR Q3 X2 (Immediate_Offset (word 16)) *)
  0x0e7480ba;       (* arm_SMLAL_VEC Q26 Q5 Q20 16 *)
  0x3cc2044b;       (* arm_LDR Q11 X2 (Postimmediate_Offset (word 32)) *)
  0x4e481a46;       (* arm_UZP1 Q6 Q18 Q8 16 *)
  0x0e6e823a;       (* arm_SMLAL_VEC Q26 Q17 Q14 16 *)
  0x0e61837a;       (* arm_SMLAL_VEC Q26 Q27 Q1 16 *)
  0x4e5c7bed;       (* arm_ZIP2 Q13 Q31 Q28 16 128 *)
  0x0e6480fa;       (* arm_SMLAL_VEC Q26 Q7 Q4 16 *)
  0x3c82040f;       (* arm_STR Q15 X0 (Postimmediate_Offset (word 32)) *)
  0x0e6a833a;       (* arm_SMLAL_VEC Q26 Q25 Q10 16 *)
  0x3c9f000d;       (* arm_STR Q13 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e629cdd;       (* arm_MUL_VEC Q29 Q6 Q2 16 128 *)
  0x4e431978;       (* arm_UZP1 Q24 Q11 Q3 16 *)
  0x4e43597f;       (* arm_UZP2 Q31 Q11 Q3 16 *)
  0x3cc2048b;       (* arm_LDR Q11 X4 (Postimmediate_Offset (word 32)) *)
  0x4e7480b7;       (* arm_SMLAL2_VEC Q23 Q5 Q20 16 *)
  0x3cdf009c;       (* arm_LDR Q28 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e6e8237;       (* arm_SMLAL2_VEC Q23 Q17 Q14 16 *)
  0x3cc204a5;       (* arm_LDR Q5 X5 (Postimmediate_Offset (word 32)) *)
  0x4e618377;       (* arm_SMLAL2_VEC Q23 Q27 Q1 16 *)
  0x3cdf00b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e7583da;       (* arm_SMLAL_VEC Q26 Q30 Q21 16 *)
  0x4cdf7474;       (* arm_LDR Q20 X3 (Postimmediate_Offset (word 16)) *)
  0x0e69821a;       (* arm_SMLAL_VEC Q26 Q16 Q9 16 *)
  0x4e5c1971;       (* arm_UZP1 Q17 Q11 Q28 16 *)
  0x4e6480f7;       (* arm_SMLAL2_VEC Q23 Q7 Q4 16 *)
  0x4e5c597b;       (* arm_UZP2 Q27 Q11 Q28 16 *)
  0x4e6a8337;       (* arm_SMLAL2_VEC Q23 Q25 Q10 16 *)
  0x4e5618ae;       (* arm_UZP1 Q14 Q5 Q22 16 *)
  0xf10005ad;       (* arm_SUBS X13 X13 (rvalue (word 1)) *)
  0xb5fff5ad;       (* arm_CBNZ X13 (word 2096820) *)
  0x0e6083b2;       (* arm_SMLAL_VEC Q18 Q29 Q0 16 *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x4e5658bc;       (* arm_UZP2 Q28 Q5 Q22 16 *)
  0x4e7583d7;       (* arm_SMLAL2_VEC Q23 Q30 Q21 16 *)
  0x4e6083a8;       (* arm_SMLAL2_VEC Q8 Q29 Q0 16 *)
  0x3dc0050f;       (* arm_LDR Q15 X8 (Immediate_Offset (word 16)) *)
  0x4e698217;       (* arm_SMLAL2_VEC Q23 Q16 Q9 16 *)
  0x3cc20515;       (* arm_LDR Q21 X8 (Postimmediate_Offset (word 32)) *)
  0x4e531976;       (* arm_UZP1 Q22 Q11 Q19 16 *)
  0x4e53596c;       (* arm_UZP2 Q12 Q11 Q19 16 *)
  0x3dc004e1;       (* arm_LDR Q1 X7 (Immediate_Offset (word 16)) *)
  0x4cdf74c6;       (* arm_LDR Q6 X6 (Postimmediate_Offset (word 16)) *)
  0x4e485a43;       (* arm_UZP2 Q3 Q18 Q8 16 *)
  0x0e7fc2c9;       (* arm_SMULL_VEC Q9 Q22 Q31 16 *)
  0x4e7fc2d2;       (* arm_SMULL2_VEC Q18 Q22 Q31 16 *)
  0x3cc204f0;       (* arm_LDR Q16 X7 (Postimmediate_Offset (word 32)) *)
  0x0e78c2d3;       (* arm_SMULL_VEC Q19 Q22 Q24 16 *)
  0x4e4f1abe;       (* arm_UZP1 Q30 Q21 Q15 16 *)
  0x4e4f5ab9;       (* arm_UZP2 Q25 Q21 Q15 16 *)
  0x4e78c2c8;       (* arm_SMULL2_VEC Q8 Q22 Q24 16 *)
  0x0e748193;       (* arm_SMLAL_VEC Q19 Q12 Q20 16 *)
  0x3dc0054d;       (* arm_LDR Q13 X10 (Immediate_Offset (word 16)) *)
  0x4e748188;       (* arm_SMLAL2_VEC Q8 Q12 Q20 16 *)
  0x4e411a1d;       (* arm_UZP1 Q29 Q16 Q1 16 *)
  0x4e788192;       (* arm_SMLAL2_VEC Q18 Q12 Q24 16 *)
  0x3cc20545;       (* arm_LDR Q5 X10 (Postimmediate_Offset (word 32)) *)
  0x0e788189;       (* arm_SMLAL_VEC Q9 Q12 Q24 16 *)
  0x3cc20564;       (* arm_LDR Q4 X11 (Postimmediate_Offset (word 32)) *)
  0x0e7c8229;       (* arm_SMLAL_VEC Q9 Q17 Q28 16 *)
  0x3cdf0176;       (* arm_LDR Q22 X11 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7c8232;       (* arm_SMLAL2_VEC Q18 Q17 Q28 16 *)
  0x4e415a10;       (* arm_UZP2 Q16 Q16 Q1 16 *)
  0x0e6e8233;       (* arm_SMLAL_VEC Q19 Q17 Q14 16 *)
  0x4cdf753c;       (* arm_LDR Q28 X9 (Postimmediate_Offset (word 16)) *)
  0x4e6e8228;       (* arm_SMLAL2_VEC Q8 Q17 Q14 16 *)
  0x4e4d18a7;       (* arm_UZP1 Q7 Q5 Q13 16 *)
  0x0e6e8369;       (* arm_SMLAL_VEC Q9 Q27 Q14 16 *)
  0x4e561891;       (* arm_UZP1 Q17 Q4 Q22 16 *)
  0x4e6e8372;       (* arm_SMLAL2_VEC Q18 Q27 Q14 16 *)
  0x4e4d58ac;       (* arm_UZP2 Q12 Q5 Q13 16 *)
  0x4e565895;       (* arm_UZP2 Q21 Q4 Q22 16 *)
  0x0e668373;       (* arm_SMLAL_VEC Q19 Q27 Q6 16 *)
  0x4e668368;       (* arm_SMLAL2_VEC Q8 Q27 Q6 16 *)
  0x4cdf758f;       (* arm_LDR Q15 X12 (Postimmediate_Offset (word 16)) *)
  0x0e7e83b3;       (* arm_SMLAL_VEC Q19 Q29 Q30 16 *)
  0x4e571b54;       (* arm_UZP1 Q20 Q26 Q23 16 *)
  0x0e7983a9;       (* arm_SMLAL_VEC Q9 Q29 Q25 16 *)
  0x4e7983b2;       (* arm_SMLAL2_VEC Q18 Q29 Q25 16 *)
  0x4e7e83a8;       (* arm_SMLAL2_VEC Q8 Q29 Q30 16 *)
  0x0e7c8213;       (* arm_SMLAL_VEC Q19 Q16 Q28 16 *)
  0x4e7c8208;       (* arm_SMLAL2_VEC Q8 Q16 Q28 16 *)
  0x4e7e8212;       (* arm_SMLAL2_VEC Q18 Q16 Q30 16 *)
  0x0e7e8209;       (* arm_SMLAL_VEC Q9 Q16 Q30 16 *)
  0x0e7580e9;       (* arm_SMLAL_VEC Q9 Q7 Q21 16 *)
  0x4e7580f2;       (* arm_SMLAL2_VEC Q18 Q7 Q21 16 *)
  0x4e7180e8;       (* arm_SMLAL2_VEC Q8 Q7 Q17 16 *)
  0x0e7180f3;       (* arm_SMLAL_VEC Q19 Q7 Q17 16 *)
  0x0e6f8193;       (* arm_SMLAL_VEC Q19 Q12 Q15 16 *)
  0x4e6f8188;       (* arm_SMLAL2_VEC Q8 Q12 Q15 16 *)
  0x4e718192;       (* arm_SMLAL2_VEC Q18 Q12 Q17 16 *)
  0x0e718189;       (* arm_SMLAL_VEC Q9 Q12 Q17 16 *)
  0x4e629e86;       (* arm_MUL_VEC Q6 Q20 Q2 16 128 *)
  0x4e481a64;       (* arm_UZP1 Q4 Q19 Q8 16 *)
  0x4e629c91;       (* arm_MUL_VEC Q17 Q4 Q2 16 128 *)
  0x4e52192c;       (* arm_UZP1 Q12 Q9 Q18 16 *)
  0x0e6080da;       (* arm_SMLAL_VEC Q26 Q6 Q0 16 *)
  0x4e629d95;       (* arm_MUL_VEC Q21 Q12 Q2 16 128 *)
  0x4e6080d7;       (* arm_SMLAL2_VEC Q23 Q6 Q0 16 *)
  0x4e608228;       (* arm_SMLAL2_VEC Q8 Q17 Q0 16 *)
  0x0e608233;       (* arm_SMLAL_VEC Q19 Q17 Q0 16 *)
  0x4e6082b2;       (* arm_SMLAL2_VEC Q18 Q21 Q0 16 *)
  0x4e575b57;       (* arm_UZP2 Q23 Q26 Q23 16 *)
  0x0e6082a9;       (* arm_SMLAL_VEC Q9 Q21 Q0 16 *)
  0x4e437aec;       (* arm_ZIP2 Q12 Q23 Q3 16 128 *)
  0x4e433af6;       (* arm_ZIP1 Q22 Q23 Q3 16 128 *)
  0x4e485a6e;       (* arm_UZP2 Q14 Q19 Q8 16 *)
  0x4e525932;       (* arm_UZP2 Q18 Q9 Q18 16 *)
  0x3d80040c;       (* arm_STR Q12 X0 (Immediate_Offset (word 16)) *)
  0x3c820416;       (* arm_STR Q22 X0 (Postimmediate_Offset (word 32)) *)
  0x4e5279d8;       (* arm_ZIP2 Q24 Q14 Q18 16 128 *)
  0x4e5239d5;       (* arm_ZIP1 Q21 Q14 Q18 16 128 *)
  0x3d800418;       (* arm_STR Q24 X0 (Immediate_Offset (word 16)) *)
  0x3c820415;       (* arm_STR Q21 X0 (Postimmediate_Offset (word 32)) *)
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
 (* Code length constants                                                     *)
 (* ------------------------------------------------------------------------- *)

 let LENGTH_POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_MC =
   REWRITE_CONV[poly_basemul_acc_montgomery_cached_k4_mc] `LENGTH poly_basemul_acc_montgomery_cached_k4_mc`
   |> CONV_RULE (RAND_CONV LENGTH_CONV);;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_PREAMBLE_LENGTH = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_PREAMBLE_LENGTH = 20`;;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_POSTAMBLE_LENGTH = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_POSTAMBLE_LENGTH = 24`;;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_START = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_START = POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_PREAMBLE_LENGTH`;;

 let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_END = new_definition
   `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_END = LENGTH poly_basemul_acc_montgomery_cached_k4_mc - POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_POSTAMBLE_LENGTH`;;

 let LENGTH_SIMPLIFY_CONV =
   REWRITE_CONV[LENGTH_POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_MC;
               POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_START; POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_END;
               POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_PREAMBLE_LENGTH; POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_POSTAMBLE_LENGTH] THENC
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

  let poly_basemul_acc_montgomery_cached_k4_GOAL = `forall srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc.
       ALL (nonoverlapping (dst, 512))
           [(word pc, LENGTH poly_basemul_acc_montgomery_cached_k4_mc); (srcA, 2048); (srcB, 2048); (srcBt, 1024)]
       ==>
       ensures arm
         (\s. aligned_bytes_loaded s (word pc) poly_basemul_acc_montgomery_cached_k4_mc /\
              read PC s = word (pc + POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_START)  /\
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
         (\s. read PC s = word (pc + POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K4_CORE_END) /\
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
        CONV_TAC LENGTH_SIMPLIFY_CONV THEN
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
       MAP_UNTIL_TARGET_PC (fun n -> ARM_STEPS_TAC poly_basemul_acc_montgomery_cached_k4_EXEC [n] THEN
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
       (REWRITE_RULE[fst poly_basemul_acc_montgomery_cached_k4_EXEC] (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV poly_basemul_acc_montgomery_cached_k4_SPEC)))
        `[D8; D9; D10; D11; D12; D13; D14; D15]` 64  THEN
     WORD_ARITH_TAC)
  ;;
