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
        0x3dc00457;       (* arm_LDR Q23 X2 (Immediate_Offset (word 16)) *)
        0x3cc20453;       (* arm_LDR Q19 X2 (Postimmediate_Offset (word 32)) *)
        0x3cc204b1;       (* arm_LDR Q17 X5 (Postimmediate_Offset (word 32)) *)
        0x4e575a6d;       (* arm_UZP2 Q13 Q19 Q23 16 *)
        0x4e571a73;       (* arm_UZP1 Q19 Q19 Q23 16 *)
        0x3cdf00b7;       (* arm_LDR Q23 X5 (Immediate_Offset (word 18446744073709551600)) *)
        0x3dc0043e;       (* arm_LDR Q30 X1 (Immediate_Offset (word 16)) *)
        0x4e575a29;       (* arm_UZP2 Q9 Q17 Q23 16 *)
        0x4e571a37;       (* arm_UZP1 Q23 Q17 Q23 16 *)
        0x3cc20431;       (* arm_LDR Q17 X1 (Postimmediate_Offset (word 32)) *)
        0x3dc004ea;       (* arm_LDR Q10 X7 (Immediate_Offset (word 16)) *)
        0x4e5e1a2c;       (* arm_UZP1 Q12 Q17 Q30 16 *)
        0x4e5e5a31;       (* arm_UZP2 Q17 Q17 Q30 16 *)
        0x4e6dc19e;       (* arm_SMULL2_VEC Q30 Q12 Q13 16 *)
        0x0e6dc18d;       (* arm_SMULL_VEC Q13 Q12 Q13 16 *)
        0x4e73c196;       (* arm_SMULL2_VEC Q22 Q12 Q19 16 *)
        0x0e73c18c;       (* arm_SMULL_VEC Q12 Q12 Q19 16 *)
        0x4e73823e;       (* arm_SMLAL2_VEC Q30 Q17 Q19 16 *)
        0x0e73822d;       (* arm_SMLAL_VEC Q13 Q17 Q19 16 *)
        0x3cc20493;       (* arm_LDR Q19 X4 (Postimmediate_Offset (word 32)) *)
        0x3cdf0090;       (* arm_LDR Q16 X4 (Immediate_Offset (word 18446744073709551600)) *)
        0x4cdf7468;       (* arm_LDR Q8 X3 (Postimmediate_Offset (word 16)) *)
        0x4e501a7a;       (* arm_UZP1 Q26 Q19 Q16 16 *)
        0x4e505a73;       (* arm_UZP2 Q19 Q19 Q16 16 *)
        0x4e69835e;       (* arm_SMLAL2_VEC Q30 Q26 Q9 16 *)
        0x0e69834d;       (* arm_SMLAL_VEC Q13 Q26 Q9 16 *)
        0x4e688236;       (* arm_SMLAL2_VEC Q22 Q17 Q8 16 *)
        0x0e68822c;       (* arm_SMLAL_VEC Q12 Q17 Q8 16 *)
        0x4e77827e;       (* arm_SMLAL2_VEC Q30 Q19 Q23 16 *)
        0x0e77826d;       (* arm_SMLAL_VEC Q13 Q19 Q23 16 *)
        0x4e778356;       (* arm_SMLAL2_VEC Q22 Q26 Q23 16 *)
        0x0e77834c;       (* arm_SMLAL_VEC Q12 Q26 Q23 16 *)
        0x3cc204f7;       (* arm_LDR Q23 X7 (Postimmediate_Offset (word 32)) *)
        0x3dc00511;       (* arm_LDR Q17 X8 (Immediate_Offset (word 16)) *)
        0x4e4a1ae9;       (* arm_UZP1 Q9 Q23 Q10 16 *)
        0x4e4a5af7;       (* arm_UZP2 Q23 Q23 Q10 16 *)
        0x3cc2054a;       (* arm_LDR Q10 X10 (Postimmediate_Offset (word 32)) *)
        0x3cdf0150;       (* arm_LDR Q16 X10 (Immediate_Offset (word 18446744073709551600)) *)
        0x4cdf7588;       (* arm_LDR Q8 X12 (Postimmediate_Offset (word 16)) *)
        0x4e50195a;       (* arm_UZP1 Q26 Q10 Q16 16 *)
        0x4e50594a;       (* arm_UZP2 Q10 Q10 Q16 16 *)
        0x4cdf74d0;       (* arm_LDR Q16 X6 (Postimmediate_Offset (word 16)) *)
        0x3dc00563;       (* arm_LDR Q3 X11 (Immediate_Offset (word 16)) *)
        0x4e708276;       (* arm_SMLAL2_VEC Q22 Q19 Q16 16 *)
        0x0e70826c;       (* arm_SMLAL_VEC Q12 Q19 Q16 16 *)
        0x3cc20573;       (* arm_LDR Q19 X11 (Postimmediate_Offset (word 32)) *)
        0x4cdf7530;       (* arm_LDR Q16 X9 (Postimmediate_Offset (word 16)) *)
        0x4e431a64;       (* arm_UZP1 Q4 Q19 Q3 16 *)
        0x4e435a73;       (* arm_UZP2 Q19 Q19 Q3 16 *)
        0x3cc20503;       (* arm_LDR Q3 X8 (Postimmediate_Offset (word 32)) *)
        0x3cc2045f;       (* arm_LDR Q31 X2 (Postimmediate_Offset (word 32)) *)
        0x4e511866;       (* arm_UZP1 Q6 Q3 Q17 16 *)
        0x4e515871;       (* arm_UZP2 Q17 Q3 Q17 16 *)
        0x4e668136;       (* arm_SMLAL2_VEC Q22 Q9 Q6 16 *)
        0x4e71813e;       (* arm_SMLAL2_VEC Q30 Q9 Q17 16 *)
        0x0e71812d;       (* arm_SMLAL_VEC Q13 Q9 Q17 16 *)
        0x0e66812c;       (* arm_SMLAL_VEC Q12 Q9 Q6 16 *)
        0x4e7082f6;       (* arm_SMLAL2_VEC Q22 Q23 Q16 16 *)
        0x4e6682fe;       (* arm_SMLAL2_VEC Q30 Q23 Q6 16 *)
        0x0e6682ed;       (* arm_SMLAL_VEC Q13 Q23 Q6 16 *)
        0x0e7082ec;       (* arm_SMLAL_VEC Q12 Q23 Q16 16 *)
        0x4e648356;       (* arm_SMLAL2_VEC Q22 Q26 Q4 16 *)
        0x4e73835e;       (* arm_SMLAL2_VEC Q30 Q26 Q19 16 *)
        0x0e73834d;       (* arm_SMLAL_VEC Q13 Q26 Q19 16 *)
        0x0e64834c;       (* arm_SMLAL_VEC Q12 Q26 Q4 16 *)
        0x4e688156;       (* arm_SMLAL2_VEC Q22 Q10 Q8 16 *)
        0x4e64815e;       (* arm_SMLAL2_VEC Q30 Q10 Q4 16 *)
        0x0e64814d;       (* arm_SMLAL_VEC Q13 Q10 Q4 16 *)
        0x0e68814c;       (* arm_SMLAL_VEC Q12 Q10 Q8 16 *)
        0x3cdf0053;       (* arm_LDR Q19 X2 (Immediate_Offset (word 18446744073709551600)) *)
        0x4e5e19b7;       (* arm_UZP1 Q23 Q13 Q30 16 *)
        0x4e561991;       (* arm_UZP1 Q17 Q12 Q22 16 *)
        0x4e629ef7;       (* arm_MUL_VEC Q23 Q23 Q2 16 128 *)
        0x4e535bf5;       (* arm_UZP2 Q21 Q31 Q19 16 *)
        0x4e531bf3;       (* arm_UZP1 Q19 Q31 Q19 16 *)
        0x4e629e31;       (* arm_MUL_VEC Q17 Q17 Q2 16 128 *)
        0x0e6082ed;       (* arm_SMLAL_VEC Q13 Q23 Q0 16 *)
        0x4e6082fe;       (* arm_SMLAL2_VEC Q30 Q23 Q0 16 *)
        0x3cc204b7;       (* arm_LDR Q23 X5 (Postimmediate_Offset (word 32)) *)
        0x4e608236;       (* arm_SMLAL2_VEC Q22 Q17 Q0 16 *)
        0x4e5e59af;       (* arm_UZP2 Q15 Q13 Q30 16 *)
        0x0e60822c;       (* arm_SMLAL_VEC Q12 Q17 Q0 16 *)
        0x3cdf00b1;       (* arm_LDR Q17 X5 (Immediate_Offset (word 18446744073709551600)) *)
        0x3dc0042d;       (* arm_LDR Q13 X1 (Immediate_Offset (word 16)) *)
        0x4e515afb;       (* arm_UZP2 Q27 Q23 Q17 16 *)
        0x4e511afc;       (* arm_UZP1 Q28 Q23 Q17 16 *)
        0x4e565987;       (* arm_UZP2 Q7 Q12 Q22 16 *)
        0x3cc20437;       (* arm_LDR Q23 X1 (Postimmediate_Offset (word 32)) *)
        0x4e4f38e5;       (* arm_ZIP1 Q5 Q7 Q15 16 128 *)
        0x3dc004e3;       (* arm_LDR Q3 X7 (Immediate_Offset (word 16)) *)
        0x4e4d1aff;       (* arm_UZP1 Q31 Q23 Q13 16 *)
        0x4e4d5af0;       (* arm_UZP2 Q16 Q23 Q13 16 *)
        0x4e75c3f8;       (* arm_SMULL2_VEC Q24 Q31 Q21 16 *)
        0x3dc00506;       (* arm_LDR Q6 X8 (Immediate_Offset (word 16)) *)
        0x3cc20557;       (* arm_LDR Q23 X10 (Postimmediate_Offset (word 32)) *)
        0x4e738218;       (* arm_SMLAL2_VEC Q24 Q16 Q19 16 *)
        0x3cdf0151;       (* arm_LDR Q17 X10 (Immediate_Offset (word 18446744073709551600)) *)
        0x4cdf7596;       (* arm_LDR Q22 X12 (Postimmediate_Offset (word 16)) *)
        0x4e511afe;       (* arm_UZP1 Q30 Q23 Q17 16 *)
        0x4e515aeb;       (* arm_UZP2 Q11 Q23 Q17 16 *)
        0x3cc20497;       (* arm_LDR Q23 X4 (Postimmediate_Offset (word 32)) *)
        0x3cdf0091;       (* arm_LDR Q17 X4 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc204e4;       (* arm_LDR Q4 X7 (Postimmediate_Offset (word 32)) *)
        0x4e511af4;       (* arm_UZP1 Q20 Q23 Q17 16 *)
        0x4e515afa;       (* arm_UZP2 Q26 Q23 Q17 16 *)
        0x4e431889;       (* arm_UZP1 Q9 Q4 Q3 16 *)
        0x4e7b8298;       (* arm_SMLAL2_VEC Q24 Q20 Q27 16 *)
        0x4cdf74c8;       (* arm_LDR Q8 X6 (Postimmediate_Offset (word 16)) *)
        0x3dc00579;       (* arm_LDR Q25 X11 (Immediate_Offset (word 16)) *)
        0x3cc2057d;       (* arm_LDR Q29 X11 (Postimmediate_Offset (word 32)) *)
        0x4cdf752c;       (* arm_LDR Q12 X9 (Postimmediate_Offset (word 16)) *)
        0x4e591baa;       (* arm_UZP1 Q10 Q29 Q25 16 *)
        0x3cc2050e;       (* arm_LDR Q14 X8 (Postimmediate_Offset (word 32)) *)
        0x4cdf7477;       (* arm_LDR Q23 X3 (Postimmediate_Offset (word 16)) *)
        0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
        0x4e7c8358;       (* arm_SMLAL2_VEC Q24 Q26 Q28 16 *)
        0x4e435884;       (* arm_UZP2 Q4 Q4 Q3 16 *)
        0x4e73c3ed;       (* arm_SMULL2_VEC Q13 Q31 Q19 16 *)
        0x3cc20443;       (* arm_LDR Q3 X2 (Postimmediate_Offset (word 32)) *)
        0x4e595ba1;       (* arm_UZP2 Q1 Q29 Q25 16 *)
        0x4e77820d;       (* arm_SMLAL2_VEC Q13 Q16 Q23 16 *)
        0x3cdf0051;       (* arm_LDR Q17 X2 (Immediate_Offset (word 18446744073709551600)) *)
        0x0e73c3f2;       (* arm_SMULL_VEC Q18 Q31 Q19 16 *)
        0x4e7c828d;       (* arm_SMLAL2_VEC Q13 Q20 Q28 16 *)
        0x0e75c3fd;       (* arm_SMULL_VEC Q29 Q31 Q21 16 *)
        0x3cc204b5;       (* arm_LDR Q21 X5 (Postimmediate_Offset (word 32)) *)
        0x4e68834d;       (* arm_SMLAL2_VEC Q13 Q26 Q8 16 *)
        0x0e73821d;       (* arm_SMLAL_VEC Q29 Q16 Q19 16 *)
        0x3cdf00b3;       (* arm_LDR Q19 X5 (Immediate_Offset (word 18446744073709551600)) *)
        0x0e778212;       (* arm_SMLAL_VEC Q18 Q16 Q23 16 *)
        0x0e7b829d;       (* arm_SMLAL_VEC Q29 Q20 Q27 16 *)
        0x4e4619df;       (* arm_UZP1 Q31 Q14 Q6 16 *)
        0x4e535abb;       (* arm_UZP2 Q27 Q21 Q19 16 *)
        0x0e7c8292;       (* arm_SMLAL_VEC Q18 Q20 Q28 16 *)
        0x3dc00439;       (* arm_LDR Q25 X1 (Immediate_Offset (word 16)) *)
        0x0e7c835d;       (* arm_SMLAL_VEC Q29 Q26 Q28 16 *)
        0x0e688352;       (* arm_SMLAL_VEC Q18 Q26 Q8 16 *)
        0x4e4659da;       (* arm_UZP2 Q26 Q14 Q6 16 *)
        0x4e7f812d;       (* arm_SMLAL2_VEC Q13 Q9 Q31 16 *)
        0x4e7a8138;       (* arm_SMLAL2_VEC Q24 Q9 Q26 16 *)
        0x0e7a813d;       (* arm_SMLAL_VEC Q29 Q9 Q26 16 *)
        0x0e7f8132;       (* arm_SMLAL_VEC Q18 Q9 Q31 16 *)
        0x4e6c808d;       (* arm_SMLAL2_VEC Q13 Q4 Q12 16 *)
        0x4e7f8098;       (* arm_SMLAL2_VEC Q24 Q4 Q31 16 *)
        0x0e7f809d;       (* arm_SMLAL_VEC Q29 Q4 Q31 16 *)
        0x0e6c8092;       (* arm_SMLAL_VEC Q18 Q4 Q12 16 *)
        0x4e6a83cd;       (* arm_SMLAL2_VEC Q13 Q30 Q10 16 *)
        0x4e6183d8;       (* arm_SMLAL2_VEC Q24 Q30 Q1 16 *)
        0x0e6183dd;       (* arm_SMLAL_VEC Q29 Q30 Q1 16 *)
        0x0e6a83d2;       (* arm_SMLAL_VEC Q18 Q30 Q10 16 *)
        0x4e76816d;       (* arm_SMLAL2_VEC Q13 Q11 Q22 16 *)
        0x4e6a8178;       (* arm_SMLAL2_VEC Q24 Q11 Q10 16 *)
        0x0e6a817d;       (* arm_SMLAL_VEC Q29 Q11 Q10 16 *)
        0x0e768172;       (* arm_SMLAL_VEC Q18 Q11 Q22 16 *)
        0x3cc20436;       (* arm_LDR Q22 X1 (Postimmediate_Offset (word 32)) *)
        0x4e581bbf;       (* arm_UZP1 Q31 Q29 Q24 16 *)
        0x4e531abc;       (* arm_UZP1 Q28 Q21 Q19 16 *)
        0x4e629ff3;       (* arm_MUL_VEC Q19 Q31 Q2 16 128 *)
        0x4e591adf;       (* arm_UZP1 Q31 Q22 Q25 16 *)
        0x4e595ad0;       (* arm_UZP2 Q16 Q22 Q25 16 *)
        0x4e515875;       (* arm_UZP2 Q21 Q3 Q17 16 *)
        0x0e60827d;       (* arm_SMLAL_VEC Q29 Q19 Q0 16 *)
        0x4e608278;       (* arm_SMLAL2_VEC Q24 Q19 Q0 16 *)
        0x4e511873;       (* arm_UZP1 Q19 Q3 Q17 16 *)
        0x4e4d1a5a;       (* arm_UZP1 Q26 Q18 Q13 16 *)
        0x4e4f78ee;       (* arm_ZIP2 Q14 Q7 Q15 16 128 *)
        0x4e629f57;       (* arm_MUL_VEC Q23 Q26 Q2 16 128 *)
        0x4e585baf;       (* arm_UZP2 Q15 Q29 Q24 16 *)
        0x4e75c3f8;       (* arm_SMULL2_VEC Q24 Q31 Q21 16 *)
        0x3d80040e;       (* arm_STR Q14 X0 (Immediate_Offset (word 16)) *)
        0x3dc004e3;       (* arm_LDR Q3 X7 (Immediate_Offset (word 16)) *)
        0x3dc00506;       (* arm_LDR Q6 X8 (Immediate_Offset (word 16)) *)
        0x3cc20548;       (* arm_LDR Q8 X10 (Postimmediate_Offset (word 32)) *)
        0x3cdf015a;       (* arm_LDR Q26 X10 (Immediate_Offset (word 18446744073709551600)) *)
        0x4cdf7596;       (* arm_LDR Q22 X12 (Postimmediate_Offset (word 16)) *)
        0x4e5a191e;       (* arm_UZP1 Q30 Q8 Q26 16 *)
        0x4e5a590b;       (* arm_UZP2 Q11 Q8 Q26 16 *)
        0x3cc20488;       (* arm_LDR Q8 X4 (Postimmediate_Offset (word 32)) *)
        0x3cdf009a;       (* arm_LDR Q26 X4 (Immediate_Offset (word 18446744073709551600)) *)
        0x3cc204e4;       (* arm_LDR Q4 X7 (Postimmediate_Offset (word 32)) *)
        0x4e5a1914;       (* arm_UZP1 Q20 Q8 Q26 16 *)
        0x4e5a591a;       (* arm_UZP2 Q26 Q8 Q26 16 *)
        0x4cdf74c8;       (* arm_LDR Q8 X6 (Postimmediate_Offset (word 16)) *)
        0x4e431889;       (* arm_UZP1 Q9 Q4 Q3 16 *)
        0x3dc00579;       (* arm_LDR Q25 X11 (Immediate_Offset (word 16)) *)
        0x3cc2057d;       (* arm_LDR Q29 X11 (Postimmediate_Offset (word 32)) *)
        0x4cdf752c;       (* arm_LDR Q12 X9 (Postimmediate_Offset (word 16)) *)
        0x3cc2050e;       (* arm_LDR Q14 X8 (Postimmediate_Offset (word 32)) *)
        0x4e738218;       (* arm_SMLAL2_VEC Q24 Q16 Q19 16 *)
        0x4e6082ed;       (* arm_SMLAL2_VEC Q13 Q23 Q0 16 *)
        0x0e6082f2;       (* arm_SMLAL_VEC Q18 Q23 Q0 16 *)
        0x4cdf7477;       (* arm_LDR Q23 X3 (Postimmediate_Offset (word 16)) *)
        0x4e7b8298;       (* arm_SMLAL2_VEC Q24 Q20 Q27 16 *)
        0x4e4d5a47;       (* arm_UZP2 Q7 Q18 Q13 16 *)
        0x4e591baa;       (* arm_UZP1 Q10 Q29 Q25 16 *)
        0x3c820405;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 32)) *)
        0x4e4f38e5;       (* arm_ZIP1 Q5 Q7 Q15 16 128 *)
        0xd10005ad;       (* arm_SUB X13 X13 (rvalue (word 1)) *)
        0xb5fff5ad;       (* arm_CBNZ X13 (word 2096820) *)
        0x4e73c3f1;       (* arm_SMULL2_VEC Q17 Q31 Q19 16 *)
        0x4e4659c1;       (* arm_UZP2 Q1 Q14 Q6 16 *)
        0x0e75c3f2;       (* arm_SMULL_VEC Q18 Q31 Q21 16 *)
        0x4e7c8358;       (* arm_SMLAL2_VEC Q24 Q26 Q28 16 *)
        0x4e778211;       (* arm_SMLAL2_VEC Q17 Q16 Q23 16 *)
        0x0e73c3f5;       (* arm_SMULL_VEC Q21 Q31 Q19 16 *)
        0x0e738212;       (* arm_SMLAL_VEC Q18 Q16 Q19 16 *)
        0x4e43589f;       (* arm_UZP2 Q31 Q4 Q3 16 *)
        0x4e4619c3;       (* arm_UZP1 Q3 Q14 Q6 16 *)
        0x0e778215;       (* arm_SMLAL_VEC Q21 Q16 Q23 16 *)
        0x0e7b8292;       (* arm_SMLAL_VEC Q18 Q20 Q27 16 *)
        0x4e595bae;       (* arm_UZP2 Q14 Q29 Q25 16 *)
        0x4e7c8291;       (* arm_SMLAL2_VEC Q17 Q20 Q28 16 *)
        0x0e7c8295;       (* arm_SMLAL_VEC Q21 Q20 Q28 16 *)
        0x0e7c8352;       (* arm_SMLAL_VEC Q18 Q26 Q28 16 *)
        0x4e618138;       (* arm_SMLAL2_VEC Q24 Q9 Q1 16 *)
        0x4e688351;       (* arm_SMLAL2_VEC Q17 Q26 Q8 16 *)
        0x0e688355;       (* arm_SMLAL_VEC Q21 Q26 Q8 16 *)
        0x0e618132;       (* arm_SMLAL_VEC Q18 Q9 Q1 16 *)
        0x4e6383f8;       (* arm_SMLAL2_VEC Q24 Q31 Q3 16 *)
        0x4e638131;       (* arm_SMLAL2_VEC Q17 Q9 Q3 16 *)
        0x0e638135;       (* arm_SMLAL_VEC Q21 Q9 Q3 16 *)
        0x0e6383f2;       (* arm_SMLAL_VEC Q18 Q31 Q3 16 *)
        0x4e6e83d8;       (* arm_SMLAL2_VEC Q24 Q30 Q14 16 *)
        0x4e6c83f1;       (* arm_SMLAL2_VEC Q17 Q31 Q12 16 *)
        0x0e6c83f5;       (* arm_SMLAL_VEC Q21 Q31 Q12 16 *)
        0x0e6e83d2;       (* arm_SMLAL_VEC Q18 Q30 Q14 16 *)
        0x4e6a8178;       (* arm_SMLAL2_VEC Q24 Q11 Q10 16 *)
        0x4e6a83d1;       (* arm_SMLAL2_VEC Q17 Q30 Q10 16 *)
        0x0e6a83d5;       (* arm_SMLAL_VEC Q21 Q30 Q10 16 *)
        0x0e6a8172;       (* arm_SMLAL_VEC Q18 Q11 Q10 16 *)
        0x4e4f78f3;       (* arm_ZIP2 Q19 Q7 Q15 16 128 *)
        0x4e768171;       (* arm_SMLAL2_VEC Q17 Q11 Q22 16 *)
        0x0e768175;       (* arm_SMLAL_VEC Q21 Q11 Q22 16 *)
        0x4e581a57;       (* arm_UZP1 Q23 Q18 Q24 16 *)
        0x3d800413;       (* arm_STR Q19 X0 (Immediate_Offset (word 16)) *)
        0x4e629ef3;       (* arm_MUL_VEC Q19 Q23 Q2 16 128 *)
        0x4e511ab7;       (* arm_UZP1 Q23 Q21 Q17 16 *)
        0x3c820405;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 32)) *)
        0x4e629efa;       (* arm_MUL_VEC Q26 Q23 Q2 16 128 *)
        0x0e608272;       (* arm_SMLAL_VEC Q18 Q19 Q0 16 *)
        0x4e608278;       (* arm_SMLAL2_VEC Q24 Q19 Q0 16 *)
        0x0e608355;       (* arm_SMLAL_VEC Q21 Q26 Q0 16 *)
        0x4e608351;       (* arm_SMLAL2_VEC Q17 Q26 Q0 16 *)
        0x4e585a4d;       (* arm_UZP2 Q13 Q18 Q24 16 *)
        0x4e515ab3;       (* arm_UZP2 Q19 Q21 Q17 16 *)
        0x4e4d3a77;       (* arm_ZIP1 Q23 Q19 Q13 16 128 *)
        0x4e4d7a73;       (* arm_ZIP2 Q19 Q19 Q13 16 128 *)
        0x3c820417;       (* arm_STR Q23 X0 (Postimmediate_Offset (word 32)) *)
        0x3c9f0013;       (* arm_STR Q19 X0 (Immediate_Offset (word 18446744073709551600)) *)
        0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
        0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
        0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
        0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
        0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
        0xd65f03c0        (* arm_RET X30 *)
      ];;

  let pmull = define
    `pmull (x0: 16 word) (x1 : 16 word) (y0 : 16 word) (y1 : 16 word) =
        word_add (word_mul ((word_sx x1) : 32 word) (word_sx y1))
                 (word_mul ((word_sx x0) : 32 word) (word_sx y0))`;;

  let pmull_acc4 = define
  `pmull_acc4 (x00: 16 word) (x01 : 16 word) (y00 : 16 word) (y01 : 16 word)
              (x10: 16 word) (x11 : 16 word) (y10 : 16 word) (y11 : 16 word)
              (x20: 16 word) (x21 : 16 word) (y20 : 16 word) (y21 : 16 word)
              (x30: 16 word) (x31 : 16 word) (y30 : 16 word) (y31 : 16 word) =
    word_add (word_add (word_add (pmull x30 x31 y30 y31) (pmull x20 x21 y20 y21)) (pmull x10 x11 y10 y11)) (pmull x00 x01 y00 y01)`;;

  let montred = define
     `(montred:int32->int16) x =
        word_subword (
           word_add (
             word_mul (
               (word_sx : 16 word -> 32 word) (
                 word_mul (
                   word_subword x (0,16)
                 ) (word 3327)
               )
             )
             (word 3329)
           ) x
        ) (16, 16)`;;

  let pmul_acc4 = define
      `pmul_acc4 (x00: 16 word) (x01 : 16 word) (y00 : 16 word) (y01 : 16 word)
                 (x10: 16 word) (x11 : 16 word) (y10 : 16 word) (y11 : 16 word)
                 (x20: 16 word) (x21 : 16 word) (y20 : 16 word) (y21 : 16 word)
                 (x30: 16 word) (x31 : 16 word) (y30 : 16 word) (y31 : 16 word) =
        montred (pmull_acc4 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21 x30 x31 y30 y31)`;;

  let basemul4_even_raw = define
     `basemul4_even_raw x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t = \i.
        pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
                  (y0 (2 * i)) (y0t i)
                  (x1 (2 * i)) (x1 (2 * i + 1))
                  (y1 (2 * i)) (y1t i)
                  (x2 (2 * i)) (x2 (2 * i + 1))
                  (y2 (2 * i)) (y2t i)
                  (x3 (2 * i)) (x3 (2 * i + 1))
                  (y3 (2 * i)) (y3t i)
     `;;

  let basemul4_odd_raw = define
   `basemul4_odd_raw x0 y0 x1 y1 x2 y2 x3 y3 = \i.
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
              (!i. i < 128 ==> read(memory :> bytes16(word_add dst (word (4 * i)))) s =
                                    basemul4_even_raw x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t i /\
                               read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s =
                                    basemul4_odd_raw x0 y0 x1 y1 x2 y2 x3 y3 i))
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
                  (SIMD_SIMPLIFY_TAC [pmull; GSYM WORD_ADD_ASSOC; pmull_acc4; montred; pmul_acc4])) (1--1355) THEN

       ENSURES_FINAL_STATE_TAC THEN
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

       (* Forget all assumptions *)
       POP_ASSUM_LIST (K ALL_TAC) THEN

       (* Split into one congruence goals per index. *)
       REPEAT CONJ_TAC THEN

       REWRITE_TAC[basemul4_even_raw; basemul4_odd_raw] THEN
       CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
       CONV_TAC(REPEATC (CHANGED_CONV (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)))) THEN
       REFL_TAC
   );;

   let TWEAK_CONV =
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    ONCE_DEPTH_CONV NUM_ADD_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0];;

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
         (!i. i < 128 ==> read(memory :> bytes16(word_add dst (word (4 * i)))) s =
                               basemul4_even_raw x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t i /\
                          read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s =
                               basemul4_odd_raw x0 y0 x1 y1 x2 y2 x3 y3 i)
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
