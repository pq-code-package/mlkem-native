(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 10 bits.                        *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "s2n_bignum/arm/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;
needs "mlkem_native/aarch64/proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "aarch64/mlkem/mlkem_poly_compress_d10_aarch64_asm.o";;
 ****)

let mlkem_poly_compress_d10_mc = define_assert_from_elf
  "mlkem_poly_compress_d10_mc" "aarch64/mlkem/mlkem_poly_compress_d10_aarch64_asm.o"
(*** BYTECODE START ***)
[
  0x6f00e418;       (* arm_MOVI Q24 (word 0) *)
  0xd28dda03;       (* arm_MOV X3 (rvalue (word 28368)) *)
  0xf2a4ebe3;       (* arm_MOVK X3 (word 10079) 16 *)
  0x4e040c79;       (* arm_DUP_GEN Q25 X3 32 128 *)
  0xd2802003;       (* arm_MOV X3 (rvalue (word 256)) *)
  0xf2a06043;       (* arm_MOVK X3 (word 770) 16 *)
  0xf2c10083;       (* arm_MOVK X3 (word 2052) 32 *)
  0xf2e14123;       (* arm_MOVK X3 (word 2569) 48 *)
  0xd2818164;       (* arm_MOV X4 (rvalue (word 3083)) *)
  0xf2a10084;       (* arm_MOVK X4 (word 2052) 16 *)
  0xf2c14124;       (* arm_MOVK X4 (word 2569) 32 *)
  0xf2e18164;       (* arm_MOVK X4 (word 3083) 48 *)
  0x4e080c7a;       (* arm_DUP_GEN Q26 X3 64 128 *)
  0x4e080c90;       (* arm_DUP_GEN Q16 X4 64 128 *)
  0x4ed03b5a;       (* arm_ZIP1 Q26 Q26 Q16 64 128 *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
  0x3dc00822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 48)) *)
  0x3dc01024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 64)) *)
  0x3dc01425;       (* arm_LDR Q5 X1 (Immediate_Offset (word 80)) *)
  0x3dc01826;       (* arm_LDR Q6 X1 (Immediate_Offset (word 96)) *)
  0x3dc01c27;       (* arm_LDR Q7 X1 (Immediate_Offset (word 112)) *)
  0x4e586810;       (* arm_TRN2 Q16 Q0 Q24 16 128 *)
  0x4e582800;       (* arm_TRN1 Q0 Q0 Q24 16 128 *)
  0x6eb9b400;       (* arm_SQRDMULH_VEC Q0 Q0 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5600;       (* arm_SLI_VEC Q0 Q16 10 128 32 *)
  0x4e986810;       (* arm_TRN2 Q16 Q0 Q24 32 128 *)
  0x6f545600;       (* arm_SLI_VEC Q0 Q16 20 128 64 *)
  0x4e1a0000;       (* arm_TBL Q0 [Q0] Q26 128 *)
  0x4e586830;       (* arm_TRN2 Q16 Q1 Q24 16 128 *)
  0x4e582821;       (* arm_TRN1 Q1 Q1 Q24 16 128 *)
  0x6eb9b421;       (* arm_SQRDMULH_VEC Q1 Q1 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5601;       (* arm_SLI_VEC Q1 Q16 10 128 32 *)
  0x4e986830;       (* arm_TRN2 Q16 Q1 Q24 32 128 *)
  0x6f545601;       (* arm_SLI_VEC Q1 Q16 20 128 64 *)
  0x4e1a0021;       (* arm_TBL Q1 [Q1] Q26 128 *)
  0x4e586850;       (* arm_TRN2 Q16 Q2 Q24 16 128 *)
  0x4e582842;       (* arm_TRN1 Q2 Q2 Q24 16 128 *)
  0x6eb9b442;       (* arm_SQRDMULH_VEC Q2 Q2 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5602;       (* arm_SLI_VEC Q2 Q16 10 128 32 *)
  0x4e986850;       (* arm_TRN2 Q16 Q2 Q24 32 128 *)
  0x6f545602;       (* arm_SLI_VEC Q2 Q16 20 128 64 *)
  0x4e1a0042;       (* arm_TBL Q2 [Q2] Q26 128 *)
  0x4e586870;       (* arm_TRN2 Q16 Q3 Q24 16 128 *)
  0x4e582863;       (* arm_TRN1 Q3 Q3 Q24 16 128 *)
  0x6eb9b463;       (* arm_SQRDMULH_VEC Q3 Q3 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5603;       (* arm_SLI_VEC Q3 Q16 10 128 32 *)
  0x4e986870;       (* arm_TRN2 Q16 Q3 Q24 32 128 *)
  0x6f545603;       (* arm_SLI_VEC Q3 Q16 20 128 64 *)
  0x4e1a0063;       (* arm_TBL Q3 [Q3] Q26 128 *)
  0x4e586890;       (* arm_TRN2 Q16 Q4 Q24 16 128 *)
  0x4e582884;       (* arm_TRN1 Q4 Q4 Q24 16 128 *)
  0x6eb9b484;       (* arm_SQRDMULH_VEC Q4 Q4 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5604;       (* arm_SLI_VEC Q4 Q16 10 128 32 *)
  0x4e986890;       (* arm_TRN2 Q16 Q4 Q24 32 128 *)
  0x6f545604;       (* arm_SLI_VEC Q4 Q16 20 128 64 *)
  0x4e1a0084;       (* arm_TBL Q4 [Q4] Q26 128 *)
  0x4e5868b0;       (* arm_TRN2 Q16 Q5 Q24 16 128 *)
  0x4e5828a5;       (* arm_TRN1 Q5 Q5 Q24 16 128 *)
  0x6eb9b4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5605;       (* arm_SLI_VEC Q5 Q16 10 128 32 *)
  0x4e9868b0;       (* arm_TRN2 Q16 Q5 Q24 32 128 *)
  0x6f545605;       (* arm_SLI_VEC Q5 Q16 20 128 64 *)
  0x4e1a00a5;       (* arm_TBL Q5 [Q5] Q26 128 *)
  0x4e5868d0;       (* arm_TRN2 Q16 Q6 Q24 16 128 *)
  0x4e5828c6;       (* arm_TRN1 Q6 Q6 Q24 16 128 *)
  0x6eb9b4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5606;       (* arm_SLI_VEC Q6 Q16 10 128 32 *)
  0x4e9868d0;       (* arm_TRN2 Q16 Q6 Q24 32 128 *)
  0x6f545606;       (* arm_SLI_VEC Q6 Q16 20 128 64 *)
  0x4e1a00c6;       (* arm_TBL Q6 [Q6] Q26 128 *)
  0x4e5868f0;       (* arm_TRN2 Q16 Q7 Q24 16 128 *)
  0x4e5828e7;       (* arm_TRN1 Q7 Q7 Q24 16 128 *)
  0x6eb9b4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5607;       (* arm_SLI_VEC Q7 Q16 10 128 32 *)
  0x4e9868f0;       (* arm_TRN2 Q16 Q7 Q24 32 128 *)
  0x6f545607;       (* arm_SLI_VEC Q7 Q16 20 128 64 *)
  0x4e1a00e7;       (* arm_TBL Q7 [Q7] Q26 128 *)
  0x6e0750d1;       (* arm_EXT Q17 Q6 Q7 80 *)
  0x4c9f7000;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7001;       (* arm_STR Q1 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7002;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7003;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7004;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7005;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7006;       (* arm_STR Q6 X0 (Postimmediate_Offset (word 16)) *)
  0xd1003000;       (* arm_SUB X0 X0 (rvalue (word 12)) *)
  0x4c9f7011;       (* arm_STR Q17 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc02020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 128)) *)
  0x3dc02421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 144)) *)
  0x3dc02822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 160)) *)
  0x3dc02c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 176)) *)
  0x3dc03024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 192)) *)
  0x3dc03425;       (* arm_LDR Q5 X1 (Immediate_Offset (word 208)) *)
  0x3dc03826;       (* arm_LDR Q6 X1 (Immediate_Offset (word 224)) *)
  0x3dc03c27;       (* arm_LDR Q7 X1 (Immediate_Offset (word 240)) *)
  0x4e586810;       (* arm_TRN2 Q16 Q0 Q24 16 128 *)
  0x4e582800;       (* arm_TRN1 Q0 Q0 Q24 16 128 *)
  0x6eb9b400;       (* arm_SQRDMULH_VEC Q0 Q0 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5600;       (* arm_SLI_VEC Q0 Q16 10 128 32 *)
  0x4e986810;       (* arm_TRN2 Q16 Q0 Q24 32 128 *)
  0x6f545600;       (* arm_SLI_VEC Q0 Q16 20 128 64 *)
  0x4e1a0000;       (* arm_TBL Q0 [Q0] Q26 128 *)
  0x4e586830;       (* arm_TRN2 Q16 Q1 Q24 16 128 *)
  0x4e582821;       (* arm_TRN1 Q1 Q1 Q24 16 128 *)
  0x6eb9b421;       (* arm_SQRDMULH_VEC Q1 Q1 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5601;       (* arm_SLI_VEC Q1 Q16 10 128 32 *)
  0x4e986830;       (* arm_TRN2 Q16 Q1 Q24 32 128 *)
  0x6f545601;       (* arm_SLI_VEC Q1 Q16 20 128 64 *)
  0x4e1a0021;       (* arm_TBL Q1 [Q1] Q26 128 *)
  0x4e586850;       (* arm_TRN2 Q16 Q2 Q24 16 128 *)
  0x4e582842;       (* arm_TRN1 Q2 Q2 Q24 16 128 *)
  0x6eb9b442;       (* arm_SQRDMULH_VEC Q2 Q2 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5602;       (* arm_SLI_VEC Q2 Q16 10 128 32 *)
  0x4e986850;       (* arm_TRN2 Q16 Q2 Q24 32 128 *)
  0x6f545602;       (* arm_SLI_VEC Q2 Q16 20 128 64 *)
  0x4e1a0042;       (* arm_TBL Q2 [Q2] Q26 128 *)
  0x4e586870;       (* arm_TRN2 Q16 Q3 Q24 16 128 *)
  0x4e582863;       (* arm_TRN1 Q3 Q3 Q24 16 128 *)
  0x6eb9b463;       (* arm_SQRDMULH_VEC Q3 Q3 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5603;       (* arm_SLI_VEC Q3 Q16 10 128 32 *)
  0x4e986870;       (* arm_TRN2 Q16 Q3 Q24 32 128 *)
  0x6f545603;       (* arm_SLI_VEC Q3 Q16 20 128 64 *)
  0x4e1a0063;       (* arm_TBL Q3 [Q3] Q26 128 *)
  0x4e586890;       (* arm_TRN2 Q16 Q4 Q24 16 128 *)
  0x4e582884;       (* arm_TRN1 Q4 Q4 Q24 16 128 *)
  0x6eb9b484;       (* arm_SQRDMULH_VEC Q4 Q4 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5604;       (* arm_SLI_VEC Q4 Q16 10 128 32 *)
  0x4e986890;       (* arm_TRN2 Q16 Q4 Q24 32 128 *)
  0x6f545604;       (* arm_SLI_VEC Q4 Q16 20 128 64 *)
  0x4e1a0084;       (* arm_TBL Q4 [Q4] Q26 128 *)
  0x4e5868b0;       (* arm_TRN2 Q16 Q5 Q24 16 128 *)
  0x4e5828a5;       (* arm_TRN1 Q5 Q5 Q24 16 128 *)
  0x6eb9b4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5605;       (* arm_SLI_VEC Q5 Q16 10 128 32 *)
  0x4e9868b0;       (* arm_TRN2 Q16 Q5 Q24 32 128 *)
  0x6f545605;       (* arm_SLI_VEC Q5 Q16 20 128 64 *)
  0x4e1a00a5;       (* arm_TBL Q5 [Q5] Q26 128 *)
  0x4e5868d0;       (* arm_TRN2 Q16 Q6 Q24 16 128 *)
  0x4e5828c6;       (* arm_TRN1 Q6 Q6 Q24 16 128 *)
  0x6eb9b4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5606;       (* arm_SLI_VEC Q6 Q16 10 128 32 *)
  0x4e9868d0;       (* arm_TRN2 Q16 Q6 Q24 32 128 *)
  0x6f545606;       (* arm_SLI_VEC Q6 Q16 20 128 64 *)
  0x4e1a00c6;       (* arm_TBL Q6 [Q6] Q26 128 *)
  0x4e5868f0;       (* arm_TRN2 Q16 Q7 Q24 16 128 *)
  0x4e5828e7;       (* arm_TRN1 Q7 Q7 Q24 16 128 *)
  0x6eb9b4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5607;       (* arm_SLI_VEC Q7 Q16 10 128 32 *)
  0x4e9868f0;       (* arm_TRN2 Q16 Q7 Q24 32 128 *)
  0x6f545607;       (* arm_SLI_VEC Q7 Q16 20 128 64 *)
  0x4e1a00e7;       (* arm_TBL Q7 [Q7] Q26 128 *)
  0x6e0750d1;       (* arm_EXT Q17 Q6 Q7 80 *)
  0x4c9f7000;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7001;       (* arm_STR Q1 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7002;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7003;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7004;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7005;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7006;       (* arm_STR Q6 X0 (Postimmediate_Offset (word 16)) *)
  0xd1003000;       (* arm_SUB X0 X0 (rvalue (word 12)) *)
  0x4c9f7011;       (* arm_STR Q17 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc04020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 256)) *)
  0x3dc04421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 272)) *)
  0x3dc04822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 288)) *)
  0x3dc04c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 304)) *)
  0x3dc05024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 320)) *)
  0x3dc05425;       (* arm_LDR Q5 X1 (Immediate_Offset (word 336)) *)
  0x3dc05826;       (* arm_LDR Q6 X1 (Immediate_Offset (word 352)) *)
  0x3dc05c27;       (* arm_LDR Q7 X1 (Immediate_Offset (word 368)) *)
  0x4e586810;       (* arm_TRN2 Q16 Q0 Q24 16 128 *)
  0x4e582800;       (* arm_TRN1 Q0 Q0 Q24 16 128 *)
  0x6eb9b400;       (* arm_SQRDMULH_VEC Q0 Q0 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5600;       (* arm_SLI_VEC Q0 Q16 10 128 32 *)
  0x4e986810;       (* arm_TRN2 Q16 Q0 Q24 32 128 *)
  0x6f545600;       (* arm_SLI_VEC Q0 Q16 20 128 64 *)
  0x4e1a0000;       (* arm_TBL Q0 [Q0] Q26 128 *)
  0x4e586830;       (* arm_TRN2 Q16 Q1 Q24 16 128 *)
  0x4e582821;       (* arm_TRN1 Q1 Q1 Q24 16 128 *)
  0x6eb9b421;       (* arm_SQRDMULH_VEC Q1 Q1 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5601;       (* arm_SLI_VEC Q1 Q16 10 128 32 *)
  0x4e986830;       (* arm_TRN2 Q16 Q1 Q24 32 128 *)
  0x6f545601;       (* arm_SLI_VEC Q1 Q16 20 128 64 *)
  0x4e1a0021;       (* arm_TBL Q1 [Q1] Q26 128 *)
  0x4e586850;       (* arm_TRN2 Q16 Q2 Q24 16 128 *)
  0x4e582842;       (* arm_TRN1 Q2 Q2 Q24 16 128 *)
  0x6eb9b442;       (* arm_SQRDMULH_VEC Q2 Q2 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5602;       (* arm_SLI_VEC Q2 Q16 10 128 32 *)
  0x4e986850;       (* arm_TRN2 Q16 Q2 Q24 32 128 *)
  0x6f545602;       (* arm_SLI_VEC Q2 Q16 20 128 64 *)
  0x4e1a0042;       (* arm_TBL Q2 [Q2] Q26 128 *)
  0x4e586870;       (* arm_TRN2 Q16 Q3 Q24 16 128 *)
  0x4e582863;       (* arm_TRN1 Q3 Q3 Q24 16 128 *)
  0x6eb9b463;       (* arm_SQRDMULH_VEC Q3 Q3 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5603;       (* arm_SLI_VEC Q3 Q16 10 128 32 *)
  0x4e986870;       (* arm_TRN2 Q16 Q3 Q24 32 128 *)
  0x6f545603;       (* arm_SLI_VEC Q3 Q16 20 128 64 *)
  0x4e1a0063;       (* arm_TBL Q3 [Q3] Q26 128 *)
  0x4e586890;       (* arm_TRN2 Q16 Q4 Q24 16 128 *)
  0x4e582884;       (* arm_TRN1 Q4 Q4 Q24 16 128 *)
  0x6eb9b484;       (* arm_SQRDMULH_VEC Q4 Q4 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5604;       (* arm_SLI_VEC Q4 Q16 10 128 32 *)
  0x4e986890;       (* arm_TRN2 Q16 Q4 Q24 32 128 *)
  0x6f545604;       (* arm_SLI_VEC Q4 Q16 20 128 64 *)
  0x4e1a0084;       (* arm_TBL Q4 [Q4] Q26 128 *)
  0x4e5868b0;       (* arm_TRN2 Q16 Q5 Q24 16 128 *)
  0x4e5828a5;       (* arm_TRN1 Q5 Q5 Q24 16 128 *)
  0x6eb9b4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5605;       (* arm_SLI_VEC Q5 Q16 10 128 32 *)
  0x4e9868b0;       (* arm_TRN2 Q16 Q5 Q24 32 128 *)
  0x6f545605;       (* arm_SLI_VEC Q5 Q16 20 128 64 *)
  0x4e1a00a5;       (* arm_TBL Q5 [Q5] Q26 128 *)
  0x4e5868d0;       (* arm_TRN2 Q16 Q6 Q24 16 128 *)
  0x4e5828c6;       (* arm_TRN1 Q6 Q6 Q24 16 128 *)
  0x6eb9b4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5606;       (* arm_SLI_VEC Q6 Q16 10 128 32 *)
  0x4e9868d0;       (* arm_TRN2 Q16 Q6 Q24 32 128 *)
  0x6f545606;       (* arm_SLI_VEC Q6 Q16 20 128 64 *)
  0x4e1a00c6;       (* arm_TBL Q6 [Q6] Q26 128 *)
  0x4e5868f0;       (* arm_TRN2 Q16 Q7 Q24 16 128 *)
  0x4e5828e7;       (* arm_TRN1 Q7 Q7 Q24 16 128 *)
  0x6eb9b4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5607;       (* arm_SLI_VEC Q7 Q16 10 128 32 *)
  0x4e9868f0;       (* arm_TRN2 Q16 Q7 Q24 32 128 *)
  0x6f545607;       (* arm_SLI_VEC Q7 Q16 20 128 64 *)
  0x4e1a00e7;       (* arm_TBL Q7 [Q7] Q26 128 *)
  0x6e0750d1;       (* arm_EXT Q17 Q6 Q7 80 *)
  0x4c9f7000;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7001;       (* arm_STR Q1 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7002;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7003;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7004;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7005;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7006;       (* arm_STR Q6 X0 (Postimmediate_Offset (word 16)) *)
  0xd1003000;       (* arm_SUB X0 X0 (rvalue (word 12)) *)
  0x4c9f7011;       (* arm_STR Q17 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc06020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 384)) *)
  0x3dc06421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 400)) *)
  0x3dc06822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 416)) *)
  0x3dc06c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 432)) *)
  0x3dc07024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 448)) *)
  0x3dc07425;       (* arm_LDR Q5 X1 (Immediate_Offset (word 464)) *)
  0x3dc07826;       (* arm_LDR Q6 X1 (Immediate_Offset (word 480)) *)
  0x3dc07c27;       (* arm_LDR Q7 X1 (Immediate_Offset (word 496)) *)
  0x4e586810;       (* arm_TRN2 Q16 Q0 Q24 16 128 *)
  0x4e582800;       (* arm_TRN1 Q0 Q0 Q24 16 128 *)
  0x6eb9b400;       (* arm_SQRDMULH_VEC Q0 Q0 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5600;       (* arm_SLI_VEC Q0 Q16 10 128 32 *)
  0x4e986810;       (* arm_TRN2 Q16 Q0 Q24 32 128 *)
  0x6f545600;       (* arm_SLI_VEC Q0 Q16 20 128 64 *)
  0x4e1a0000;       (* arm_TBL Q0 [Q0] Q26 128 *)
  0x4e586830;       (* arm_TRN2 Q16 Q1 Q24 16 128 *)
  0x4e582821;       (* arm_TRN1 Q1 Q1 Q24 16 128 *)
  0x6eb9b421;       (* arm_SQRDMULH_VEC Q1 Q1 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5601;       (* arm_SLI_VEC Q1 Q16 10 128 32 *)
  0x4e986830;       (* arm_TRN2 Q16 Q1 Q24 32 128 *)
  0x6f545601;       (* arm_SLI_VEC Q1 Q16 20 128 64 *)
  0x4e1a0021;       (* arm_TBL Q1 [Q1] Q26 128 *)
  0x4e586850;       (* arm_TRN2 Q16 Q2 Q24 16 128 *)
  0x4e582842;       (* arm_TRN1 Q2 Q2 Q24 16 128 *)
  0x6eb9b442;       (* arm_SQRDMULH_VEC Q2 Q2 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5602;       (* arm_SLI_VEC Q2 Q16 10 128 32 *)
  0x4e986850;       (* arm_TRN2 Q16 Q2 Q24 32 128 *)
  0x6f545602;       (* arm_SLI_VEC Q2 Q16 20 128 64 *)
  0x4e1a0042;       (* arm_TBL Q2 [Q2] Q26 128 *)
  0x4e586870;       (* arm_TRN2 Q16 Q3 Q24 16 128 *)
  0x4e582863;       (* arm_TRN1 Q3 Q3 Q24 16 128 *)
  0x6eb9b463;       (* arm_SQRDMULH_VEC Q3 Q3 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5603;       (* arm_SLI_VEC Q3 Q16 10 128 32 *)
  0x4e986870;       (* arm_TRN2 Q16 Q3 Q24 32 128 *)
  0x6f545603;       (* arm_SLI_VEC Q3 Q16 20 128 64 *)
  0x4e1a0063;       (* arm_TBL Q3 [Q3] Q26 128 *)
  0x4e586890;       (* arm_TRN2 Q16 Q4 Q24 16 128 *)
  0x4e582884;       (* arm_TRN1 Q4 Q4 Q24 16 128 *)
  0x6eb9b484;       (* arm_SQRDMULH_VEC Q4 Q4 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5604;       (* arm_SLI_VEC Q4 Q16 10 128 32 *)
  0x4e986890;       (* arm_TRN2 Q16 Q4 Q24 32 128 *)
  0x6f545604;       (* arm_SLI_VEC Q4 Q16 20 128 64 *)
  0x4e1a0084;       (* arm_TBL Q4 [Q4] Q26 128 *)
  0x4e5868b0;       (* arm_TRN2 Q16 Q5 Q24 16 128 *)
  0x4e5828a5;       (* arm_TRN1 Q5 Q5 Q24 16 128 *)
  0x6eb9b4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5605;       (* arm_SLI_VEC Q5 Q16 10 128 32 *)
  0x4e9868b0;       (* arm_TRN2 Q16 Q5 Q24 32 128 *)
  0x6f545605;       (* arm_SLI_VEC Q5 Q16 20 128 64 *)
  0x4e1a00a5;       (* arm_TBL Q5 [Q5] Q26 128 *)
  0x4e5868d0;       (* arm_TRN2 Q16 Q6 Q24 16 128 *)
  0x4e5828c6;       (* arm_TRN1 Q6 Q6 Q24 16 128 *)
  0x6eb9b4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5606;       (* arm_SLI_VEC Q6 Q16 10 128 32 *)
  0x4e9868d0;       (* arm_TRN2 Q16 Q6 Q24 32 128 *)
  0x6f545606;       (* arm_SLI_VEC Q6 Q16 20 128 64 *)
  0x4e1a00c6;       (* arm_TBL Q6 [Q6] Q26 128 *)
  0x4e5868f0;       (* arm_TRN2 Q16 Q7 Q24 16 128 *)
  0x4e5828e7;       (* arm_TRN1 Q7 Q7 Q24 16 128 *)
  0x6eb9b4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q25 32 128 *)
  0x6eb9b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 32 128 *)
  0x6f2a5607;       (* arm_SLI_VEC Q7 Q16 10 128 32 *)
  0x4e9868f0;       (* arm_TRN2 Q16 Q7 Q24 32 128 *)
  0x6f545607;       (* arm_SLI_VEC Q7 Q16 20 128 64 *)
  0x4e1a00e7;       (* arm_TBL Q7 [Q7] Q26 128 *)
  0x6e0750d1;       (* arm_EXT Q17 Q6 Q7 80 *)
  0x4c9f7000;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7001;       (* arm_STR Q1 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7002;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7003;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7004;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7005;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
  0xd1001800;       (* arm_SUB X0 X0 (rvalue (word 6)) *)
  0x4c9f7006;       (* arm_STR Q6 X0 (Postimmediate_Offset (word 16)) *)
  0xd1003000;       (* arm_SUB X0 X0 (rvalue (word 12)) *)
  0x4c9f7011;       (* arm_STR Q17 X0 (Postimmediate_Offset (word 16)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLKEM_POLY_COMPRESS_D10_EXEC = ARM_MK_EXEC_RULE mlkem_poly_compress_d10_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_COMPRESS_D10_MC =
  REWRITE_CONV[mlkem_poly_compress_d10_mc] `LENGTH mlkem_poly_compress_d10_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_COMPRESS_D10_PREAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D10_PREAMBLE_LENGTH = 0`;;

let MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH = 4`;;

let MLKEM_POLY_COMPRESS_D10_CORE_START = new_definition
  `MLKEM_POLY_COMPRESS_D10_CORE_START = MLKEM_POLY_COMPRESS_D10_PREAMBLE_LENGTH`;;

let MLKEM_POLY_COMPRESS_D10_CORE_END = new_definition
  `MLKEM_POLY_COMPRESS_D10_CORE_END =
   LENGTH mlkem_poly_compress_d10_mc - MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_COMPRESS_D10_MC;
               MLKEM_POLY_COMPRESS_D10_CORE_START;
               MLKEM_POLY_COMPRESS_D10_CORE_END;
               MLKEM_POLY_COMPRESS_D10_PREAMBLE_LENGTH;
               MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* compress: per-coefficient formula.                                        *)
(*                                                                           *)
(* TRN1/TRN2 against zero put each coefficient x, zero-extended, into a      *)
(* 32-bit lane, and SQRDMULH by 660565712 computes compress_d10_aarch64 x    *)
(* there; the definition is stated in the form that the symbolic simulation  *)
(* produces, so that SIMD_SIMPLIFY_TAC can fold it. The packing keeps only   *)
(* the low 10 bits of each lane.                                             *)
(* ------------------------------------------------------------------------- *)

let compress_d10_aarch64 = new_definition
 `compress_d10_aarch64 (x:int16) : int32 =
  iword_saturate((&2 * ival(word_join (word 0:int16) x : int32) * &660565712 +
                  &2147483648) div &4294967296)`;;

(* The low 10 bits of compress_d10_aarch64 x are compress_d10 x for all
 * x in [0, 3328]; checked for each of the 3329 values. *)
let COMPRESS_D10_AARCH64_CORRECT = PROVE_BY_COEFF_ENUMERATION
  [compress_d10_aarch64; compress_d10]
  `!x:int16. val x < 3329
             ==> word_subword (compress_d10_aarch64 x) (0,10) : 10 word =
                 compress_d10 x`;;

(* ------------------------------------------------------------------------- *)
(* pack and compact: 4 coefficients in bytes 0..4 of a 64-bit lane.          *)
(*                                                                           *)
(* With y0, ..., y3 the 32-bit lanes after compress (y0, y2 in one vector,   *)
(* y1, y3 in the other), the code computes                                   *)
(*                                                                           *)
(*   32-bit lanes: p = (y1 << 10) | (y0 & 0x3ff)              (pair_d10)     *)
(*   64-bit lanes: g = (p1 << 20) | (p0 & 0xfffff)            (group_d10)    *)
(*                                                                           *)
(* WORD_AND_JOIN_1048575 rewrites the masking of a joined 64-bit lane, which *)
(* otherwise copies p1 into the result of the second SLI. The byte lemmas    *)
(* show that bytes 0..4 of a group, the only ones that TBL moves into the    *)
(* output, are the bytes of the 40-bit word that joins the low 10 bits of    *)
(* y0, ..., y3. They hold for any 32-bit y0, ..., y3: bit 10 of y3, set if   *)
(* the coefficient is 1024, ends up in bit 40 of the lane, which is not      *)
(* stored.                                                                   *)
(* ------------------------------------------------------------------------- *)

let pair_d10 = new_definition
 `pair_d10 (y0:int32) (y1:int32) : int32 =
  word_or (word_shl y1 10) (word_and y0 (word 1023))`;;

let group_d10 = new_definition
 `group_d10 (p0:int32) (p1:int32) : int64 =
  word_or (word_shl (word_join (word 0:int32) p1) 20)
          (word_zx (word_and p0 (word 1048575)))`;;

let WORD_AND_JOIN_1048575 = WORD_BLAST
 `!(h:int32) (l:int32).
        word_and (word_join h l : int64) (word 1048575) =
        word_zx (word_and l (word 1048575))`;;

let GROUP_D10_BYTES =
  let mk t =
    let pos = mk_small_numeral (8 * t) in
    let tm = subst [pos,`p:num`]
     `!y0 y1 y2 y3.
        word_subword (group_d10 (pair_d10 y0 y1) (pair_d10 y2 y3)) (p,8):byte =
        word_subword
         (word_join
           (word_join (word_subword (y3:int32) (0,10):10 word)
                      (word_subword (y2:int32) (0,10):10 word):20 word)
           (word_join (word_subword (y1:int32) (0,10):10 word)
                      (word_subword (y0:int32) (0,10):10 word):20 word):40 word)
         (p,8)` in
    prove(tm, REWRITE_TAC[group_d10; pair_d10] THEN CONV_TAC WORD_BLAST) in
  map mk (0--4);;

(* Everything SIMD_SIMPLIFY_TAC should fold or rewrite after each step *)
let COMPRESS_D10_SIMPS =
  [compress_d10_aarch64; pair_d10; group_d10] @
  map GSYM ([WORD_AND_JOIN_1048575] @ GROUP_D10_BYTES);;

(* ------------------------------------------------------------------------- *)
(* Overlapping stores.                                                       *)
(*                                                                           *)
(* The 16-byte stores of the output overlap: the store at byte 10k of a      *)
(* block is followed by one at byte 10k + 10, which overwrites its last 6    *)
(* bytes. The symbolic simulation drops every memory assumption that it      *)
(* cannot show to be disjoint from a store, so a whole 16-byte assumption    *)
(* would be lost. STORE_SPLIT_MERGE_TAC therefore splits each new store      *)
(* into bytes after the step that performs it; a later store then only       *)
(* drops the bytes it overwrites. The stores are in increasing address       *)
(* order, so the bytes below the latest store are final; to keep the number  *)
(* of assumptions, and the cost of each later step, small, runs of 4 final   *)
(* bytes are merged into one bytes32 assumption. No store writes 4 bytes, so *)
(* merged assumptions are not mistaken for new stores. At the end,           *)
(* SPLIT_MERGED_BYTES_TAC splits them into bytes again.                      *)
(* ------------------------------------------------------------------------- *)

let STORE_SPLIT_MERGE_TAC base simps =
  let pat128 = `read (memory :> bytes128 a) s = x`
  and pat64 = `read (memory :> bytes64 a) s = x`
  and pat8 = `read (memory :> bytes8 a) s = x` in
  let offset_of tm =
    if tm = base then Some 0 else
    try let l,r = dest_binop `word_add:int64->int64->int64` tm in
        if l = base then Some (dest_small_numeral (rand r)) else None
    with Failure _ -> None in
  let addr_of th = rand(rand(rand(rator(lhand(concl th))))) in
  let is_out pat th =
    can (term_match [] pat) (concl th) &&
    (match offset_of (addr_of th) with Some _ -> true | None -> false) in
  let split th =
    let n = if can (term_match [] pat128) (concl th) then 4 else 3 in
    let th' = CONV_RULE (READ_MEMORY_SPLIT_CONV n) th in
    map (CONV_RULE (RAND_CONV (SIMD_SIMPLIFY_CONV simps))) (CONJUNCTS th') in
  let mk_addr k =
    if k = 0 then base
    else mk_binop `word_add:int64->int64->int64` base
           (mk_comb(`word:num->int64`, mk_small_numeral k)) in
  let merge_tac limit (asl,w) =
    let bytes = mapfilter (fun (_,th) ->
      if is_out pat8 th then
        (match offset_of (addr_of th) with Some k -> (k,th) | None -> fail())
      else fail()) asl in
    let final = filter (fun (k,_) -> k < limit) bytes in
    let rec runs ks acc =
      match ks with
        [] -> rev acc
      | k::_ ->
          let run = map (fun i -> k + i) (0--3) in
          if forall (fun i -> mem i ks) run
          then runs (filter (fun i -> not (mem i run)) ks) (k::acc)
          else runs (tl ks) acc in
    let starts = runs (sort (<) (map fst final)) [] in
    let merge1 k =
      let ths = map (fun i -> assoc (k + i) final) (0--3) in
      let s = rand(lhand(concl(hd ths))) in
      let rd = list_mk_icomb "read"
                 [mk_icomb(mk_icomb(`(:>):(armstate,(64)word->byte)component->
                             ((64)word->byte,int32)component->
                             (armstate,int32)component`, `memory`),
                           mk_comb(`bytes32`, mk_addr k)); s] in
      let mth = READ_MEMORY_MERGE_CONV 2 rd in
      let mth' = GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) ths mth in
      mth', map concl ths in
    let merged = map merge1 starts in
    (MAP_EVERY (fun (th,tms) ->
       MP_TAC th THEN
       MAP_EVERY (fun tm -> UNDISCH_THEN tm (K ALL_TAC)) tms THEN
       DISCH_TAC) merged) (asl,w) in
  fun (asl,w) ->
    let stores = filter (fun (_,th) -> is_out pat128 th || is_out pat64 th) asl in
    if stores = [] then ALL_TAC (asl,w) else
    let limit = itlist (fun (_,th) m ->
                  match offset_of (addr_of th) with Some k -> max k m | None -> m)
                stores 0 in
    (MAP_EVERY (fun (_,th) ->
       UNDISCH_THEN (concl th) (fun th -> MAP_EVERY ASSUME_TAC (split th)))
       stores THEN
     merge_tac limit) (asl,w);;

let SPLIT_MERGED_BYTES_TAC base simps =
  let pat32 = `read (memory :> bytes32 a) s = x` in
  let offset_ok tm =
    tm = base ||
    (try fst(dest_binop `word_add:int64->int64->int64` tm) = base
     with Failure _ -> false) in
  let is_out th =
    can (term_match [] pat32) (concl th) &&
    offset_ok (rand(rand(rand(rator(lhand(concl th)))))) in
  REPEAT (FIRST_X_ASSUM (fun th ->
    if is_out th then
      MAP_EVERY (ASSUME_TAC o CONV_RULE (RAND_CONV (SIMD_SIMPLIFY_CONV simps)))
        (CONJUNCTS (CONV_RULE (READ_MEMORY_SPLIT_CONV 2) th))
    else failwith "SPLIT_MERGED_BYTES_TAC"));;

(* ------------------------------------------------------------------------- *)
(* Output layout.                                                            *)
(*                                                                           *)
(* The expected output is written as 32 words of 80 bits, one for each 8     *)
(* coefficients, and each word is split into its 10 bytes, which are then    *)
(* compared with the byte assumptions.                                       *)
(* ------------------------------------------------------------------------- *)

(* Generic: for an n-bit word w with n = m * k, val w is the number formed by
 * the k m-bit subwords of w, as a little-endian word list. *)
let mk_val_as_wordlist n m =
  let k = n / m in
  let s = Printf.sprintf in
  let w = s "(w:%d word)" n in
  let ls_def = s "list_of_seq (\\i. word_subword %s (%d * i,%d):%d word) %d"
                 w m m m k in
  let tm = parse_term (s "!w:%d word. val w = num_of_wordlist (%s)" n ls_def) in
  let ls = s "(ls:(%d word)list)" m in
  let n_ty = mk_finty (Num.num_of_int n)
  and m_ty = mk_finty (Num.num_of_int m) in
  let th = prove(tm,
    GEN_TAC THEN
    ABBREV_TAC (parse_term (s "%s = %s" ls ls_def)) THEN
    SUBGOAL_THEN (parse_term (s "LENGTH %s = %d" ls k)) ASSUME_TAC THENL
     [EXPAND_TAC "ls" THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
    SUBGOAL_THEN (parse_term (s "(word (num_of_wordlist %s) : %d word) = %s"
                                ls n w))
    MP_TAC THENL
     [MP_TAC(ISPECL [parse_term (s "(word (num_of_wordlist %s) : %d word)"
                                   ls n);
                     parse_term w]
        (INST [mk_small_numeral m,`l:num`; mk_small_numeral k,`k:num`]
          (INST_TYPE [n_ty,`:N`; m_ty,`:M`] WORD_PACKED_EQ))) THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [parse_term ls; `i:num`]
        (INST_TYPE [n_ty,`:KL`; m_ty,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST)) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN
      EXPAND_TAC "ls" THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC VAL_WORD_EXACT THEN
      MP_TAC(ISPEC (parse_term ls) NUM_OF_WORDLIST_BOUND_LENGTH) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV]) in
  CONV_RULE(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV THENC
            DEPTH_CONV BETA_CONV THENC DEPTH_CONV NUM_MULT_CONV) th;;

(* Generic: for an n-bit word w, reading w at address a is reading its
 * n / 8 bytes at a, a + 1, ... *)
let mk_wbytes_split n =
  let k = n / 8 in
  let s = Printf.sprintf in
  let vth = mk_val_as_wordlist n 8 in
  let tm = parse_term (s
    "!(a:int64) (s:armstate) (w:%d word).
       read (memory :> wbytes a) s = w <=>
       read (memory :> bytes(a,%d)) s = val w" n k) in
  let th1 = prove(tm,
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV) in
  let th2 = REWRITE_RULE[vth] th1 in
  let th3 = GEN_ALL(CONV_RULE(RAND_CONV
              BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) (SPEC_ALL th2)) in
  REWRITE_RULE[GSYM BYTES8_WBYTES] th3;;

let WBYTES80_SPLIT = mk_wbytes_split 80;;

let SUBWORD_SIMP_CONV =
  TOP_DEPTH_CONV (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D10_CORRECT = prove
 (`!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,320))
            [(word pc,LENGTH mlkem_poly_compress_d10_mc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_compress_d10_mc /\
                  read PC s = word (pc + MLKEM_POLY_COMPRESS_D10_CORE_START) /\
                  C_ARGUMENTS [r;a] s /\
                  LENGTH l = 256 /\
                  (!i. i < 256
                       ==> &0 <= ival (EL i l) /\ ival (EL i l) <= &3328) /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + MLKEM_POLY_COMPRESS_D10_CORE_END) /\
                  read(memory :> bytes(r,320)) s =
                    num_of_wordlist (MAP compress_d10 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Restate the input bound in terms of val ***)

  SUBGOAL_THEN `!i. i < 256 ==> val (EL i (l:int16 list)) < 3329`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IVAL_VAL; DIMINDEX_16; bitval; BIT_VAL] THEN
    MP_TAC(ISPEC `EL i (l:int16 list)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Digitize the input to match the 128-bit loads ***)

  POLY_BYTES128_TAC
   `read(memory :> bytes(a,512)) s0 = num_of_wordlist(l:int16 list)` THEN

  (*** Simulate to the end, folding compress and pack, splitting stores ***)

  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLKEM_POLY_COMPRESS_D10_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC COMPRESS_D10_SIMPS THEN
    STORE_SPLIT_MERGE_TAC `r:int64` COMPRESS_D10_SIMPS) 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Keep only the output bytes ***)

  DISCARD_NONMATCHING_ASSUMPTIONS
   [`read (memory :> bytes8 a) s = x`;
    `read (memory :> bytes32 a) s = x`;
    `!i. i < 256 ==> val (EL i (l:int16 list)) < 3329`;
    `LENGTH (l:int16 list) = 256`] THEN
  SPLIT_MERGED_BYTES_TAC `r:int64` COMPRESS_D10_SIMPS THEN

  (*** Replace compress_d10 by the low 10 bits of compress_d10_aarch64 ***)

  SUBGOAL_THEN
   `MAP compress_d10 (l:int16 list) =
    MAP (\x. word_subword (compress_d10_aarch64 x) (0,10)) l`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MAP] THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC COMPRESS_D10_AARCH64_CORRECT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN

  (*** Spell out the output as 32 words of 80 bits, then as bytes ***)

  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
  ASM_SIMP_TAC[EL_MAP; ARITH] THEN
  REPLICATE_TAC 3
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[WBYTES80_SPLIT] THEN
  CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN

  (*** Compare each byte ***)

  CONV_TAC SUBWORD_SIMP_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/aarch64/src/arith_native_aarch64.h *)

let MLKEM_POLY_COMPRESS_D10_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,320))
            [(word pc,LENGTH mlkem_poly_compress_d10_mc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_poly_compress_d10_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  LENGTH l = 256 /\
                  (!i. i < 256
                       ==> &0 <= ival (EL i l) /\ ival (EL i l) <= &3328) /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes(r,320)) s =
                    num_of_wordlist (MAP compress_d10 l))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_POLY_COMPRESS_D10_EXEC
   (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D10_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "mlkem_native/aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_poly_compress_d10" subroutine_signatures)
    MLKEM_POLY_COMPRESS_D10_SUBROUTINE_CORRECT
    MLKEM_POLY_COMPRESS_D10_EXEC;;

let MLKEM_POLY_COMPRESS_D10_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,320))
               [word pc,LENGTH mlkem_poly_compress_d10_mc; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_poly_compress_d10_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,320] [r,320])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_POLY_COMPRESS_D10_EXEC);;
