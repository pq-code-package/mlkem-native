(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 10 bits.                        *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "x86_64/proofs/mlkem_compress_common.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d10.o";; *)

let mlkem_poly_compress_d10_mc =
  define_assert_from_elf "mlkem_poly_compress_d10_mc" "x86_64/mlkem/mlkem_poly_compress_d10.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xf5; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm1) (%_% ymm0) (Imm8 (word 3)) *)
  0xb8; 0x0f; 0x00; 0x0f; 0x00;
                           (* MOV (% eax) (Imm32 (word 983055)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0x00; 0x10; 0x00; 0x10;
                           (* MOV (% eax) (Imm32 (word 268439552)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xb8; 0xff; 0x03; 0xff; 0x03;
                           (* MOV (% eax) (Imm32 (word 67044351)) *)
  0xc5; 0xf9; 0x6e; 0xe0;  (* VMOVD (%_% xmm4) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x04; 0x01; 0x00; 0x00; 0x04;
                           (* MOV (% rax) (Imm64 (word 288230380513787905)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xe8;
                           (* VMOVQ (%_% xmm5) (% rax) *)
  0xc4; 0xe2; 0x7d; 0x59; 0xed;
                           (* VPBROADCASTQ (%_% ymm5) (%_% xmm5) *)
  0xb8; 0x0c; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 12)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xf0;
                           (* VMOVQ (%_% xmm6) (% rax) *)
  0xc4; 0xe2; 0x7d; 0x59; 0xf6;
                           (* VPBROADCASTQ (%_% ymm6) (%_% xmm6) *)
  0xc5; 0xfd; 0x6f; 0x3a;  (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x06;  (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x07;  (* VMOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x4f; 0x10;
                           (* VMOVD (Memop Doubleword (%% (rdi,16))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x20;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x47; 0x14;
                           (* VMOVDQU (Memop Word128 (%% (rdi,20))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x4f; 0x24;
                           (* VMOVD (Memop Doubleword (%% (rdi,36))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x40;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x47; 0x28;
                           (* VMOVDQU (Memop Word128 (%% (rdi,40))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x4f; 0x38;
                           (* VMOVD (Memop Doubleword (%% (rdi,56))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x60;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x47; 0x3c;
                           (* VMOVDQU (Memop Word128 (%% (rdi,60))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x4f; 0x4c;
                           (* VMOVD (Memop Doubleword (%% (rdi,76))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x47; 0x50;
                           (* VMOVDQU (Memop Word128 (%% (rdi,80))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x4f; 0x60;
                           (* VMOVD (Memop Doubleword (%% (rdi,96))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x47; 0x64;
                           (* VMOVDQU (Memop Word128 (%% (rdi,100))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x4f; 0x74;
                           (* VMOVD (Memop Doubleword (%% (rdi,116))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x47; 0x78;
                           (* VMOVDQU (Memop Word128 (%% (rdi,120))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,136))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0x8c; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,140))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0x9c; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,156))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,160))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,176))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0xb4; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,180))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0xc4; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,196))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,200))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0xd8; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,216))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0xdc; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,220))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0xec; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,236))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0xf0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,240))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,256))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0x04; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,260))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0x14; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,276))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0x18; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,280))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,296))) (%_% xmm9) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0x3d; 0xd5; 0xc9;  (* VPMULLW (%_% ymm9) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xfd; 0xd2;  (* VPADDW (%_% ymm10) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x3d; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm8) (%_% ymm8) (Imm8 (word 3)) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x41; 0x35; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0x71; 0xd1; 0x0f;
                           (* VPSRLW (%_% ymm9) (%_% ymm9) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc1;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc3;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xdb; 0xc4;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xf5; 0xc5;  (* VPMADDWD (%_% ymm8) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x62; 0x3d; 0x47; 0xc6;
                           (* VPSLLVD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xd0; 0x0c;
                           (* VPSRLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 12)) *)
  0xc4; 0x62; 0x3d; 0x00; 0xc7;
                           (* VPSHUFB (%_% ymm8) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x43; 0x7d; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI128 (%_% xmm9) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x39; 0x0e; 0xc1; 0xe0;
                           (* VPBLENDW (%_% xmm8) (%_% xmm8) (%_% xmm9) (Imm8 (word 224)) *)
  0xc5; 0x7a; 0x7f; 0x87; 0x2c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,300))) (%_% xmm8) *)
  0xc5; 0x79; 0x7e; 0x8f; 0x3c; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,316))) (%_% xmm9) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_poly_compress_d10_tmc =
  define_trimmed "mlkem_poly_compress_d10_tmc" mlkem_poly_compress_d10_mc;;
let MLKEM_POLY_COMPRESS_D10_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_compress_d10_tmc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_COMPRESS_D10_MC =
  REWRITE_CONV[mlkem_poly_compress_d10_mc] `LENGTH mlkem_poly_compress_d10_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_COMPRESS_D10_TMC =
  REWRITE_CONV[mlkem_poly_compress_d10_tmc] `LENGTH mlkem_poly_compress_d10_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH = 1`;;

let MLKEM_POLY_COMPRESS_D10_CORE_END = new_definition
  `MLKEM_POLY_COMPRESS_D10_CORE_END =
   LENGTH mlkem_poly_compress_d10_tmc - MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_COMPRESS_D10_MC;
               LENGTH_MLKEM_POLY_COMPRESS_D10_TMC;
               MLKEM_POLY_COMPRESS_D10_CORE_END;
               MLKEM_POLY_COMPRESS_D10_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

let DIMINDEX_10 = DIMINDEX_CONV `dimindex (:10)`;;

(* ------------------------------------------------------------------------- *)
(* AVX2 implementation of compress_d10 as a word expression                  *)
(* ------------------------------------------------------------------------- *)

let compress_d10_avx2 = new_definition
  `compress_d10_avx2 (a:16 word) : 16 word =
   word_and
    (word_subword
      (word_add
        (word_ushr
          (word_mul
            (word_sx
              (word_sub
                (word_subword (word_mul (word_sx (word_shl a 3)) (word 20159) : 32 word) (16,16) : 16 word)
                (word_ushr
                  (word_and (word_not (word_mul a (word 30200)))
                    (word_sub (word_mul a (word 30200))
                      (word_add a (word 15))))
                  15)))
            (word 4096) : 32 word)
          14)
        (word 1) : 32 word)
      (1,16) : 16 word)
    (word 1023)`;;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for 10-bit compression                                      *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_1023 = WORD_BLAST
  `word_and (x : 16 word) (word 1023) =
   word_zx (word_subword x (0,10) : 10 word) : 16 word`;;

let MULADD_1024_JOIN = prove(
  `word_add (word_mul (word_sx (word_zx (x : 10 word) : 16 word) : 32 word) (word 1))
   (word_mul (word_sx (word_zx (y : 10 word) : 16 word) : 32 word) (word 1024)) =
   word_zx (word_join y x : 20 word) : 32 word`,
  BITBLAST_TAC);;

let DECOMPRESS_MULADD_1024_JOIN = prove(
  `word_add
    (word_mul (word_sx (compress_d10_avx2 x) : 32 word) (word 1))
    (word_mul (word_sx (compress_d10_avx2 y) : 32 word) (word 1024)) =
   word_zx (word_join (word_subword (compress_d10_avx2 y) (0,10) : 10 word)
                      (word_subword (compress_d10_avx2 x) (0,10) : 10 word) : 20 word) : 32 word`,
  REWRITE_TAC [compress_d10_avx2; WORD_AND_1023; MULADD_1024_JOIN; WORD_BLAST
    `!x:10 word. word_subword (word_zx x : 16 word) (0,10) : 10 word = x`]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the per-element compression formula                        *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_CORRECT = prove(
  `!(x : 16 word). val x < 3329 ==>
   compress_d10 x = word_subword (compress_d10_avx2 x) (0,10)`, 
  let CORE = prove(
    `!(x : num). x < 3329 ==>
     compress_d10 (word x) = word_subword (compress_d10_avx2 (word x)) (0,10)`,
    REWRITE_TAC[compress_d10; compress_d10_avx2] THEN
    BRUTE_FORCE_WITH (CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN CONV_TAC WORD_BLAST)) in
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `val(x:16 word)` CORE) THEN
  ASM_REWRITE_TAC[WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* Specialized WORD_PACKED_EQ for 160-bit words with 10-bit subwords         *)
(* ------------------------------------------------------------------------- *)

let WORD_PACKED_EQ_D10 = prove(
 `!(x:160 word) (y:160 word).
    (x = y <=>
     !i. i < 16
         ==> word_subword x (10*i, 10) : (10) word =
             word_subword y (10*i, 10))`,
  REPEAT GEN_TAC THEN
  MP_TAC(INST [`10`,`l:num`; `16`,`k:num`]
    (INST_TYPE [`:160`,`:N`; `:10`,`:M`] WORD_PACKED_EQ)) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Merge separate 128+32 memory reads into 160-bit word                      *)
(* ------------------------------------------------------------------------- *)

let READ_WBYTES_MERGE_128_32 = prove(
  `read (bytes128 a) s = x0 : 128 word ==>
   read (bytes32 (word_add a (word 16))) s = x1 : 32 word ==>
   read (wbytes a) s = (word_join x1 x0) : 160 word`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [READ_WBYTES_SPLIT_128_32] THEN
  NUM_REDUCE_TAC THEN
  REWRITE_TAC BASE_SIMPS_D10 THEN
  ASM_REWRITE_TAC [] THEN
  BITBLAST_TAC);;

let READ_MEMORY_WBYTES_MERGE_128_32 = prove(
  `read (memory :> bytes128 a) s = x0 : 128 word ==>
   read (memory :> bytes32 (word_add a (word 16))) s = x1 : 32 word ==>
   read (memory :> wbytes a) s = (word_join x1 x0) : 160 word`,
  REWRITE_TAC [READ_COMPONENT_COMPOSE] THEN
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC [READ_WBYTES_MERGE_128_32]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to combine 128+32 byte reads into 160-bit words                    *)
(* ------------------------------------------------------------------------- *)

type asm_info = { label: string; thm: thm; comp: string; addr: term; rhs: term };;

let COMBINE_WBYTES_160_TAC : tactic = fun (asl,w) ->
  let get_comp_addr_rhs tm =
    try let l = lhand tm and r = rand tm in
        let rd = rator l in
        let comp = snd(dest_binary ":>" (rand rd)) in
        let cname = fst(dest_const(rator comp)) in
        {label=""; thm=TRUTH; comp=cname; addr=rand comp; rhs=r}
    with _ -> {label=""; thm=TRUTH; comp=""; addr=`T`; rhs=`T`} in
  let get_base_offset addr =
    try let args = snd(strip_comb addr) in
        (hd args, Num.int_of_num(dest_numeral (rand (hd(tl args)))))
    with _ -> (addr, 0) in
  let mk_info s th =
    let i = get_comp_addr_rhs (concl th) in
    {i with label=s; thm=th} in
  let asms = map (fun a -> mk_info (fst a) (snd a)) asl in
  let b128s = filter (fun i -> i.comp = "bytes128") asms in
  let b32s  = filter (fun i -> i.comp = "bytes32") asms in
  let addr_matches base tgt i =
    let p = get_base_offset i.addr in fst p = base && snd p = tgt in
  let rec find_pair = function
    | [] -> failwith "COMBINE_WBYTES_160_TAC: no matching pair"
    | i128::rest ->
      let p = get_base_offset i128.addr in
      let base = fst p and off = snd p in
      (try
        let i32 = find (addr_matches base (off+16)) b32s in
        [i128; i32]
      with _ -> find_pair rest) in
  let pair = find_pair b128s in
  let i128 = el 0 pair and i32 = el 1 pair in
  let s_tm = rand(lhand(concl i128.thm)) in
  let lemma = INST [i128.addr,`a:int64`; s_tm,`s:x86state`;
                    i128.rhs,`x0:128 word`;
                    i32.rhs,`x1:32 word`] READ_MEMORY_WBYTES_MERGE_128_32 in
  let lemma' = CONV_RULE(DEPTH_CONV(CHANGED_CONV
    (REWRITE_CONV[WORD_ADD_ASSOC_CONSTS] THENC NUM_REDUCE_CONV))) lemma in
  let result = MP (MP lemma' i128.thm) i32.thm in
  let drop_thms = [i128.thm; i32.thm] in
  let asl' = filter (fun (_,th) -> not (mem th drop_thms)) asl in
  ASSUME_TAC result (asl',w);;

(* ------------------------------------------------------------------------- *)
(* Rewrite compress_d10_avx2 back to compress_d10                            *)
(* ------------------------------------------------------------------------- *)

let REWRITE_COMPRESS =
  let derive_instance thm tm =
    let thm' = PART_MATCH rand thm tm in
    MP thm' (EQT_ELIM(NUM_REDUCE_CONV (fst(dest_imp(concl thm')))))
  in
  (UNDISCH_THEN (`forall i. i < 256 ==> val (EL i (inlist : (16 word) list)) < 3329`) (fun thm ->
   RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (COND_REWRITE_CONV (derive_instance thm) (GSYM COMPRESS_D10_CORRECT))))
   THEN ASSUME_TAC thm
  ));;

let SIMPLIFY_WORD_ADD = RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV (COND_REWRITE_CONV WORD_BLAST WORD_ADD_OR)));;

(* ------------------------------------------------------------------------- *)
(* Main correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D10_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 320))
          [(word pc, LENGTH mlkem_poly_compress_d10_tmc); (a, 512); (data, 32)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_compress_d10_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d10_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = word (pc + MLKEM_POLY_COMPRESS_D10_CORE_END) /\
                read (memory :> bytes(r, 320)) s = num_of_wordlist (MAP compress_d10 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 320)] ,,
            MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10])`,

  MAP_EVERY X_GEN_TAC
    [`r:int64`; `a:int64`; `data:int64`; `inlist:(16 word) list`; `pc:num`] THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Move to 256-bit granular preconditions for input array *)
  UNDISCH_TAC `read(memory :> bytes(a,512)) (s0 : x86state) = num_of_wordlist(inlist: (16 word) list)` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
  REWRITE_TAC[] THEN
  REPLICATE_TAC 4
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN
  REPEAT STRIP_TAC THEN

  (* Move to 256-bit granular precondition for constant array *)
  UNDISCH_TAC
   `read(memory :> bytes(data,32)) s0 = num_of_wordlist ((MAP iword compress_d10_data) : (8 word) list)` THEN
  REWRITE_TAC [compress_d10_data; MAP] THEN
  REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                   [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN STRIP_TAC THEN

  SUBGOAL_THEN `!i. i < 256 ==> val (EL i (inlist:(16 word) list)) < 3329` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IVAL_VAL; DIMINDEX_16; bitval; BIT_VAL] THEN
    MP_TAC(ISPEC `EL i (inlist:(16 word) list)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Symbolic execution ***)
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_COMPRESS_D10_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC
    [GSYM WORD_JOIN_AND_TYBIT0; GSYM WORD_JOIN_NOT_TYBIT0; compress_d10_avx2;
     GSYM DECOMPRESS_MULADD_1024_JOIN; GSYM (CONV_RULE NUM_REDUCE_CONV BYTES128_JOIN); GSYM WORD_ZX_128_256_128; GSYM WORD_64_SUB_8_8_JOIN_16]) (1 -- 324) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_ADD_0]) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read ymm s = (t : 256 word)`] THEN

  REWRITE_COMPRESS THEN
  SIMPLIFY_WORD_ADD THEN

  REPEAT (COMBINE_WBYTES_160_TAC) THEN

  SUBGOAL_THEN `LENGTH (MAP compress_d10 (inlist : (16 word) list)) = 256` ASSUME_TAC THENL [ASM_SIMP_TAC [LENGTH_MAP]; ALL_TAC] THEN
  MAP_EVERY (fun i -> SUBGOAL_THEN (subst [mk_small_numeral (16 * i), `i: num`] `LENGTH (SUB_LIST (i, 16) (MAP compress_d10 (inlist : (16 word) list))) = 16`) ASSUME_TAC
      THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC]) (0 -- 15) THEN

  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_10_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read c s = (t : N word)`] THEN
  REPEAT CONJ_TAC THEN

  REWRITE_TAC [WORD_PACKED_EQ_D10] THEN
  CONV_TAC (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D10) THEN
  REPEAT CONJ_TAC THEN
  UNDISCH_THEN `LENGTH (MAP compress_d10 (inlist : (16 word) list)) = 256` (fun th ->
    CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  ASM_SIMP_TAC [EL_MAP; ARITH] THEN
  CONV_TAC WORD_BLAST
);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrappers                                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D10_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 320))
          [(word pc, LENGTH mlkem_poly_compress_d10_tmc); (a, 512); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d10_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d10_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 320)) s = num_of_wordlist (MAP compress_d10 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 320)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_compress_d10_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D10_CORRECT));;

let MLKEM_POLY_COMPRESS_D10_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 320))
          [(word pc, LENGTH mlkem_poly_compress_d10_mc); (a, 512); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d10_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d10_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 320)) s = num_of_wordlist (MAP compress_d10 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 320)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_COMPRESS_D10_NOIBT_SUBROUTINE_CORRECT));;

