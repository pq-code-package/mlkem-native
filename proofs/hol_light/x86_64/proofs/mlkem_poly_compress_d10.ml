(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 10 bits.                        *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
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

(* TODO: Prove correctness of poly_compress_d10_avx2 *)
