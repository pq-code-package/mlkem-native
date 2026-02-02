(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 10 bits.                    *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d10.o";; *)

let mlkem_poly_decompress_d10_mc =
  define_assert_from_elf "mlkem_poly_decompress_d10_mc" "x86_64/mlkem/mlkem_poly_decompress_d10.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x04; 0x34; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218182660)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 4)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xc8;
                           (* VMOVQ (%_% xmm1) (% rax) *)
  0xc4; 0xe2; 0x7d; 0x59; 0xc9;
                           (* VPBROADCASTQ (%_% ymm1) (%_% xmm1) *)
  0xb8; 0xf8; 0x1f; 0xe0; 0x7f;
                           (* MOV (% eax) (Imm32 (word 2145394680)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xc5; 0xfd; 0x6f; 0x1a;  (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfa; 0x6f; 0x26;  (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,0))) *)
  0xc5; 0xf9; 0x6e; 0x6e; 0x10;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,16))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x27;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x14;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,20))) *)
  0xc5; 0xf9; 0x6e; 0x6e; 0x24;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,36))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x28;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,40))) *)
  0xc5; 0xf9; 0x6e; 0x6e; 0x38;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,56))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x3c;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,60))) *)
  0xc5; 0xf9; 0x6e; 0x6e; 0x4c;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,76))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x50;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,80))) *)
  0xc5; 0xf9; 0x6e; 0x6e; 0x60;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,96))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x64;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,100))) *)
  0xc5; 0xf9; 0x6e; 0x6e; 0x74;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,116))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0x66; 0x78;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,120))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0x88; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0x8c; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,140))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0x9c; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,156))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,160))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0xb0; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,176))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0xb4; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,180))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0xc4; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,196))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,200))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0xd8; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,216))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0xdc; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,220))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0xec; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,236))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0xf0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,240))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,256))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0x04; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,260))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0x14; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,276))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0x18; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,280))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,296))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm4) *)
  0xc5; 0xfa; 0x6f; 0xa6; 0x2c; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm4) (Memop Word128 (%% (rsi,300))) *)
  0xc5; 0xf9; 0x6e; 0xae; 0x3c; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm5) (Memop Doubleword (%% (rsi,316))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe5; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm5) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xe4; 0x94;
                           (* VPERMQ (%_% ymm4) (%_% ymm4) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x47; 0xe1;
                           (* VPSLLVD (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xd4; 0x01;
                           (* VPSRLW (%_% ymm4) (%_% ymm4) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm4) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

(* TODO: Prove correctness of poly_decompress_d10_avx2 *)
