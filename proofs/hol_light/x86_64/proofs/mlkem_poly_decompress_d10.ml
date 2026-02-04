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

let mlkem_poly_decompress_d10_tmc =
  define_trimmed "mlkem_poly_decompress_d10_tmc" mlkem_poly_decompress_d10_mc;;
let MLKEM_POLY_DECOMPRESS_D10_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_decompress_d10_tmc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D10_MC =
  REWRITE_CONV[mlkem_poly_decompress_d10_mc] `LENGTH mlkem_poly_decompress_d10_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_DECOMPRESS_D10_TMC =
  REWRITE_CONV[mlkem_poly_decompress_d10_tmc] `LENGTH mlkem_poly_decompress_d10_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D10_MC;
               LENGTH_MLKEM_POLY_DECOMPRESS_D10_TMC] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for 10-bit word lists                                       *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_WORDLIST_SPLIT_10_256 = prove(
  `!(l: (10 word) list). LENGTH l = 256 ==>
       num_of_wordlist l = num_of_wordlist (MAP ((word:num->160 word) o num_of_wordlist)
          (list_of_seq (\i. SUB_LIST (16 * i, 16) l) 16)
       )`,
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `LENGTH (l : (10 word) list) = 256` (fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPECL [`16`; `16`; `l:'a list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (ISPECL [`ll: ((10 word) list) list`; `16`] (INST_TYPE [`:10`, `:N`; `:160`, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let READ_BYTES_SPLIT_128_32 = prove(`read (bytes (a,20)) (s : 64 word -> 8 word) = t <=>
     read (bytes (a,16)) s = t MOD 2 EXP 128 /\
     read (bytes (word_add a (word 16),4)) s = t DIV 2 EXP 128`,
  REWRITE_TAC [REWRITE_RULE [ARITH_RULE `16 + 4 = 20`; ARITH_RULE `8 * 16 = 128`]
  (INST [`16`,`k:num`; `4`,`l:num`] READ_BYTES_SPLIT_ANY)]);;

let DIMINDEX_160 = DIMINDEX_CONV `dimindex (:160)`;;

let READ_WBYTES_SPLIT_128_32 = prove(`read (wbytes a) s = (t : 160 word) <=>
     read (bytes128 a) s = word (val t MOD 2 EXP 128) /\
     read (bytes32 (word_add a (word 16))) s = word (val t DIV 2 EXP 128)`,
  let VAL_WORD_160_MOD_128 = prove(`val (word (val (t : 160 word) MOD 2 EXP 128) : 128 word) = val t MOD 2 EXP 128`,
    SIMP_TAC[VAL_WORD; DIMINDEX_128; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 128 128 = 128`]) in
  let VAL_WORD_160_DIV_128 = prove (`val (word (val (t : 160 word) DIV 2 EXP 128) : 32 word) = val t DIV 2 EXP 128`,
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `t:160 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_160] THEN ARITH_TAC) in
  REWRITE_TAC[BYTES128_WBYTES; BYTES32_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES; DIMINDEX_160; ARITH_RULE `160 DIV 8 = 20`;
    READ_BYTES_SPLIT_128_32; DIMINDEX_128; DIMINDEX_32; ARITH_RULE `128 DIV 8 = 16`; ARITH_RULE `32 DIV 8 = 4`;
    VAL_WORD_160_MOD_128; VAL_WORD_160_DIV_128]);;

let READ_WBYTES_SPLIT_128_32' = prove(`t < 2 EXP 160 ==> (read (wbytes a) s = (word t : 160 word) <=>
     read (bytes128 a) s = word (t MOD 2 EXP 128) /\
     read (bytes32 (word_add a (word 16))) s = word (t DIV 2 EXP 128))`,
  STRIP_TAC THEN REWRITE_TAC [READ_WBYTES_SPLIT_128_32] THEN IMP_REWRITE_TAC [VAL_WORD_EXACT; DIMINDEX_160]);;

let READ_MEMORY_WBYTES_SPLIT_128_32 = prove(`t < 2 EXP 160 ==> (read (memory :> wbytes a) s = (word t : 160 word) <=>
     read (memory :> bytes128 a) s = word (t MOD 2 EXP 128) /\
     read (memory :> bytes32 (word_add a (word 16))) s = word (t DIV 2 EXP 128))`,
  STRIP_TAC THEN REWRITE_TAC [READ_COMPONENT_COMPOSE] THEN IMP_REWRITE_TAC [READ_WBYTES_SPLIT_128_32']);;

let MOD_2_128_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t MOD 2 EXP 128) : 128 word = word_subword (word t : 160 word) (0, 128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:160)`] THEN
    MP_TAC (SPECL [`t:num`; `2`; `160`; `128`] MOD_MOD_EXP_MIN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC));;

let DIV_2_128_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t DIV 2 EXP 128) : 32 word = word_subword (word t : 160 word) (128, 32)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_32] THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:160)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]));;

(* Subword simplification lemmas for 160-bit words split into 128+32 *)
let subword_goal_d10 n =
  let n8 = mk_small_numeral (8 * n) in
  if n < 16 then
    subst [n8, `n_term:num`] `word_subword (word_subword (x : 160 word) (0, 128) : 128 word) (n_term, 8) = word_subword (x : 160 word) (n_term, 8) : 8 word`
  else
    let offset = mk_small_numeral (8 * (n - 16)) in
    subst [offset, `n_term:num`; n8, `m_term:num`]
      `word_subword (word_subword (word_subword (x : 160 word) (128, 32) : 32 word) (0, 64) : 64 word) (n_term, 8) = word_subword (x : 160 word) (m_term, 8) : 8 word`;;

let SUBWORD_SIMPS_D10 = map (fun i -> WORD_BLAST (subword_goal_d10 i)) (0--19);;

let WORD_SUBWORD_NUM_OF_WORDLIST_16_10 = prove(`!ls:(10 word)list k.
    LENGTH ls = 16 /\ k < 16
    ==> word_subword (word (num_of_wordlist ls) : 160 word) (10*k,10) : 10 word = EL k ls`,
  let th = INST_TYPE [`:160`,`:KL`; `:10`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
  let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
  REWRITE_TAC [REWRITE_RULE[ARITH_RULE `160 = 10 * n <=> n = 16`; MESON[] `n = 16 /\ k < n <=> n = 16 /\ k < 16`] th]);;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D10 =
  let base = WORD_SUBWORD_NUM_OF_WORDLIST_16_10 in
  let mk k =
    let th = SPEC (mk_small_numeral k) (SPEC `ls:(10 word)list` base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0--15);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the decompression formula                                  *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_10 = DIMINDEX_CONV `dimindex (:10)`;;

let DECOMPRESS_D10_CORRECT = prove(
  `word_subword (word_add (word_ushr
     (word_mul (word_shl (word_zx (x : 10 word) : 32 word) 5) (word 3329))
     14) (word 1)) (1, 16) = decompress_d10 x`,
  REWRITE_TAC[decompress_d10; GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_ADD;
              VAL_WORD_USHR; VAL_WORD_MUL; VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:10 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(x:10 word)`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let mk_bitfiddle_d10 n =
  let base = n - (n mod 2) in
  let lo_byte = 10 * base / 8 in
  let pre_shift = if n mod 4 < 2 then 4 else 0 in
  let mul_shift = if n mod 2 = 0 then 2 else 0 in
  let word16_base = if n mod 2 = 0 then 0 else 16 in
  let mask = if n mod 2 = 0 then 8184 else 32736 in
  let word_for_byte k =
      subst [mk_small_numeral (8*k), `b:num`] `word_subword (t: 160 word) (b, 8) : 8 word` in
  let word32 = subst [word_for_byte (lo_byte + 2), `b2 : 8 word`;
                      word_for_byte (lo_byte + 1), `b1 : 8 word`;
                      word_for_byte (lo_byte + 0), `b0 : 8 word`]
     `word_join (word_join (b2 : 8 word) (b1 : 8 word) : 16 word) (word_join b1 (b0 : 8 word) : 16 word) : 32 word` in
  (* The algorithm shifts left by 4 then right by 1, net shift left by 3, then masks with 0x7FF8 *)
  let word_term = subst [mk_small_numeral pre_shift, `pre_shift: num`; 
                         mk_small_numeral mul_shift, `mul_shift: num`; 
                         mk_small_numeral word16_base, `word16_base: num`;
                         mk_small_numeral mask, `mask: num`;
                         word32, `word32 : 32 word`]
     `word_shl (
        word_sx (
          word_and (
            word_ushr (
              word_subword (
                word_shl (word32 : 32 word) (pre_shift: num))
              (word16_base,16) : 16 word) 
            1) 
          (word mask : 16 word)) : 32 word)
        mul_shift` in
    subst [word_term, `abstract_entry: 32 word`; mk_small_numeral n, `n: num`; mk_small_numeral (10*n), `i:num`]
        `(abstract_entry: 32 word) = word_shl (word_zx (word_subword (t : 160 word) (i,10) : 10 word) : 32 word) 5`;;

let BITFIDDLE_LEMMAS_D10 = map (fun n -> WORD_BLAST (mk_bitfiddle_d10 n)) (0--15);;

let SIMP_DECOMPOSE_TAC_D10 =
  RULE_ASSUM_TAC (REWRITE_RULE [
    WORD_BLAST `word_mul (word_sx (x : 16 word) : 32 word) (word 3329) = word_mul (word_shl (word_sx (x : 16 word)) 0) (word 3329)`;
    WORD_BLAST `word_mul (x : 32 word) (word 13316) = word_mul (word_shl x 2) (word 3329)`]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE ([DIV_2_128_AS_SUBWORD; MOD_2_128_AS_SUBWORD] @ SUBWORD_SIMPS_D10 @ BITFIDDLE_LEMMAS_D10)) THEN
  REPEAT (FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `read (memory :> bytes256 r) s0 = xxx`) o concl))) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D10) THEN
  REWRITE_TAC [DECOMPRESS_D10_CORRECT] THEN
  UNDISCH_THEN `LENGTH (inlist : (10 word) list) = 256` (fun th -> CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  REPEAT DISCH_TAC;;

let MLKEM_POLY_DECOMPRESS_D10_CORRECT = prove(
  `!r a data (inlist:(10 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d10_tmc); (a, 320); (data, 32)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_decompress_d10_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword decompress_d10_data): (8 word) list) /\
                read (memory :> bytes(a, 320)) s = num_of_wordlist inlist)
           (\s. read RIP s = word (pc + 954) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d10 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 512)] ,,
            MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5])`,

  MAP_EVERY X_GEN_TAC
    [`r:int64`; `a:int64`; `data:int64`; `inlist:(10 word) list`; `pc:num`] THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Move to 256-bit granular preconditions for input array *)
  UNDISCH_TAC `read(memory :> bytes(a,320)) s0 = num_of_wordlist(inlist: (10 word) list)` THEN
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_10_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN

  IMP_REWRITE_TAC [READ_MEMORY_WBYTES_SPLIT_128_32] THEN
  MAP_EVERY (fun n -> SUBGOAL_THEN (subst[mk_small_numeral n,`k:num`] `num_of_wordlist (SUB_LIST (16 * k,16) (inlist : (10 word) list)) < 2 EXP 160`)
     (fun th -> REWRITE_TAC[th]) THENL [
       TRANS_TAC LTE_TRANS (subst[mk_small_numeral n,`k:num`]
                            `2 EXP (dimindex(:10) * LENGTH(SUB_LIST(16*k,16) (inlist : (10 word) list)))`) THEN
       REWRITE_TAC[NUM_OF_WORDLIST_BOUND] THEN
       REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_CONV `dimindex (:10)`] THEN
       ASM_SIMP_TAC [] THEN NUM_REDUCE_TAC;
       ALL_TAC]) (0--15) THEN
  REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (TOP_SWEEP_CONV NUM_ADD_CONV) THEN
  STRIP_TAC THEN

  (* Move to 256-bit granular precondition for constant array *)
  UNDISCH_TAC
   `read(memory :> bytes(data,32)) s0 = num_of_wordlist ((MAP iword decompress_d10_data) : (8 word) list)` THEN
  REWRITE_TAC [decompress_d10_data; MAP] THEN
  REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                   [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN
  STRIP_TAC THEN

  (* Gather some derived preconditions for the length of sublists *)
  MAP_EVERY (fun i -> SUBGOAL_THEN (subst [mk_small_numeral (16 * i), `i: num`] `LENGTH (SUB_LIST (i, 16) (inlist : (10 word) list)) = 16`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC]) (0 -- 15) THEN

  (*** Symbolic execution ***)
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_DECOMPRESS_D10_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC []) (1--170) THEN
  SIMP_DECOMPOSE_TAC_D10 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Spell out input list entry by entry *)
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC (TOP_SWEEP_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC [MAP] THEN
  (* Switch to 256-bit granularity *)
  REPLICATE_TAC 4 (CONV_TAC (ONCE_REWRITE_CONV [GSYM NUM_OF_PAIR_WORDLIST])) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC (ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM BYTES256_WBYTES]);;

let MLKEM_POLY_DECOMPRESS_D10_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(10 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d10_tmc); (a, 320); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d10_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword decompress_d10_data): (8 word) list) /\
                read (memory :> bytes(a, 320)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d10 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d10 inlist)) /\
                                       ival (EL i (MAP decompress_d10 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d10_tmc
    MLKEM_POLY_DECOMPRESS_D10_CORRECT THEN
  (* Prove bounds *)
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [EL_MAP; ARITH; IVAL_DECOMPRESS_D10_BOUND]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/x86_64/src/arith_native_x86_64.h *)

let MLKEM_POLY_DECOMPRESS_D10_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(10 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d10_mc); (a, 320); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d10_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword decompress_d10_data): (8 word) list) /\
                read (memory :> bytes(a, 320)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d10 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d10 inlist)) /\
                                       ival (EL i (MAP decompress_d10 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D10_NOIBT_SUBROUTINE_CORRECT));;
