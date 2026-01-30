(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 4 bits.                     *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d4.o";; *)

let mlkem_poly_decompress_d4_mc =
  define_assert_from_elf "mlkem_poly_decompress_d4_mc" "x86_64/mlkem/mlkem_poly_decompress_d4.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x0f; 0x00; 0xf0; 0x00;
                           (* MOV (% eax) (Imm32 (word 15728655)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xb8; 0x00; 0x08; 0x80; 0x00;
                           (* MOV (% eax) (Imm32 (word 8390656)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xc5; 0xfd; 0x6f; 0x1a;  (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfa; 0x7e; 0x26;  (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x27;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x08;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x10;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x18;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x20;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x28;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,40))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x30;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,48))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x38;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,56))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x40;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,64))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x48;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,72))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x50;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x58;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x60;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,96))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x68;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,104))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x70;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,112))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x78;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,120))) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe3;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xdb; 0xe1;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm4) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)
