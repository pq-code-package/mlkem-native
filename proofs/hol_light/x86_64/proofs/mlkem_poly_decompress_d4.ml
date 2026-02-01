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
needs "x86_64/proofs/mlkem_compress_consts.ml";;

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

let mlkem_poly_decompress_d4_tmc =
  define_trimmed "mlkem_poly_decompress_d4_tmc" mlkem_poly_decompress_d4_mc;;
let MLKEM_POLY_DECOMPRESS_D4_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_decompress_d4_tmc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D4_MC =
  REWRITE_CONV[mlkem_poly_decompress_d4_mc] `LENGTH mlkem_poly_decompress_d4_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_DECOMPRESS_D4_TMC =
  REWRITE_CONV[mlkem_poly_decompress_d4_tmc] `LENGTH mlkem_poly_decompress_d4_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D4_MC;
               LENGTH_MLKEM_POLY_DECOMPRESS_D4_TMC] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Word-expression for decompression computed by the AVX2 assembly           *)
(* ------------------------------------------------------------------------- *)

let decompress_d4_avx2 = new_definition `decompress_d4_avx2 (x : 4 word) : 16 word =
   word_subword (word_add (word_ushr
     (word_mul (word_sx (word_mul (word_zx x : 16 word) (word 2048 : 16 word)) : 32 word) (word 3329 : 32 word))
     14) (word 1)) (1, 16)`;;

let DECOMPRESS_D4_AVX2_CORRECT = prove(
  `decompress_d4_avx2 x = decompress_d4 x`,
  let DIMINDEX_4 = DIMINDEX_CONV `dimindex(:4)` in
  let VAL_4_WORD_BOUND = WORD_BLAST `val (x : 4 word) < 16` in
  let VAL_16_WORD_BOUND = WORD_BLAST `val (x : 16 word) < 65536` in
  let VAL_DECOMPRESS_D4_AVX2_CORE = prove(`!(x: 16 word).
    val (word_subword
          (word_add
             (word_ushr
                (word_shl (word_zx x : 32 word) 11)
                14)
             (word 1))
           (1,16) : 16 word)
      = (val x + 8) DIV 16`,
    GEN_TAC THEN
    REWRITE_TAC [WORD_BLAST `!(x : 16 word). word_ushr (word_shl (word_zx x : 32 word) 11) 14 = word_ushr (word_zx x) 3`] THEN
    REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_SHL;
                VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MP_TAC VAL_16_WORD_BOUND THEN STRIP_TAC THEN
    MAP_EVERY (fun t -> SUBGOAL_THEN t SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC])
      [`val (x:16 word) MOD 4294967296 = val x`;
       `(val (x:16 word) DIV 8 + 1) MOD 4294967296 = val x DIV 8 + 1`;
       `((val (x:16 word) DIV 8 + 1) DIV 2) MOD 65536 = (val x DIV 8 + 1) DIV 2`] THEN
    ASM_ARITH_TAC) in
  let VAL_DECOMPRESS_D4 = prove(
    `val (decompress_d4 x) = (val x * 3329 + 8) DIV 16`,
    IMP_REWRITE_TAC [decompress_d4; VAL_WORD_EQ; DIMINDEX_16] THEN MP_TAC VAL_4_WORD_BOUND THEN ARITH_TAC) in
  let MUL_ZX_SHUFFLE = prove(`!(x : 4 word). word_mul (word 3329) (word_zx x : 32 word) = word_zx (word_mul (word 3329) (word_zx x : 16 word))`,
    GEN_TAC THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD;
                DIMINDEX_4; DIMINDEX_16; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC VAL_4_WORD_BOUND THEN STRIP_TAC THEN
    CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(GSYM MOD_LT) THEN ASM_ARITH_TAC) in
  let TECHNICAL_EQ = prove(
    `word_sx (word_mul (word_zx (x:4 word):16 word) (word 2048:16 word)):32 word
     = word_shl (word_zx (x:4 word):32 word) 11`,
     REWRITE_TAC [WORD_BLAST `!(x : 16 word). word_mul x (word 2048 : 16 word) = word_shl x 11`] THEN CONV_TAC WORD_BLAST) in
  REWRITE_TAC [GSYM VAL_EQ;decompress_d4_avx2; MUL_ZX_SHUFFLE; VAL_DECOMPRESS_D4; VAL_DECOMPRESS_D4_AVX2_CORE; TECHNICAL_EQ; WORD_MUL_SHL] THEN
  IMP_REWRITE_TAC [VAL_WORD_MUL_EXACT; VAL_WORD_EXACT; VAL_WORD_ZX_EXACT; DIMINDEX_4; DIMINDEX_16] THEN
  NUM_REDUCE_TAC THEN MP_TAC VAL_4_WORD_BOUND THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Main correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_8_4_4_15 = prove(
   `word_and (word_join (x:8 word) (word_join (b:4 word) (a:4 word):8 word))
             (word 15:16 word) = word_zx a`, CONV_TAC WORD_BLAST);;
let WORD_AND_8_4_4_240 = prove(
   `word_and (word_join (x:8 word) (word_join (b:4 word) (a:4 word):8 word))
             (word 240:16 word) = word_shl (word_zx b) 4`, CONV_TAC WORD_BLAST);;
let WORD_SHL_THEN_MUL_2048 = prove(
      `(word_mul (word_shl (word_zx (x : 4 word) : 16 word) 4) (word 128)) = word_mul (word_zx x : 16 word) (word 2048)`,
      CONV_TAC WORD_BLAST);;

let MLKEM_POLY_DECOMPRESS_D4_CORRECT = prove(
  `!r a data (inlist:(4 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d4_tmc); (a, 128); (data, 32)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_decompress_d4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword decompress_d4_data): (8 word) list) /\
                read (memory :> bytes(a, 128)) s = num_of_wordlist inlist)
           (\s. read RIP s = word (pc + 624) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d4 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 512)] ,,
            MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4])`,
  MAP_EVERY X_GEN_TAC
    [`r:int64`; `a:int64`; `data:int64`; `inlist:(4 word) list`; `pc:num`] THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (* Move to 256-bit granular preconditions for input array *)
  ENSURES_INIT_TAC "s0" THEN
  UNDISCH_TAC `read(memory :> bytes(a,128)) s0 = num_of_wordlist(inlist: (4 word) list)` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
  REWRITE_TAC[] THEN
  REPLICATE_TAC 4 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                   [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN STRIP_TAC THEN
  (* Move to 256-bit granular precondition for constant array *)
  UNDISCH_TAC
   `read(memory :> bytes(data,32)) s0 = num_of_wordlist ((MAP iword decompress_d4_data) : (8 word) list)` THEN
  REWRITE_TAC [decompress_d4_data; MAP] THEN
  REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                   [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN STRIP_TAC THEN
  (*** Symbolic execution ***)
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_DECOMPRESS_D4_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC [GSYM WORD_AND_8_4_4_15; GSYM WORD_AND_8_4_4_240; GSYM WORD_SHL_THEN_MUL_2048; decompress_d4_avx2; GSYM DECOMPRESS_D4_AVX2_CORRECT])
            (1--122) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* Spell out input list entry by entry *)
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC (TOP_SWEEP_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP] THEN
  (* Switch to 256-bit granularity *)
  REPLICATE_TAC 4 (CONV_TAC (ONCE_REWRITE_CONV [GSYM NUM_OF_PAIR_WORDLIST])) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC (ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM BYTES256_WBYTES]);;

let MLKEM_POLY_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(4 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d4_tmc); (a, 128); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword decompress_d4_data): (8 word) list) /\
                read (memory :> bytes(a, 128)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d4 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d4_tmc
    MLKEM_POLY_DECOMPRESS_D4_CORRECT);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/x86_64/src/arith_native_x86_64.h *)

let MLKEM_POLY_DECOMPRESS_D4_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(4 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d4_mc); (a, 128); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword decompress_d4_data): (8 word) list) /\
                read (memory :> bytes(a, 128)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d4 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT));;
