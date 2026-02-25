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

let MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH = 1`;;

let MLKEM_POLY_DECOMPRESS_D4_CORE_END = new_definition
  `MLKEM_POLY_DECOMPRESS_D4_CORE_END =
   LENGTH mlkem_poly_decompress_d4_tmc - MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D4_MC;
               LENGTH_MLKEM_POLY_DECOMPRESS_D4_TMC;
               MLKEM_POLY_DECOMPRESS_D4_CORE_END;
               MLKEM_POLY_DECOMPRESS_D4_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Word-expression for decompression computed by the AVX2 assembly           *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_WORDLIST_SPLIT_4_256 = prove(
  `!(l: (4 word) list). LENGTH l = 256 ==>
       num_of_wordlist l = num_of_wordlist (MAP ((word:num->64 word) o num_of_wordlist)
          (list_of_seq (\i. SUB_LIST (16 * i, 16) l) 16)
       )`,
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `LENGTH (l : (4 word) list) = 256` (fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPECL [`16`; `16`; `l:'a list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (ISPECL [`ll: ((4 word) list) list`; `16`] (INST_TYPE [`:4`, `:N`; `:64`, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let WORD_SUBWORD_NUM_OF_WORDLIST_16_4 = prove(`!ls:(4 word)list k.
    LENGTH ls = 16 /\ k < 16
    ==> word_subword (word (num_of_wordlist ls) : 64 word) (4*k,4) : 4 word = EL k ls`,
  let th = INST_TYPE [`:64`,`:KL`; `:4`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
  let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
  REWRITE_TAC [REWRITE_RULE[ARITH_RULE `64 = 4 * n <=> n = 16`; MESON[] `n = 16 /\ k < n <=> n = 16 /\ k < 16`] th]);;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D4 =
  let base = WORD_SUBWORD_NUM_OF_WORDLIST_16_4 in
  let mk k =
    let th = SPEC (mk_small_numeral k) (SPEC `ls:(4 word)list` base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0--15);;

let DECOMPRESS_D4_CORRECT = prove(
  `word_subword (word_add (word_ushr
     (word_mul (word_shl (word_zx (x : 4 word) : 32 word) 11) (word 3329 : 32 word))
     14) (word 1)) (1, 16) = decompress_d4 x`,
  REWRITE_TAC[decompress_d4; GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_ADD;
              VAL_WORD_USHR; VAL_WORD_MUL; VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:4 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(x:4 word)`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SIMP_DECOMPRESS_D4_TAC =   
  RULE_ASSUM_TAC (fun th -> let tm = concl th in
    if is_bytes256_read tm then
    CONV_RULE (TRY_CONV (DECOMPRESS_256_CONV 11 4) THENC (ONCE_REWRITE_CONV [DECOMPRESS_D4_CORRECT])) th
    else th);;  

(* ------------------------------------------------------------------------- *)
(* Main correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

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
           (\s. read RIP s = word (pc + MLKEM_POLY_DECOMPRESS_D4_CORE_END) /\
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
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_4_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN 
  REPEAT STRIP_TAC THEN

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
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_DECOMPRESS_D4_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC (map GSYM (WORD_MUL_2EXP @ WORD_MUL_2EXP_3329))
                      THEN SIMP_DECOMPRESS_D4_TAC) (1--122) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Gather some derived preconditions for the length of sublists *)
  MAP_EVERY (fun i -> SUBGOAL_THEN (subst [mk_small_numeral (16 * i), `i: num`] `LENGTH (SUB_LIST (i, 16) (inlist : (4 word) list)) = 16`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC]) (0 -- 15) THEN

  (* Unwrap assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE [WRAP]) THEN  

  REPEAT (FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `read (memory :> bytes256 r) s0 = xxx`) o concl))) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D4) THEN
  UNDISCH_THEN `LENGTH (inlist : (4 word) list) = 256` (fun th -> CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  REPEAT DISCH_TAC THEN

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
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d4 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d4 inlist)) /\
                                       ival (EL i (MAP decompress_d4 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d4_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D4_CORRECT) THEN
  (* Prove bounds *)
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [EL_MAP; ARITH; IVAL_DECOMPRESS_D4_BOUND]);;

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
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d4 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d4 inlist)) /\
                                       ival (EL i (MAP decompress_d4 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_poly_decompress_d4" subroutine_signatures)
    MLKEM_POLY_DECOMPRESS_D4_CORRECT
    MLKEM_POLY_DECOMPRESS_D4_TMC_EXEC;;

let MLKEM_POLY_DECOMPRESS_D4_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(4 word) list) pc.
           LENGTH inlist = 256 /\
           aligned 32 r /\
           aligned 32 data /\
           ALL (nonoverlapping (r,512))
           [word pc,LENGTH mlkem_poly_decompress_d4_tmc; a,128; data,32]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc)
                      (BUTLAST mlkem_poly_decompress_d4_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + MLKEM_POLY_DECOMPRESS_D4_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc /\
                         memaccess_inbounds e2
                           [a,128; data,32; r,512] [r,512]))
               (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes (r,512)] ,,
              MAYCHANGE [RIP] ,,
              MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_DECOMPRESS_D4_TMC_EXEC);;

let MLKEM_POLY_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(4 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 r /\
           aligned 32 data /\
           ALL (nonoverlapping (r,512))
           [word pc,LENGTH mlkem_poly_decompress_d4_tmc; a,128; data,32;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_decompress_d4_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [a,128; data,32; r,512; stackpointer,8]
                           [r,512; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d4_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D4_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_POLY_DECOMPRESS_D4_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(4 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 r /\
           aligned 32 data /\
           ALL (nonoverlapping (r,512))
           [word pc,LENGTH mlkem_poly_decompress_d4_mc; a,128; data,32;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_decompress_d4_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [a,128; data,32; r,512; stackpointer,8]
                           [r,512; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE));;
