(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 5 bits.                     *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(** print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d5.o";; *)

let mlkem_poly_decompress_d5_mc =
  define_assert_from_elf "mlkem_poly_decompress_d5_mc" "x86_64/mlkem/mlkem_poly_decompress_d5.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xfd; 0x6f; 0x0a;  (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfd; 0x6f; 0x52; 0x20;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xfd; 0x6f; 0x5a; 0x40;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdx,64))) *)
  0xc5; 0xfa; 0x7e; 0x26;  (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,0))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x08; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,8))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x27;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x0a;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,10))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x12; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,18))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x14;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,20))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x1c; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,28))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x1e;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,30))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x26; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,38))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x28;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,40))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x30; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,48))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x32;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,50))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x3a; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,58))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x3c;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,60))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x44; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,68))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x46;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,70))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x4e; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,78))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x50;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,80))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x58; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,88))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x5a;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,90))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x62; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,98))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x64;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,100))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x6c; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,108))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x6e;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,110))) *)
  0xc5; 0xd9; 0xc4; 0x66; 0x76; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,118))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0x66; 0x78;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,120))) *)
  0xc5; 0xd9; 0xc4; 0xa6; 0x80; 0x00; 0x00; 0x00; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,128))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0xa6; 0x82; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,130))) *)
  0xc5; 0xd9; 0xc4; 0xa6; 0x8a; 0x00; 0x00; 0x00; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,138))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0xa6; 0x8c; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,140))) *)
  0xc5; 0xd9; 0xc4; 0xa6; 0x94; 0x00; 0x00; 0x00; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,148))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm4) *)
  0xc5; 0xfa; 0x7e; 0xa6; 0x96; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rsi,150))) *)
  0xc5; 0xd9; 0xc4; 0xa6; 0x9e; 0x00; 0x00; 0x00; 0x04;
                           (* VPINSRW (%_% xmm4) (%_% xmm4) (Memop Word (%% (rsi,158))) (Imm8 (word 4)) *)
  0xc4; 0xe3; 0x5d; 0x38; 0xe4; 0x01;
                           (* VINSERTI128 (%_% ymm4) (%_% ymm4) (%_% xmm4) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x5d; 0x00; 0xe1;
                           (* VPSHUFB (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xdb; 0xe2;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xd5; 0xe3;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc4; 0xe2; 0x5d; 0x0b; 0xe0;
                           (* VPMULHRSW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm4) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_poly_decompress_d5_tmc =
  define_trimmed "mlkem_poly_decompress_d5_tmc" mlkem_poly_decompress_d5_mc;;
let MLKEM_POLY_DECOMPRESS_D5_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_decompress_d5_tmc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D5_MC =
  REWRITE_CONV[mlkem_poly_decompress_d5_mc] `LENGTH mlkem_poly_decompress_d5_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_DECOMPRESS_D5_TMC =
  REWRITE_CONV[mlkem_poly_decompress_d5_tmc] `LENGTH mlkem_poly_decompress_d5_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D5_MC;
               LENGTH_MLKEM_POLY_DECOMPRESS_D5_TMC] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

let NUM_OF_WORDLIST_SPLIT_5_256 = prove(
  `!(l: (5 word) list). LENGTH l = 256 ==> 
       num_of_wordlist l = num_of_wordlist (MAP ((word:num->80 word) o num_of_wordlist)
          (list_of_seq (\i. SUB_LIST (16 * i, 16) l) 16)
       )`,
  REPEAT STRIP_TAC THEN
  (* Rewrite LHS l using SUBLIST_PARTITION *)
  UNDISCH_THEN `LENGTH (l : (5 word) list) = 256` (fun th -> 
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPECL [`16`; `16`; `l:'a list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (ISPECL [`ll: ((5 word) list) list`; `16`] (INST_TYPE [`:5`, `:N`; `:80`, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let READ_BYTES_SPLIT_64_16 = prove(`read (bytes (a,10)) (s : 64 word -> 8 word) = t <=>
     read (bytes (a,8)) s = t MOD 2 EXP 64 /\
     read (bytes (word_add a (word 8),2)) s = t DIV 2 EXP 64`, 
  REWRITE_TAC [REWRITE_RULE [ARITH_RULE `8 + 2 = 10`; ARITH_RULE `8 * 8 = 64`]
  (INST [`8`,`k:num`; `2`,`l:num`] READ_BYTES_SPLIT_ANY)]);;

let DIMINDEX_80 = DIMINDEX_CONV `dimindex (:80)`

let READ_WBYTES_SPLIT_64_16 = prove(`read (wbytes a) s = (t : 80 word) <=>
     read (bytes64 a) s = word (val t MOD 2 EXP 64) /\
     read (bytes16 (word_add a (word 8))) s = word (val t DIV 2 EXP 64)`,
  let VAL_WORD_80_MOD_64 = prove(`val (word (val (t : 80 word) MOD 2 EXP 64) : 64 word) = val t MOD 2 EXP 64`,
    SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 64 64 = 64`]) in
  let VAL_WORD_80_DIV_64 = prove (`val (word (val (t : 80 word) DIV 2 EXP 64) : 16 word) = val t DIV 2 EXP 64`,
    REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `t:80 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_80] THEN ARITH_TAC) in
  REWRITE_TAC[BYTES64_WBYTES; BYTES16_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES; DIMINDEX_80; ARITH_RULE `80 DIV 8 = 10`;
    READ_BYTES_SPLIT_64_16; DIMINDEX_64; DIMINDEX_16; DIMINDEX_80; ARITH_RULE `64 DIV 8 = 8`; ARITH_RULE `16 DIV 8 = 2`; 
    VAL_WORD_80_MOD_64; VAL_WORD_80_DIV_64]);;

let READ_WBYTES_SPLIT_64_16' = prove(`t < 2 EXP 80 ==> (read (wbytes a) s = (word t : 80 word) <=>
     read (bytes64 a) s = word (t MOD 2 EXP 64) /\
     read (bytes16 (word_add a (word 8))) s = word (t DIV 2 EXP 64))`,
  STRIP_TAC THEN REWRITE_TAC [READ_WBYTES_SPLIT_64_16] THEN IMP_REWRITE_TAC [VAL_WORD_EXACT; DIMINDEX_80]);;

let READ_MEMORY_WBYTES_SPLIT_64_16 = prove(`t < 2 EXP 80 ==> (read (memory :> wbytes a) s = (word t : 80 word) <=>
     read (memory :> bytes64 a) s = word (t MOD 2 EXP 64) /\
     read (memory :> bytes16 (word_add a (word 8))) s = word (t DIV 2 EXP 64))`,
  STRIP_TAC THEN REWRITE_TAC [READ_COMPONENT_COMPOSE] THEN IMP_REWRITE_TAC [READ_WBYTES_SPLIT_64_16']);;
  
let MOD_2_64_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t MOD 2 EXP 64) : 64 word = word_subword (word t : 80 word) (0, 64)`, 
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:80)`] THEN
    MP_TAC (SPECL [`t:num`; `2`; `80`; `64`] MOD_MOD_EXP_MIN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC));;

let DIV_2_64_AS_SUBWORD = CONV_RULE NUM_REDUCE_CONV (prove(`word (t DIV 2 EXP 64) : 16 word = word_subword (word t : 80 word) (64, 16)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_16] THEN
    SIMP_TAC[DIMINDEX_CONV `dimindex(:80)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]));;

(* Since we need to split the natural 10-byte chunks into 8+2, we nested word_subword expressions 
 * `subword (subword (x : 80 word) (0, 64)) (8*i,8)` and `subword (subword (x : 80 word) (64, 16)) (8*i,8)` 
 * in the proof. The following lemmas bring them back to single word_subword on `80 word`s *)
let subword_goal n =
  let n8 = mk_small_numeral (8 * n) in
  if n < 8 then
    subst [n8, `n_term:num`] `word_subword (word_subword (x : 80 word) (0, 64) : 64 word) (n_term, 8) = word_subword (x : 80 word) (n_term, 8) : 8 word`
  else
    let offset = mk_small_numeral (8 * (n - 8)) in
    subst [offset, `n_term:num`; n8, `m_term:num`]
      `word_subword (word_subword (x : 80 word) (64, 16) : 16 word) (n_term, 8) = word_subword (x : 80 word) (m_term, 8) : 8 word`;;

let mk_subword_simp n =
    if n < 8 then
      prove(subword_goal n,
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
        SIMP_TAC[DIMINDEX_CONV `dimindex(:80)`; DIMINDEX_CONV `dimindex(:64)`; DIMINDEX_CONV `dimindex(:8)`] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[DIV_1; DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [DIV_1; CONV_RULE NUM_REDUCE_CONV (SPECL [`val (x:80 word)`; `2`; `64`; mk_small_numeral (8*n + 8)] MOD_MOD_EXP_MIN)])
    else
      prove(subword_goal n,
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
        SIMP_TAC[DIMINDEX_CONV `dimindex(:80)`; DIMINDEX_CONV `dimindex(:16)`; DIMINDEX_CONV `dimindex(:8)`] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[DIV_1; MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SIMP_TAC[DIV_DIV; ARITH_EQ; EXP_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        MP_TAC (SPECL [`val (x:80 word)`; `2`; `80`; mk_small_numeral (8*n + 8)] MOD_MOD_EXP_MIN) THEN
        CONV_TAC NUM_REDUCE_CONV);;

let SUBWORD_SIMPS = map mk_subword_simp (0--9);;

let WORD_SUBWORD_NUM_OF_WORDLIST_16 = prove(`!ls:(5 word)list k.
    LENGTH ls = 16 /\ k < 16
    ==> word_subword (word (num_of_wordlist ls) : 80 word) (5*k,5) : 5 word = EL k ls`,
  let th = INST_TYPE [`:80`,`:KL`; `:5`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
  let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
  REWRITE_TAC [REWRITE_RULE[ARITH_RULE `80 = 5 * n <=> n = 16`; MESON[] `n = 16 /\ k < n <=> n = 16 /\ k < 16`] th]);;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES =
  let base = WORD_SUBWORD_NUM_OF_WORDLIST_16 in
  let mk k =
    let th = SPEC (mk_small_numeral k) (SPEC `ls:(5 word)list` base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0--15);;

(* We operate on 256-bit vector registers naturally split in 8/16-bit chunks, but logically
 * operate on 5-bit nibbles. The following lemma shows that the shift and mask operations happening
 * on the vectors extract 5-bit nibbles. *)
let mk_bitfiddle n = 
   (* We want to work with nibble n, spanning bit position 5*n+0 .. 5*n + 4. Check which bytes are needed for that. *)
   let lo_byte = 5 * n / 8 in
   let hi_byte = (5 * n + 4) / 8 in
   let lo_bit = lo_byte * 8 in
   let hi_bit = hi_byte * 8 in
   let offset = 10 - (5 * n - lo_bit) in
   let wordlist_for_byte k b = 
      subst [mk_small_numeral b, `b:num`] `word_subword (t: 80 word) (b, 8) : 8 word` in
   let word_term = 
     (subst [mk_small_numeral (lo_byte * 8), `l:num`; mk_small_numeral (hi_byte * 8), `h:num`; mk_small_numeral offset, `offset:num`;
             wordlist_for_byte lo_byte lo_bit, `lo_byte: 8 word`;
             wordlist_for_byte hi_byte hi_bit, `hi_byte: 8 word`]
        `(word_and (word_shl (word_join (hi_byte: 8 word) (lo_byte: 8 word): 16 word) offset) (word 31744))`) in
    subst [word_term, `abstract_entry: 16 word`; mk_small_numeral n, `n: num`; mk_small_numeral (5*n), `i:num`]
        `word_sx (abstract_entry: 16 word) : 32 word = word_shl (word_zx (word_subword (t : 80 word) (i,5) : 5 word) : 32 word) 10`;;

let BITFIDDLE_LEMMAS = map (fun n -> WORD_BLAST (mk_bitfiddle n)) (0--15);;

let SHIFT_LEMMAS = map (fun i -> CONV_RULE NUM_REDUCE_CONV 
   (WORD_BLAST (subst [mk_small_numeral i, `i:num`] `word_mul (x : 16 word) (word (2 EXP i)) = word_shl x i`))) (0--11);;

let DIMINDEX_5 = DIMINDEX_CONV `dimindex (:5)`

let DECOMPRESS_D5_CORRECT = prove(
  `word_subword (word_add (word_ushr
     (word_mul (word_shl (word_zx (x : 5 word) : 32 word) 10) (word 3329 : 32 word))
     14) (word 1)) (1, 16) = decompress_d5 x`,
  REWRITE_TAC[decompress_d5; GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_ADD;
              VAL_WORD_USHR; VAL_WORD_MUL; VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:5 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(x:5 word)`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SIMP_DECOMPOSE_TAC =
  RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE ([WORD_SHL_WORD; WORD_SHL_AND] @ SHIFT_LEMMAS)) THEN
  RULE_ASSUM_TAC (REWRITE_RULE ([DIV_2_64_AS_SUBWORD; MOD_2_64_AS_SUBWORD] @ SUBWORD_SIMPS @ BITFIDDLE_LEMMAS)) THEN
  REPEAT (FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `read (memory :> bytes256 r) s0 = xxx`) o concl))) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES) THEN
  REWRITE_TAC [DECOMPRESS_D5_CORRECT] THEN
  UNDISCH_THEN `LENGTH (inlist : (5 word) list) = 256` (fun th -> CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  REPEAT DISCH_TAC;;

let MLKEM_POLY_DECOMPRESS_D5_CORRECT = prove(
  `!r a data (inlist:(5 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d5_tmc); (a, 160); (data, 96)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_decompress_d5_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 96)) s =
                  num_of_wordlist ((MAP iword decompress_d5_data): (8 word) list) /\
                read (memory :> bytes(a, 160)) s = num_of_wordlist inlist)
           (\s. read RIP s = word (pc + 723) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d5 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 512)] ,,
            MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4])`,

  MAP_EVERY X_GEN_TAC
    [`r:int64`; `a:int64`; `data:int64`; `inlist:(5 word) list`; `pc:num`] THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (* Move to 256-bit granular preconditions for input array *)
  ENSURES_INIT_TAC "s0" THEN

  UNDISCH_TAC `read(memory :> bytes(a,160)) s0 = num_of_wordlist(inlist: (5 word) list)` THEN
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_5_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN

  IMP_REWRITE_TAC [READ_MEMORY_WBYTES_SPLIT_64_16] THEN
  MAP_EVERY (fun n -> SUBGOAL_THEN (subst[mk_small_numeral n,`k:num`] `num_of_wordlist (SUB_LIST (16 * k,16) (inlist : (5 word) list)) < 2 EXP 80`)
     (fun th -> REWRITE_TAC[th]) THENL [
       TRANS_TAC LTE_TRANS (subst[mk_small_numeral n,`k:num`]
                            `2 EXP (dimindex(:5) * LENGTH(SUB_LIST(16*k,16) (inlist : (5 word) list)))`) THEN
       REWRITE_TAC[NUM_OF_WORDLIST_BOUND] THEN
       REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_CONV `dimindex (:5)`] THEN
       ASM_SIMP_TAC [] THEN NUM_REDUCE_TAC;
       ALL_TAC]) (0--15) THEN
  REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (TOP_SWEEP_CONV NUM_ADD_CONV) THEN
  STRIP_TAC THEN

  (* Move to 256-bit granular precondition for constant array *)
  UNDISCH_TAC
   `read(memory :> bytes(data,96)) s0 = num_of_wordlist ((MAP iword decompress_d5_data) : (8 word) list)` THEN
  REWRITE_TAC [decompress_d5_data; MAP] THEN
  REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                   [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN 
  STRIP_TAC THEN

  (* Gather some derived preconditions for the length of sublists *)
  MAP_EVERY (fun i -> SUBGOAL_THEN (subst [mk_small_numeral (16 * i), `i: num`] `LENGTH (SUB_LIST (i, 16) (inlist : (5 word) list)) = 16`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC]) (0 -- 15) THEN

  (*** Symbolic execution ***)
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_DECOMPRESS_D5_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC []) (1--134) THEN
  SIMP_DECOMPOSE_TAC THEN
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

let MLKEM_POLY_DECOMPRESS_D5_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(5 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d5_tmc); (a, 160); (data, 96); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d5_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 96)) s =
                  num_of_wordlist ((MAP iword decompress_d5_data): (8 word) list) /\
                read (memory :> bytes(a, 160)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d5 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d5 inlist)) /\
                                       ival (EL i (MAP decompress_d5 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d5_tmc
    MLKEM_POLY_DECOMPRESS_D5_CORRECT THEN
  (* Prove bounds *)
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [EL_MAP; ARITH; IVAL_DECOMPRESS_D5_BOUND]);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/x86_64/src/arith_native_x86_64.h *)

let MLKEM_POLY_DECOMPRESS_D5_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(5 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d5_mc); (a, 160); (data, 96); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d5_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 96)) s =
                  num_of_wordlist ((MAP iword decompress_d5_data): (8 word) list) /\
                read (memory :> bytes(a, 160)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d5 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d5 inlist)) /\
                                       ival (EL i (MAP decompress_d5 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D5_NOIBT_SUBROUTINE_CORRECT));;
