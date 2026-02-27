(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 5 bits.                     *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "x86_64/proofs/mlkem_compress_common.ml";;
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

let MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH = 1`;;

let MLKEM_POLY_DECOMPRESS_D5_CORE_END = new_definition
  `MLKEM_POLY_DECOMPRESS_D5_CORE_END =
   LENGTH mlkem_poly_decompress_d5_tmc - MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D5_MC;
               LENGTH_MLKEM_POLY_DECOMPRESS_D5_TMC;
               MLKEM_POLY_DECOMPRESS_D5_CORE_END;
               MLKEM_POLY_DECOMPRESS_D5_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

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

let SIMP_DECOMPRESS_D5_TAC =   
  RULE_ASSUM_TAC (fun th -> let tm = concl th in
    if is_bytes256_read tm then
    CONV_RULE (TRY_CONV (DECOMPRESS_256_CONV 10 5) THENC (ONCE_REWRITE_CONV [DECOMPRESS_D5_CORRECT])) th
    else th);;

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
           (\s. read RIP s = word (pc + MLKEM_POLY_DECOMPRESS_D5_CORE_END) /\
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
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_DECOMPRESS_D5_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC (map GSYM (BASE_SIMPS_D5 @ WORD_MUL_2EXP @ WORD_MUL_2EXP_3329))
                      THEN SIMP_DECOMPRESS_D5_TAC) (1--134) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Unwrap assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE [WRAP]) THEN  

  REPEAT (FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `read (memory :> bytes256 r) s0 = xxx`) o concl))) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D5) THEN
  UNDISCH_THEN `LENGTH (inlist : (5 word) list) = 256` (fun th -> CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
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
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d5_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D5_CORRECT) THEN
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

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_poly_decompress_d5" subroutine_signatures)
    MLKEM_POLY_DECOMPRESS_D5_CORRECT
    MLKEM_POLY_DECOMPRESS_D5_TMC_EXEC;;

let MLKEM_POLY_DECOMPRESS_D5_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(5 word) list) pc.
           LENGTH inlist = 256 /\
           aligned 32 r /\
           aligned 32 data /\
           ALL (nonoverlapping (r,512))
           [word pc,LENGTH mlkem_poly_decompress_d5_tmc; a,160; data,96]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc)
                      (BUTLAST mlkem_poly_decompress_d5_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s.
                    read RIP s =
                      word (pc + MLKEM_POLY_DECOMPRESS_D5_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc /\
                         memaccess_inbounds e2
                           [a,160; data,96; r,512] [r,512]))
               (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes (r,512)] ,,
              MAYCHANGE [RIP] ,,
              MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_DECOMPRESS_D5_TMC_EXEC);;

let MLKEM_POLY_DECOMPRESS_D5_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(5 word) list) pc stackpointer returnaddress.
          LENGTH inlist = 256 /\
          aligned 32 r /\
          aligned 32 data /\
          ALL (nonoverlapping (r,512))
          [word pc,LENGTH mlkem_poly_decompress_d5_tmc; a,160; data,96;
           stackpointer,8]
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_decompress_d5_tmc /\
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
                           [a,160; data,96; r,512; stackpointer,8]
                           [r,512; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d5_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D5_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_POLY_DECOMPRESS_D5_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(5 word) list) pc stackpointer returnaddress.
          LENGTH inlist = 256 /\
          aligned 32 r /\
          aligned 32 data /\
          ALL (nonoverlapping (r,512))
          [word pc,LENGTH mlkem_poly_decompress_d5_mc; a,160; data,96;
           stackpointer,8]
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_decompress_d5_mc /\
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
                           [a,160; data,96; r,512; stackpointer,8]
                           [r,512; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D5_NOIBT_SUBROUTINE_SAFE));;
