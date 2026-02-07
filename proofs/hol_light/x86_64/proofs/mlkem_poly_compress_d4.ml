(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 4 bits.                         *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d4.o";; *)

let mlkem_poly_compress_d4_mc =
  define_assert_from_elf "mlkem_poly_compress_d4_mc" "x86_64/mlkem/mlkem_poly_compress_d4.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x00; 0x02; 0x00; 0x02;
                           (* MOV (% eax) (Imm32 (word 33554944)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xb8; 0x0f; 0x00; 0x0f; 0x00;
                           (* MOV (% eax) (Imm32 (word 983055)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0x01; 0x10; 0x01; 0x10;
                           (* MOV (% eax) (Imm32 (word 268505089)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc5; 0xfd; 0x6f; 0x22;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfd; 0x6f; 0x2e;  (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x76; 0x20;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x7e; 0x40;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x60;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x2f;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xae; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xae; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xae; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

(* TODO: Prove correctness of poly_compress_d4_avx2 *)
