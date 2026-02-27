(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 5 bits.                         *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "x86_64/proofs/mlkem_compress_common.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d5.o";; *)

let mlkem_poly_compress_d5_mc =
  define_assert_from_elf "mlkem_poly_compress_d5_mc" "x86_64/mlkem/mlkem_poly_compress_d5.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x00; 0x04; 0x00; 0x04;
                           (* MOV (% eax) (Imm32 (word 67109888)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xb8; 0x1f; 0x00; 0x1f; 0x00;
                           (* MOV (% eax) (Imm32 (word 2031647)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0x01; 0x20; 0x01; 0x20;
                           (* MOV (% eax) (Imm32 (word 536944641)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xb8; 0x01; 0x00; 0x00; 0x04;
                           (* MOV (% eax) (Imm32 (word 67108865)) *)
  0xc5; 0xf9; 0x6e; 0xe0;  (* VMOVD (%_% xmm4) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0xb8; 0x0c; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 12)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xe8;
                           (* VMOVQ (%_% xmm5) (% rax) *)
  0xc4; 0xe2; 0x7d; 0x59; 0xed;
                           (* VPBROADCASTQ (%_% ymm5) (%_% xmm5) *)
  0xc5; 0xfd; 0x6f; 0x32;  (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfd; 0x6f; 0x3e;  (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x20;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0x3f;  (* VMOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x47; 0x10;
                           (* VMOVD (Memop Doubleword (%% (rdi,16))) (%_% xmm8) *)
  0xc5; 0xfd; 0x6f; 0x7e; 0x40;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x60;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0x7f; 0x14;
                           (* VMOVDQU (Memop Word128 (%% (rdi,20))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x47; 0x24;
                           (* VMOVD (Memop Doubleword (%% (rdi,36))) (%_% xmm8) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0x7f; 0x28;
                           (* VMOVDQU (Memop Word128 (%% (rdi,40))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x47; 0x38;
                           (* VMOVD (Memop Doubleword (%% (rdi,56))) (%_% xmm8) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0x7f; 0x3c;
                           (* VMOVDQU (Memop Word128 (%% (rdi,60))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x47; 0x4c;
                           (* VMOVD (Memop Doubleword (%% (rdi,76))) (%_% xmm8) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0x7f; 0x50;
                           (* VMOVDQU (Memop Word128 (%% (rdi,80))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x47; 0x60;
                           (* VMOVD (Memop Doubleword (%% (rdi,96))) (%_% xmm8) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0x7f; 0x64;
                           (* VMOVDQU (Memop Word128 (%% (rdi,100))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x47; 0x74;
                           (* VMOVD (Memop Doubleword (%% (rdi,116))) (%_% xmm8) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0x7f; 0x78;
                           (* VMOVDQU (Memop Word128 (%% (rdi,120))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x87; 0x88; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,136))) (%_% xmm8) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xf5; 0xfc;  (* VPMADDWD (%_% ymm7) (%_% ymm7) (%_% ymm4) *)
  0xc4; 0xe2; 0x45; 0x47; 0xfd;
                           (* VPSLLVD (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0xc5; 0x45; 0xfd;
                           (* VPSRLVQ (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xe2; 0x45; 0x00; 0xfe;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xf8; 0x01;
                           (* VEXTRACTI128 (%_% xmm8) (%_% ymm7) (Imm8 (word 1)) *)
  0xc4; 0xc3; 0x41; 0x4c; 0xf8; 0x60;
                           (* VPBLENDVB (%_% xmm7) (%_% xmm7) (%_% xmm8) (%_% xmm6) *)
  0xc5; 0xfa; 0x7f; 0xbf; 0x8c; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,140))) (%_% xmm7) *)
  0xc5; 0x79; 0x7e; 0x87; 0x9c; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,156))) (%_% xmm8) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_poly_compress_d5_tmc =
  define_trimmed "mlkem_poly_compress_d5_tmc" mlkem_poly_compress_d5_mc;;
let MLKEM_POLY_COMPRESS_D5_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_compress_d5_tmc;;

let LENGTH_MLKEM_POLY_COMPRESS_D5_MC =
  REWRITE_CONV[mlkem_poly_compress_d5_mc] `LENGTH mlkem_poly_compress_d5_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_COMPRESS_D5_TMC =
  REWRITE_CONV[mlkem_poly_compress_d5_tmc] `LENGTH mlkem_poly_compress_d5_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH = 1`;;

let MLKEM_POLY_COMPRESS_D5_CORE_END = new_definition
  `MLKEM_POLY_COMPRESS_D5_CORE_END =
   LENGTH mlkem_poly_compress_d5_tmc - MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_COMPRESS_D5_MC;
               LENGTH_MLKEM_POLY_COMPRESS_D5_TMC;
               MLKEM_POLY_COMPRESS_D5_CORE_END;
               MLKEM_POLY_COMPRESS_D5_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

(* ------------------------------------------------------------------------- *)
(* AVX2 implementation of compress_d5 as a word expression.                  *)
(* Unlike d10/d11, d5 does NOT use Barrett reduction.                        *)
(* It uses VPMULHW directly with the constant 0x4EBF.                        *)
(* The result is a 5-bit value in the low bits of a 16-bit word.             *)
(* ------------------------------------------------------------------------- *)

let compress_d5_avx2 = new_definition
  `compress_d5_avx2 (a:16 word) : 5 word =
   word_subword (word_and
    (word_subword
      (word_add
        (word_ushr
          (word_mul
            (word_sx
              (word_subword (word_mul (word_sx a) (word 20159) : 32 word) (16,16) : 16 word))
            (word 1024) : 32 word)
          14)
        (word 1) : 32 word)
      (1,16) : 16 word)
    (word 31)) (0,5) : 5 word`;;

let compress_d5_avx2_alt = prove(
  `word_zx (compress_d5_avx2 x) : 16 word = 
       (word_and
          (word_subword
             (word_add
                (word_ushr
                   (word_mul
            (word_sx
              (word_subword (word_mul (word_sx x) (word 20159) : 32 word) (16,16) : 16 word))
            (word 1024) : 32 word)
          14)
        (word 1) : 32 word)
      (1,16) : 16 word)
    (word 31))`, 
    REWRITE_TAC [compress_d5_avx2] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for 5-bit compression                                       *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_31 = WORD_BLAST
  `word_and (x : 16 word) (word 31) =
   word_zx (word_subword x (0,5) : 5 word) : 16 word`;;

(* VPACKUSWB packs two 16-bit vectors into one 8-bit vector.
 * For 5-bit values (0..31), this is just truncation to 8 bits. *)
let WORD_PACK_5_TO_8 = WORD_BLAST
  `!x:16 word. val x < 32 ==>
   word_subword x (0,8) : 8 word = word_zx (word_subword x (0,5) : 5 word)`;;

let MULADD_32_1_JOIN = prove(
  `word_add (word_mul (word_zx (x : 5 word)) (word 1) : 32 word)
            (word_mul (word_zx (y : 5 word)) (word 32)) =
   word_zx (word_join y x : 10 word) : 32 word`,
  BITBLAST_TAC);;

(* VPMADDWD: pairs of 16-bit values packed with multiplier 0x04000001 = (1024,1)
 * This computes a*1024 + b for consecutive pairs, packing two 10-bit values
 * into a 20-bit value in a 32-bit word. *)
let MULADD_1024_1_JOIN = prove(
  `word_add (word_mul (word_sx (word_zx (x : 10 word) : 16 word) : 32 word) (word 1))
            (word_mul (word_sx (word_zx (y : 10 word) : 16 word) : 32 word) (word 1024)) =
   word_zx (word_join y x : 20 word) : 32 word`,
  BITBLAST_TAC);;

(* Combined: rewrite the VPMADDWD output in terms of compress_d5_avx2 *)
let DECOMPRESS_MULADD_D5 = prove(
  `word_add
    (word_mul (word_sx (word_zx (word_join
       (compress_d5_avx2 b) (compress_d5_avx2 a) : 10 word) : 16 word) : 32 word) (word 1))
    (word_mul (word_sx (word_zx (word_join
       (compress_d5_avx2 d) (compress_d5_avx2 c) : 10 word) : 16 word) : 32 word) (word 1024)) =
   word_zx (word_join
     (word_join (compress_d5_avx2 d)
                (compress_d5_avx2 c) : 10 word)
     (word_join (compress_d5_avx2 b)
                (compress_d5_avx2 a) : 10 word) : 20 word) : 32 word`,
  REWRITE_TAC[MULADD_1024_1_JOIN]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the per-element compression formula                        *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_CORRECT = prove(
  `!(x : 16 word). val x < 3329 ==>
   compress_d5 x = compress_d5_avx2 x`,
  let CORE = prove(
    `!(x : num). x < 3329 ==>
     compress_d5 (word x) = compress_d5_avx2 (word x)`,
    REWRITE_TAC[compress_d5; compress_d5_avx2] THEN
    BRUTE_FORCE_WITH (CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN CONV_TAC WORD_BLAST)) in
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `val(x:16 word)` CORE) THEN
  ASM_REWRITE_TAC[WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* WORD_PACKED_EQ for 160-bit words with 5-bit subwords (32 subwords)        *)
(* Each iteration outputs 32 compressed 5-bit coefficients = 160 bits.       *)
(* ------------------------------------------------------------------------- *)

let WORD_PACKED_EQ_D5 = prove(
 `!(x:160 word) (y:160 word).
    (x = y <=>
     !i. i < 32
         ==> word_subword x (5*i, 5) : (5) word =
             word_subword y (5*i, 5))`,
  REPEAT GEN_TAC THEN
  MP_TAC(INST [`5`,`l:num`; `32`,`k:num`]
    (INST_TYPE [`:160`,`:N`; `:5`,`:M`] WORD_PACKED_EQ)) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

(* Split 256 5-bit coefficients into 8 chunks of 32 (160-bit words) *)
let NUM_OF_WORDLIST_SPLIT_5_32_256 = prove(
  `!(l: (5 word) list). LENGTH l = 256 ==>
       num_of_wordlist l = num_of_wordlist (MAP ((word:num->160 word) o num_of_wordlist)
          (list_of_seq (\i. SUB_LIST (32 * i, 32) l) 8)
       )`,
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `LENGTH (l : (5 word) list) = 256` (fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATCH_MP (CONV_RULE NUM_REDUCE_CONV (ISPECL [`32`; `8`; `l:'a list`] SUBLIST_PARTITION)) th] THEN ASSUME_TAC th) THEN
  IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) (ISPECL [`ll: ((5 word) list) list`; `32`] (INST_TYPE [`:5`, `:N`; `:160`, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

(* Extract 5-bit coefficients from 160-bit packed representation (32 subwords) *)
let WORD_SUBWORD_NUM_OF_WORDLIST_32_5 = prove(`!ls:(5 word)list k.
    LENGTH ls = 32 /\ k < 32
    ==> word_subword (word (num_of_wordlist ls) : 160 word) (5*k,5) : 5 word = EL k ls`,
  let th = INST_TYPE [`:160`,`:KL`; `:5`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
  let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
  REWRITE_TAC [REWRITE_RULE[ARITH_RULE `160 = 5 * n <=> n = 32`; MESON[] `n = 32 /\ k < n <=> n = 32 /\ k < 32`] th]);;

let WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D5_32 =
  let base = WORD_SUBWORD_NUM_OF_WORDLIST_32_5 in
  let mk k =
    let th = SPEC (mk_small_numeral k) (SPEC `ls:(5 word)list` base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0--31);;

(* ------------------------------------------------------------------------- *)
(* Merge separate 128+32 memory reads into 160-bit word                      *)
(* (Same structure as d10: 20 bytes = 16 + 4)                                *)
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

let REWRITE_COMPRESS =
  let derive_instance thm tm =
    let thm' = PART_MATCH rand thm tm in
    MP thm' (EQT_ELIM(NUM_REDUCE_CONV (fst(dest_imp(concl thm')))))
  in
  (UNDISCH_THEN (`forall i. i < 256 ==> val (EL i (inlist : (16 word) list)) < 3329`) (fun thm ->
   RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (COND_REWRITE_CONV (derive_instance thm) (GSYM COMPRESS_D5_CORRECT))))
   THEN ASSUME_TAC thm
  ));;

let SIMPLIFY_WORD_ADD = RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV (COND_REWRITE_CONV WORD_BLAST WORD_ADD_OR)));;

let BIT_15_ZX_5_16 = WORD_BLAST `!a:5 word. bit 15 (word_zx a: 16 word) = false`;;
let BIT_31_ZX_10_32 = WORD_BLAST `!a:10 word. bit 31 (word_zx a: 32 word) = false`;;
let BIT_15_ZX_10_32 = WORD_BLAST `!a:10 word. bit 15 (word_zx a: 32 word) = false`;;

let MIN_ZX_5_16 = prove(
  `!a:5 word. MIN (val (word_zx a : 16 word)) 255 = val a`,
  GEN_TAC THEN
  SIMP_TAC[word_zx; VAL_WORD; DIMINDEX_16; DIMINDEX_CONV `dimindex(:5)`] THEN
  SUBGOAL_THEN `val (a:5 word) MOD 2 EXP 16 = val a` SUBST1_TAC THENL
  [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
   MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `2 EXP 5` THEN
   REWRITE_TAC[VAL_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
   MP_TAC(ISPEC `a:5 word` VAL_BOUND) THEN
   REWRITE_TAC[DIMINDEX_CONV `dimindex(:5)`] THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN ARITH_TAC] THEN
  MP_TAC(ISPEC `a:5 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN ARITH_TAC);;

let WORD_ZX_WORD_VAL_5_32 = prove(
  `(word_zx:(8)word->(32)word) ((word:num->(8)word) ((val:(5)word->num) x)) = word_zx x`, BITBLAST_TAC);;

let WORD_SUBWORD_ZX = WORD_BLAST `((word_subword:(32)word->num#num->(16)word)
      ((word_zx:(10)word->(32)word) x)) (0,16) : 16 word = word_zx x`;;
  
(* ------------------------------------------------------------------------- *)
(* Main correctness theorem                                                  *)
(* d5 processes 32 coefficients per iteration (2 VMOVDQA loads),             *)
(* outputting 160 bits = 20 bytes (128+32 split) per iteration.              *)
(* 8 iterations × 32 coefficients = 256 total.                              *)
(* 8 iterations × 20 bytes = 160 bytes total output.                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D5_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 160))
          [(word pc, LENGTH mlkem_poly_compress_d5_tmc); (a, 512); (data, 32)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_compress_d5_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d5_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = word (pc + MLKEM_POLY_COMPRESS_D5_CORE_END) /\
                read (memory :> bytes(r, 160)) s = num_of_wordlist (MAP compress_d5 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 160)] ,,
            MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8])`,

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
   `read(memory :> bytes(data,32)) s0 = num_of_wordlist ((MAP iword compress_d5_data) : (8 word) list)` THEN
  REWRITE_TAC [compress_d5_data; MAP] THEN
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

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_COMPRESS_D5_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC
    ([compress_d5_avx2_alt;
     GSYM DECOMPRESS_MULADD_D5;
     GSYM MULADD_32_1_JOIN; GSYM MULADD_1024_1_JOIN;
     GSYM (CONV_RULE NUM_REDUCE_CONV BYTES128_JOIN);
     GSYM WORD_ZX_128_256_128;
     GSYM WORD_64_SUB_8_8_JOIN_16;
     GSYM WORD_ZX_WORD_VAL_5_32;
     GSYM BIT_15_ZX_5_16; 
     GSYM BIT_31_ZX_10_32; 
     GSYM BIT_15_ZX_10_32; 
     GSYM MIN_ZX_5_16; GSYM WORD_SUBWORD_ZX;
     ADD_ASSOC; GSYM (CONV_RULE NUM_REDUCE_CONV BYTES256_JOIN)])) (1 -- 163) THEN

  DISCARD_MATCHING_ASSUMPTIONS [`read ymm s = (t : 256 word)`] THEN   
  REWRITE_COMPRESS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT (COMBINE_WBYTES_160_TAC) THEN

  SUBGOAL_THEN `LENGTH (MAP compress_d5 (inlist : (16 word) list)) = 256` ASSUME_TAC THENL [ASM_SIMP_TAC [LENGTH_MAP]; ALL_TAC] THEN
  MAP_EVERY (fun i -> SUBGOAL_THEN (subst [mk_small_numeral (32 * i), `i: num`] `LENGTH (SUB_LIST (i, 32) (MAP compress_d5 (inlist : (16 word) list))) = 32`) ASSUME_TAC
      THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC]) (0 -- 7) THEN

  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_5_32_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read c s = (t : N word)`] THEN
  REPEAT CONJ_TAC THEN

  REWRITE_TAC [WORD_PACKED_EQ_D5] THEN
  CONV_TAC (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D5_32) THEN
  REPEAT CONJ_TAC THEN
  UNDISCH_THEN `LENGTH (MAP compress_d5 (inlist : (16 word) list)) = 256` (fun th ->
    CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  ASM_SIMP_TAC [EL_MAP; ARITH] THEN
  CONV_TAC WORD_BLAST
);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrappers                                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D5_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 160))
          [(word pc, LENGTH mlkem_poly_compress_d5_tmc); (a, 512); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d5_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d5_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 160)) s = num_of_wordlist (MAP compress_d5 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 160)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_compress_d5_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D5_CORRECT));;

let MLKEM_POLY_COMPRESS_D5_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 160))
          [(word pc, LENGTH mlkem_poly_compress_d5_mc); (a, 512); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d5_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d5_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 160)) s = num_of_wordlist (MAP compress_d5 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 160)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_COMPRESS_D5_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_poly_compress_d5" subroutine_signatures)
    MLKEM_POLY_COMPRESS_D5_CORRECT
    MLKEM_POLY_COMPRESS_D5_TMC_EXEC;;

let MLKEM_POLY_COMPRESS_D5_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,160))
           [word pc,LENGTH mlkem_poly_compress_d5_tmc; a,512; data,32]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc)
                      (BUTLAST mlkem_poly_compress_d5_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + MLKEM_POLY_COMPRESS_D5_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc /\
                         memaccess_inbounds e2
                           [a,512; data,32; r,160] [r,160]))
               (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes (r,160)] ,,
              MAYCHANGE [RIP] ,,
              MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_COMPRESS_D5_TMC_EXEC);;

let MLKEM_POLY_COMPRESS_D5_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,160))
           [word pc,LENGTH mlkem_poly_compress_d5_tmc; a,512; data,32;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_compress_d5_tmc /\
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
                           [a,512; data,32; r,160; stackpointer,8]
                           [r,160; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_compress_d5_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D5_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_POLY_COMPRESS_D5_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,160))
           [word pc,LENGTH mlkem_poly_compress_d5_mc; a,512; data,32;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_compress_d5_mc /\
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
                           [a,512; data,32; r,160; stackpointer,8]
                           [r,160; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_COMPRESS_D5_NOIBT_SUBROUTINE_SAFE));;
