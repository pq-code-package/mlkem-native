(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 5 bits.                         *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
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

(* TODO: Prove correctness of poly_compress_d5_avx2 *)
