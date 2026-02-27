(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 11 bits.                         *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "x86_64/proofs/mlkem_compress_common.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d11.o";; *)

let mlkem_poly_compress_d11_mc =
  define_assert_from_elf "mlkem_poly_compress_d11_mc" "x86_64/mlkem/mlkem_poly_compress_d11.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xf5; 0x71; 0xf0; 0x03;
                           (* VPSLLW (%_% ymm1) (%_% ymm0) (Imm8 (word 3)) *)
  0xb8; 0x24; 0x00; 0x24; 0x00;
                           (* MOV (% eax) (Imm32 (word 2359332)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0x00; 0x20; 0x00; 0x20;
                           (* MOV (% eax) (Imm32 (word 536879104)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xb8; 0xff; 0x07; 0xff; 0x07;
                           (* MOV (% eax) (Imm32 (word 134154239)) *)
  0xc5; 0xf9; 0x6e; 0xe0;  (* VMOVD (%_% xmm4) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x08; 0x01; 0x00; 0x00; 0x08;
                           (* MOV (% rax) (Imm64 (word 576460756732608513)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xe8;
                           (* VMOVQ (%_% xmm5) (% rax) *)
  0xc4; 0xe2; 0x7d; 0x59; 0xed;
                           (* VPBROADCASTQ (%_% ymm5) (%_% xmm5) *)
  0xb8; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 10)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xf0;
                           (* VMOVQ (%_% xmm6) (% rax) *)
  0xc4; 0xe2; 0x7d; 0x59; 0xf6;
                           (* VPBROADCASTQ (%_% ymm6) (%_% xmm6) *)
  0xc5; 0xfd; 0x6f; 0x3a;  (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x42; 0x20;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0x7d; 0x6f; 0x0e;  (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x0f;  (* VMOVDQU (Memop Word128 (%% (rdi,0))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x57; 0x10;
                           (* VMOVD (Memop Doubleword (%% (rdi,16))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x57; 0x14; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,20))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x4e; 0x20;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x4f; 0x16;
                           (* VMOVDQU (Memop Word128 (%% (rdi,22))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x57; 0x26;
                           (* VMOVD (Memop Doubleword (%% (rdi,38))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x57; 0x2a; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,42))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x4e; 0x40;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x4f; 0x2c;
                           (* VMOVDQU (Memop Word128 (%% (rdi,44))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x57; 0x3c;
                           (* VMOVD (Memop Doubleword (%% (rdi,60))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x57; 0x40; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,64))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x4e; 0x60;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x4f; 0x42;
                           (* VMOVDQU (Memop Word128 (%% (rdi,66))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x57; 0x52;
                           (* VMOVD (Memop Doubleword (%% (rdi,82))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x57; 0x56; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,86))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x4f; 0x58;
                           (* VMOVDQU (Memop Word128 (%% (rdi,88))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x57; 0x68;
                           (* VMOVD (Memop Doubleword (%% (rdi,104))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x57; 0x6c; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,108))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x4f; 0x6e;
                           (* VMOVDQU (Memop Word128 (%% (rdi,110))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x57; 0x7e;
                           (* VMOVD (Memop Doubleword (%% (rdi,126))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0x82; 0x00; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,130))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0x84; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,132))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0x94; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,148))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0x98; 0x00; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,152))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0x9a; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,154))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0xaa; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,170))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0xae; 0x00; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,174))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,176))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,192))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0xc4; 0x00; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,196))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0xc6; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,198))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0xd6; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,214))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0xda; 0x00; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,218))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0xdc; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,220))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0xec; 0x00; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,236))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0xf0; 0x00; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,240))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0xf2; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,242))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0x02; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,258))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0x06; 0x01; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,262))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,264))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0x18; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,280))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0x1c; 0x01; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,284))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0x1e; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,286))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0x2e; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,302))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0x32; 0x01; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,306))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0x34; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,308))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0x44; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,324))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0x48; 0x01; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,328))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc5; 0x7d; 0x6f; 0x8e; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0x35; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xfd; 0xda;  (* VPADDW (%_% ymm11) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0x71; 0xf1; 0x03;
                           (* VPSLLW (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x2d; 0x71; 0xd2; 0x0f;
                           (* VPSRLW (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) *)
  0xc4; 0x41; 0x35; 0xf9; 0xca;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x62; 0x35; 0x0b; 0xcb;
                           (* VPMULHRSW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xdb; 0xcc;  (* VPAND (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x35; 0xf5; 0xcd;  (* VPMADDWD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x62; 0x35; 0x47; 0xce;
                           (* VPSLLVD (%_% ymm9) (%_% ymm9) (%_% ymm6) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd9; 0x08;
                           (* VPSRLDQ (%_% ymm10) (%_% ymm9) (Imm8 (word 8)) *)
  0xc4; 0x62; 0xb5; 0x45; 0xcf;
                           (* VPSRLVQ (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x22;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 34)) *)
  0xc4; 0x41; 0x35; 0xd4; 0xca;
                           (* VPADDQ (%_% ymm9) (%_% ymm9) (%_% ymm10) *)
  0xc4; 0x42; 0x35; 0x00; 0xc8;
                           (* VPSHUFB (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x7d; 0x39; 0xca; 0x01;
                           (* VEXTRACTI128 (%_% xmm10) (%_% ymm9) (Imm8 (word 1)) *)
  0xc4; 0x43; 0x31; 0x4c; 0xca; 0x80;
                           (* VPBLENDVB (%_% xmm9) (%_% xmm9) (%_% xmm10) (%_% xmm8) *)
  0xc5; 0x7a; 0x7f; 0x8f; 0x4a; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word128 (%% (rdi,330))) (%_% xmm9) *)
  0xc5; 0x79; 0x7e; 0x97; 0x5a; 0x01; 0x00; 0x00;
                           (* VMOVD (Memop Doubleword (%% (rdi,346))) (%_% xmm10) *)
  0xc4; 0x63; 0x79; 0x15; 0x97; 0x5e; 0x01; 0x00; 0x00; 0x02;
                           (* VPEXTRW (Memop Word (%% (rdi,350))) (%_% xmm10) (Imm8 (word 2)) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_poly_compress_d11_tmc =
  define_trimmed "mlkem_poly_compress_d11_tmc" mlkem_poly_compress_d11_mc;;
let MLKEM_POLY_COMPRESS_D11_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_compress_d11_tmc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_COMPRESS_D11_MC =
  REWRITE_CONV[mlkem_poly_compress_d11_mc] `LENGTH mlkem_poly_compress_d11_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_COMPRESS_D11_TMC =
  REWRITE_CONV[mlkem_poly_compress_d11_tmc] `LENGTH mlkem_poly_compress_d11_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_COMPRESS_D11_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D11_POSTAMBLE_LENGTH = 1`;;

let MLKEM_POLY_COMPRESS_D11_CORE_END = new_definition
  `MLKEM_POLY_COMPRESS_D11_CORE_END =
   LENGTH mlkem_poly_compress_d11_tmc - MLKEM_POLY_COMPRESS_D11_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_COMPRESS_D11_MC;
               LENGTH_MLKEM_POLY_COMPRESS_D11_TMC;
               MLKEM_POLY_COMPRESS_D11_CORE_END;
               MLKEM_POLY_COMPRESS_D11_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

let DIMINDEX_11 = DIMINDEX_CONV `dimindex (:11)`;;

let compress_d11_avx2 = new_definition
  `compress_d11_avx2 (a:16 word) : 16 word =
   word_and
    (word_subword
      (word_add
        (word_ushr
          (word_mul
            (word_sx
              (word_sub
                (word_subword (word_mul (word_sx (word_shl a 3)) (word 20159) : 32 word) (16,16) : 16 word)
                (word_ushr
                  (word_and (word_not (word_mul a (word 30200)))
                    (word_sub (word_mul a (word 30200))
                      (word_add a (word 36))))
                  15)))
            (word 8192) : 32 word)
          14)
        (word 1) : 32 word)
      (1,16) : 16 word)
    (word 2047)`;; 

let WORD_AND_2047 = WORD_BLAST `word_and (x : 16 word) (word 2047) = word_zx (word_subword x (0,11) : 11 word) : 16 word`;;
REWRITE_RULE [WORD_AND_2047] compress_d11_avx2

let MULADD_2048_JOIN = prove(`word_add (word_mul (word_sx (word_zx (x : 11 word) : 16 word) : 32 word) (word 1))
   (word_mul (word_sx (word_zx (y : 11 word) : 16 word) : 32 word) (word 2048)) = word_zx (word_join y x : 22 word) : 32 word`,
  BITBLAST_TAC);;

let DECOMPRESS_MULADD_2048_JOIN = prove(`((word_add:(32)word->(32)word->(32)word)
            ((word_mul:(32)word->(32)word->(32)word)
             ((word_sx:(16)word->(32)word)
             ((compress_d11_avx2:(16)word->(16)word) x))
            ((word:num->(32)word) 1))
           ((word_mul:(32)word->(32)word->(32)word)
            ((word_sx:(16)word->(32)word)
            ((compress_d11_avx2:(16)word->(16)word) y))
           ((word:num->(32)word) 2048))) = 
    word_zx (word_join (word_subword (compress_d11_avx2 y) (0,11) : 11 word) 
                       (word_subword (compress_d11_avx2 x) (0,11) : 11 word) : 22 word) : 32 word`,
  REWRITE_TAC [compress_d11_avx2; WORD_AND_2047; MULADD_2048_JOIN; WORD_BLAST 
    `!x:11 word. word_subword (word_zx x : 16 word) (0,11) : 11 word = x`]);;

let WORD_SUBWORD_USHR_HIGH_64 = REWRITE_RULE[DIMINDEX_CONV `dimindex(:64)`]
  (INST_TYPE [`:64`,`:N`] WORD_SUBWORD_USHR_HIGH);;  

let DECOMPRESS_D11_CORRECT = prove(`!(x : 16 word). val x < 3329 ==> compress_d11 x = word_subword (compress_d11_avx2 x) (0,11)`,
  let CORE = prove(`!(x : num). x < 3329 ==> compress_d11 (word x) = word_subword (compress_d11_avx2 (word x)) (0,11)`,
    REWRITE_TAC[compress_d11; compress_d11_avx2] THEN
    BRUTE_FORCE_WITH (CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV))) in
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `val(x:16 word)` CORE) THEN
  ASM_REWRITE_TAC[WORD_VAL]);;
 
type asm_info = { label: string; thm: thm; comp: string; addr: term; rhs: term };;

let COMBINE_WBYTES_176_TAC : tactic = fun (asl,w) ->
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
  let b16s  = filter (fun i -> i.comp = "bytes16") asms in
  let addr_matches base tgt i =
    let p = get_base_offset i.addr in fst p = base && snd p = tgt in
  let rec find_triple = function
    | [] -> failwith "COMBINE_WBYTES_176_TAC: no matching triple"
    | i128::rest ->
      let p = get_base_offset i128.addr in
      let base = fst p and off = snd p in
      (try
        let i32 = find (addr_matches base (off+16)) b32s in
        let i16 = find (addr_matches base (off+20)) b16s in
        [i128; i32; i16]
      with _ -> find_triple rest) in
  let trip = find_triple b128s in
  let i128 = el 0 trip and i32 = el 1 trip and i16 = el 2 trip in
  let s_tm = rand(lhand(concl i128.thm)) in
  let lemma = INST [i128.addr,`a:int64`; s_tm,`s:x86state`;
                    i128.rhs,`x0:128 word`;
                    i32.rhs,`x1:32 word`;
                    i16.rhs,`x2:16 word`] READ_MEMORY_WBYTES_MERGE_128_32_16 in
  let lemma' = CONV_RULE(DEPTH_CONV(CHANGED_CONV
    (REWRITE_CONV[WORD_ADD_ASSOC_CONSTS] THENC NUM_REDUCE_CONV))) lemma in
  let result = MP (MP (MP lemma' i128.thm) i32.thm) i16.thm in
  let drop_thms = [i128.thm; i32.thm; i16.thm] in
  let asl' = filter (fun (_,th) -> not (mem th drop_thms)) asl in  
  ASSUME_TAC result (asl',w);;

let REWRITE_COMPRESS =
   let derive_instance thm tm =
     let thm' = PART_MATCH rand thm tm in
      MP thm' (EQT_ELIM(NUM_REDUCE_CONV (fst(dest_imp(concl thm')))))
   in   
    (UNDISCH_THEN (`forall i. i < 256 ==> val (EL i (inlist : (16 word) list)) < 3329`) (fun thm -> 
     RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (COND_REWRITE_CONV (derive_instance thm) (GSYM DECOMPRESS_D11_CORRECT))))
     THEN ASSUME_TAC thm
    ));;

let SIMPLIFY_WORD_ADD = RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV (COND_REWRITE_CONV WORD_BLAST WORD_ADD_OR)));;

let MLKEM_POLY_COMPRESS_D11_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 352))
          [(word pc, LENGTH mlkem_poly_compress_d11_tmc); (a, 512); (data, 64)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_compress_d11_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 64)) s =
                  num_of_wordlist ((MAP iword compress_d11_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = word (pc + MLKEM_POLY_COMPRESS_D11_CORE_END) /\
                read (memory :> bytes(r, 352)) s = num_of_wordlist (MAP compress_d11 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 352)] ,,
            MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11])`,

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
   `read(memory :> bytes(data,64)) s0 = num_of_wordlist ((MAP iword compress_d11_data) : (8 word) list)` THEN
  REWRITE_TAC [compress_d11_data; MAP] THEN
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
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_COMPRESS_D11_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC 
    [GSYM WORD_SUBWORD_USHR_HIGH_64; GSYM WORD_SUBWORD_USHR_64; GSYM WORD_JOIN_AND_TYBIT0; GSYM WORD_JOIN_NOT_TYBIT0; compress_d11_avx2;
     GSYM DECOMPRESS_MULADD_2048_JOIN; GSYM (CONV_RULE NUM_REDUCE_CONV BYTES128_JOIN); GSYM WORD_ZX_128_256_128; GSYM WORD_64_SUB_8_8_JOIN_16]) (1 -- 389) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  RULE_ASSUM_TAC (REWRITE_RULE [WORD_ADD_0]) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read ymm s = (t : 256 word)`] THEN

  REWRITE_COMPRESS THEN 
  SIMPLIFY_WORD_ADD THEN

  REPEAT (COMBINE_WBYTES_176_TAC) THEN
  
  SUBGOAL_THEN `LENGTH (MAP compress_d11 (inlist : (16 word) list)) = 256` ASSUME_TAC THENL [ASM_SIMP_TAC [LENGTH_MAP]; ALL_TAC] THEN 
  MAP_EVERY (fun i -> SUBGOAL_THEN (subst [mk_small_numeral (16 * i), `i: num`] `LENGTH (SUB_LIST (i, 16) (MAP compress_d11 (inlist : (16 word) list))) = 16`) ASSUME_TAC
      THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC]) (0 -- 15) THEN
            
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_11_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read c s = (t : N word)`] THEN
  REPEAT CONJ_TAC THEN

  REWRITE_TAC [WORD_PACKED_EQ_D11] THEN
  CONV_TAC (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D11) THEN
  REPEAT CONJ_TAC THEN
  UNDISCH_THEN `LENGTH (MAP compress_d11 (inlist : (16 word) list)) = 256` (fun th -> 
    CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  ASM_SIMP_TAC [EL_MAP; ARITH] THEN
  CONV_TAC WORD_BLAST
);;

let MLKEM_POLY_COMPRESS_D11_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 352))
          [(word pc, LENGTH mlkem_poly_compress_d11_tmc); (a, 512); (data, 64); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d11_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 64)) s =
                  num_of_wordlist ((MAP iword compress_d11_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 352)) s = num_of_wordlist (MAP compress_d11 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 352)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_compress_d11_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D11_CORRECT));;

let MLKEM_POLY_COMPRESS_D11_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 352))
          [(word pc, LENGTH mlkem_poly_compress_d11_mc); (a, 512); (data, 64); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d11_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 64)) s =
                  num_of_wordlist ((MAP iword compress_d11_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 352)) s = num_of_wordlist (MAP compress_d11 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 352)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_COMPRESS_D11_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_poly_compress_d11" subroutine_signatures)
    MLKEM_POLY_COMPRESS_D11_CORRECT
    MLKEM_POLY_COMPRESS_D11_TMC_EXEC;;

let MLKEM_POLY_COMPRESS_D11_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,352))
           [word pc,LENGTH mlkem_poly_compress_d11_tmc; a,512; data,64]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc)
                      (BUTLAST mlkem_poly_compress_d11_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + MLKEM_POLY_COMPRESS_D11_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc /\
                         memaccess_inbounds e2
                           [a,512; data,64; r,352] [r,352]))
               (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes (r,352)] ,,
              MAYCHANGE [RIP] ,,
              MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_COMPRESS_D11_TMC_EXEC);;

let MLKEM_POLY_COMPRESS_D11_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,352))
           [word pc,LENGTH mlkem_poly_compress_d11_tmc; a,512; data,64;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_compress_d11_tmc /\
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
                           [a,512; data,64; r,352; stackpointer,8]
                           [r,352; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_compress_d11_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D11_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_POLY_COMPRESS_D11_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,352))
           [word pc,LENGTH mlkem_poly_compress_d11_mc; a,512; data,64;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_compress_d11_mc /\
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
                           [a,512; data,64; r,352; stackpointer,8]
                           [r,352; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_COMPRESS_D11_NOIBT_SUBROUTINE_SAFE));;
