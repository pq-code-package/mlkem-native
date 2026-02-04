(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 11 bits.                         *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
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

(* TODO: Prove correctness of poly_compress_d11_avx2 *)
