(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 11 bits.                    *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "x86_64/proofs/mlkem_compress_common.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d11.o";; *)

let mlkem_poly_decompress_d11_mc =
  define_assert_from_elf "mlkem_poly_decompress_d11_mc" "x86_64/mlkem/mlkem_poly_decompress_d11.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xf0; 0x7f; 0xf0; 0x7f;
                           (* MOV (% eax) (Imm32 (word 2146467824)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xfd; 0x6f; 0x12;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfd; 0x6f; 0x5a; 0x20;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xfd; 0x6f; 0x62; 0x40;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,64))) *)
  0xc5; 0xfd; 0x6f; 0x6a; 0x60;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,96))) *)
  0xc5; 0xfa; 0x6f; 0x36;  (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,0))) *)
  0xc5; 0xf9; 0x6e; 0x7e; 0x10;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,16))) *)
  0xc5; 0xc1; 0xc4; 0x7e; 0x14; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,20))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x37;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x16;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,22))) *)
  0xc5; 0xf9; 0x6e; 0x7e; 0x26;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,38))) *)
  0xc5; 0xc1; 0xc4; 0x7e; 0x2a; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,42))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x2c;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,44))) *)
  0xc5; 0xf9; 0x6e; 0x7e; 0x3c;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,60))) *)
  0xc5; 0xc1; 0xc4; 0x7e; 0x40; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,64))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x42;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,66))) *)
  0xc5; 0xf9; 0x6e; 0x7e; 0x52;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,82))) *)
  0xc5; 0xc1; 0xc4; 0x7e; 0x56; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,86))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x58;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,88))) *)
  0xc5; 0xf9; 0x6e; 0x7e; 0x68;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,104))) *)
  0xc5; 0xc1; 0xc4; 0x7e; 0x6c; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,108))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0x76; 0x6e;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,110))) *)
  0xc5; 0xf9; 0x6e; 0x7e; 0x7e;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,126))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0x82; 0x00; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,130))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x84; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,132))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0x94; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,148))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0x98; 0x00; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,152))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x9a; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,154))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0xaa; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,170))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0xae; 0x00; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,174))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0xb0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,176))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,192))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0xc4; 0x00; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,196))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0xc6; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,198))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0xd6; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,214))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0xda; 0x00; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,218))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0xdc; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,220))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0xec; 0x00; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,236))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0xf0; 0x00; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,240))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0xf2; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,242))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0x02; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,258))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0x06; 0x01; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,262))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,264))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0x18; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,280))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0x1c; 0x01; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,284))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x1e; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,286))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0x2e; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,302))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0x32; 0x01; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,306))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x34; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,308))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0x44; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,324))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0x48; 0x01; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,328))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm6) *)
  0xc5; 0xfa; 0x6f; 0xb6; 0x4a; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% xmm6) (Memop Word128 (%% (rsi,330))) *)
  0xc5; 0xf9; 0x6e; 0xbe; 0x5a; 0x01; 0x00; 0x00;
                           (* VMOVD (%_% xmm7) (Memop Doubleword (%% (rsi,346))) *)
  0xc5; 0xc1; 0xc4; 0xbe; 0x5e; 0x01; 0x00; 0x00; 0x02;
                           (* VPINSRW (%_% xmm7) (%_% xmm7) (Memop Word (%% (rsi,350))) (Imm8 (word 2)) *)
  0xc4; 0xe3; 0x4d; 0x38; 0xf7; 0x01;
                           (* VINSERTI128 (%_% ymm6) (%_% ymm6) (%_% xmm7) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xf6; 0x94;
                           (* VPERMQ (%_% ymm6) (%_% ymm6) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x4d; 0x00; 0xf2;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xe2; 0x4d; 0x45; 0xf3;
                           (* VPSRLVD (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xe2; 0xcd; 0x45; 0xf4;
                           (* VPSRLVQ (%_% ymm6) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xcd; 0xd5; 0xf5;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x71; 0xd6; 0x01;
                           (* VPSRLW (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xcd; 0xdb; 0xf1;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf0;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm6) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_poly_decompress_d11_tmc =
  define_trimmed "mlkem_poly_decompress_d11_tmc" mlkem_poly_decompress_d11_mc;;
let MLKEM_POLY_DECOMPRESS_D11_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_decompress_d11_tmc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_POLY_DECOMPRESS_D11_MC =
  REWRITE_CONV[mlkem_poly_decompress_d11_mc] `LENGTH mlkem_poly_decompress_d11_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_DECOMPRESS_D11_TMC =
  REWRITE_CONV[mlkem_poly_decompress_d11_tmc] `LENGTH mlkem_poly_decompress_d11_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH = 1`;;

let MLKEM_POLY_DECOMPRESS_D11_CORE_END = new_definition
  `MLKEM_POLY_DECOMPRESS_D11_CORE_END =
   LENGTH mlkem_poly_decompress_d11_tmc - MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_DECOMPRESS_D11_MC;
               LENGTH_MLKEM_POLY_DECOMPRESS_D11_TMC;
               MLKEM_POLY_DECOMPRESS_D11_CORE_END;
               MLKEM_POLY_DECOMPRESS_D11_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Correctness of the decompression formula                                  *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_11 = DIMINDEX_CONV `dimindex (:11)`;;

let DECOMPRESS_D11_CORRECT = prove(
  `word_subword (word_add (word_ushr
     (word_mul (word_shl (word_zx (x : 11 word) : 32 word) 4) (word 3329 : 32 word))
     14) (word 1)) (1, 16) = decompress_d11 x`,
  REWRITE_TAC[decompress_d11; GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_ADD;
              VAL_WORD_USHR; VAL_WORD_MUL; VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:11 word` VAL_BOUND) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(x:11 word)`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;
  
let SIMP_DECOMPRESS_D11_TAC =   
  RULE_ASSUM_TAC (fun th -> let tm = concl th in
    if is_bytes256_read tm then
    CONV_RULE (TRY_CONV (DECOMPRESS_256_CONV 4 11) THENC (ONCE_REWRITE_CONV [DECOMPRESS_D11_CORRECT])) th
    else th);;

let MLKEM_POLY_DECOMPRESS_D11_CORRECT = prove(
  `!r a data (inlist:(11 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d11_tmc); (a, 352); (data, 128)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_decompress_d11_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 128)) s =
                  num_of_wordlist ((MAP iword decompress_d11_data): (8 word) list) /\
                read (memory :> bytes(a, 352)) s = num_of_wordlist inlist)
           (\s. read RIP s = word (pc + MLKEM_POLY_DECOMPRESS_D11_CORE_END) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d11 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 512)] ,,
            MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7])`,

  MAP_EVERY X_GEN_TAC
    [`r:int64`; `a:int64`; `data:int64`; `inlist:(11 word) list`; `pc:num`] THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Move to 176-bit granular preconditions for input array *)
  (* 256 coefficients * 11 bits = 2816 bits = 352 bytes *)
  (* Each chunk: 16 coefficients * 11 bits = 176 bits = 22 bytes = 16 + 4 + 2 *)
  UNDISCH_TAC `read(memory :> bytes(a,352)) s0 = num_of_wordlist(inlist: (11 word) list)` THEN
  IMP_REWRITE_TAC [NUM_OF_WORDLIST_SPLIT_11_256] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC [MAP; o_DEF] THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN

  (* Triple split: 22 = 16 + 4 + 2 bytes *)
  IMP_REWRITE_TAC [READ_MEMORY_WBYTES_SPLIT_128_32_16] THEN
  MAP_EVERY (fun n -> SUBGOAL_THEN (subst[mk_small_numeral n,`k:num`] `num_of_wordlist (SUB_LIST (16 * k,16) (inlist : (11 word) list)) < 2 EXP 176`)
     (fun th -> REWRITE_TAC[th]) THENL [
       TRANS_TAC LTE_TRANS (subst[mk_small_numeral n,`k:num`]
                            `2 EXP (dimindex(:11) * LENGTH(SUB_LIST(16*k,16) (inlist : (11 word) list)))`) THEN
       REWRITE_TAC[NUM_OF_WORDLIST_BOUND] THEN
       REWRITE_TAC[LENGTH_SUB_LIST; DIMINDEX_CONV `dimindex (:11)`] THEN
       ASM_SIMP_TAC [] THEN NUM_REDUCE_TAC;
       ALL_TAC]) (0--15) THEN
  REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (TOP_SWEEP_CONV NUM_ADD_CONV) THEN
  STRIP_TAC THEN

  (* Move to 256-bit granular precondition for constant array *)
  (* d11 uses 128 bytes of constants: 4 x 32-byte vectors *)
  UNDISCH_TAC
   `read(memory :> bytes(data,128)) s0 = num_of_wordlist ((MAP iword decompress_d11_data) : (8 word) list)` THEN
  REWRITE_TAC [decompress_d11_data; MAP] THEN
  REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                   [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN
  STRIP_TAC THEN

  (* Gather some derived preconditions for the length of sublists *)
  MAP_EVERY (fun i -> SUBGOAL_THEN (subst [mk_small_numeral (16 * i), `i: num`] `LENGTH (SUB_LIST (i, 16) (inlist : (11 word) list)) = 16`) ASSUME_TAC
    THENL [ASM_REWRITE_TAC [LENGTH_SUB_LIST] THEN NUM_REDUCE_TAC; ALL_TAC]) (0 -- 15) THEN

  (*** Symbolic execution ***)
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_DECOMPRESS_D11_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC (map GSYM (BASE_SIMPS_D11 @ WORD_MUL_2EXP @ WORD_MUL_2EXP_3329))
                      THEN SIMP_DECOMPRESS_D11_TAC) (1--218) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Unwrap assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE [WRAP]) THEN

  REPEAT (FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `read (memory :> bytes256 r) s0 = xxx`) o concl))) THEN
  TRY (IMP_REWRITE_TAC WORD_SUBWORD_NUM_OF_WORDLIST_CASES_D11) THEN
  UNDISCH_THEN `LENGTH (inlist : (11 word) list) = 256` (fun th -> CONV_TAC (TOP_SWEEP_CONV (EL_SUB_LIST_CONV th)) THEN ASSUME_TAC th) THEN
  REPEAT DISCH_TAC THEN

  (* Spell out input list entry by entry *)
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC (TOP_SWEEP_CONV LIST_OF_SEQ_CONV) THEN
  ASM_REWRITE_TAC [MAP] THEN
  (* Switch to 256-bit granularity *)
  REPLICATE_TAC 4 (CONV_TAC (ONCE_REWRITE_CONV [GSYM NUM_OF_PAIR_WORDLIST])) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC (ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM BYTES256_WBYTES]);;


let MLKEM_POLY_DECOMPRESS_D11_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(11 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d11_tmc); (a, 352); (data, 128); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d11_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 128)) s =
                  num_of_wordlist ((MAP iword decompress_d11_data): (8 word) list) /\
                read (memory :> bytes(a, 352)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d11 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d11 inlist)) /\
                                       ival (EL i (MAP decompress_d11 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d11_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D11_CORRECT) THEN
  (* Prove bounds *)
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [EL_MAP; ARITH; IVAL_DECOMPRESS_D11_BOUND]);;

let MLKEM_POLY_DECOMPRESS_D11_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(11 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 r /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_poly_decompress_d11_mc); (a, 352); (data, 128); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_decompress_d11_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 128)) s =
                  num_of_wordlist ((MAP iword decompress_d11_data): (8 word) list) /\
                read (memory :> bytes(a, 352)) s = num_of_wordlist inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 512)) s = num_of_wordlist (MAP decompress_d11 inlist) /\
                (!i. i < 256 ==> &0 <= ival (EL i (MAP decompress_d11 inlist)) /\
                                       ival (EL i (MAP decompress_d11 inlist)) < &3329))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D11_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_poly_decompress_d11" subroutine_signatures)
    MLKEM_POLY_DECOMPRESS_D11_CORRECT
    MLKEM_POLY_DECOMPRESS_D11_TMC_EXEC;;

let MLKEM_POLY_DECOMPRESS_D11_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(11 word) list) pc.
           LENGTH inlist = 256 /\
           aligned 32 r /\
           aligned 32 data /\
           ALL (nonoverlapping (r,512))
           [word pc,LENGTH mlkem_poly_decompress_d11_tmc; a,352; data,128]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc)
                      (BUTLAST mlkem_poly_decompress_d11_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s.
                    read RIP s =
                      word (pc + MLKEM_POLY_DECOMPRESS_D11_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc /\
                         memaccess_inbounds e2
                           [a,352; data,128; r,512] [r,512]))
               (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes (r,512)] ,,
              MAYCHANGE [RIP] ,,
              MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_DECOMPRESS_D11_TMC_EXEC);;

let MLKEM_POLY_DECOMPRESS_D11_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(11 word) list) pc stackpointer returnaddress.
          LENGTH inlist = 256 /\
          aligned 32 r /\
          aligned 32 data /\
          ALL (nonoverlapping (r,512))
          [word pc,LENGTH mlkem_poly_decompress_d11_tmc; a,352; data,128;
           stackpointer,8]
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_decompress_d11_tmc /\
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
                           [a,352; data,128; r,512; stackpointer,8]
                           [r,512; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_decompress_d11_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_DECOMPRESS_D11_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_POLY_DECOMPRESS_D11_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(11 word) list) pc stackpointer returnaddress.
          LENGTH inlist = 256 /\
          aligned 32 r /\
          aligned 32 data /\
          ALL (nonoverlapping (r,512))
          [word pc,LENGTH mlkem_poly_decompress_d11_mc; a,352; data,128;
           stackpointer,8]
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_decompress_d11_mc /\
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
                           [a,352; data,128; r,512; stackpointer,8]
                           [r,512; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_DECOMPRESS_D11_NOIBT_SUBROUTINE_SAFE));;
