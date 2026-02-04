(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of polynomial coefficients from 11 bits.                    *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
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

(* TODO: Prove correctness of poly_decompress_d11_avx2 *)
