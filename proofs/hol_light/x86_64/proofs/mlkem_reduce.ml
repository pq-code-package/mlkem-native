(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_reduce.o";; *)

let mlkem_reduce_mc =
  define_assert_from_elf "mlkem_reduce_mc" "x86_64/mlkem/mlkem_reduce.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xfd; 0x6f; 0x17;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x5f; 0x20;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x40;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x60;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0x6d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xed; 0xf9; 0xd0;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0xe5; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xdc;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xdd; 0xf9; 0xe0;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe4;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xd5; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xec;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xcd; 0xf9; 0xf0;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe6; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf4;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0xc5; 0xf9; 0xf8;  (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe7; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm7) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfc;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xf9; 0xc0;  (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe0; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm8) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xf9; 0xc8;  (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe1; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm9) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x5f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x6d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xed; 0xf9; 0xd0;  (* VPSUBW (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc5; 0xe5; 0xf9; 0xd8;  (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xdc;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0xdd; 0xf9; 0xe0;  (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe4;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xd5; 0xf9; 0xe8;  (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xec;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xcd; 0xf9; 0xf0;  (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe6; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf4;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0xc5; 0xf9; 0xf8;  (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x9d; 0x71; 0xe7; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm7) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfc;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x3d; 0xf9; 0xc0;  (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe0; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm8) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x35; 0xf9; 0xc8;  (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe1; 0x0f;
                           (* VPSRAW (%_% ymm12) (%_% ymm9) (Imm8 (word 15)) *)
  0xc5; 0x1d; 0xdb; 0xe0;  (* VPAND (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0xfd; 0x7f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm9) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_reduce_tmc = define_trimmed "mlkem_reduce_tmc" mlkem_reduce_mc;;
let mlkem_reduce_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_reduce_tmc;;

(* Enable simplification of word_subwords by default.
   Nedded to prevent the symbolic simulation to explode
   as we add more instructions. *)
let org_extra_word_conv = !extra_word_CONV;;
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ !extra_word_CONV;;

let lemma_rem = prove
 (`(y == x) (mod &3329) /\
   &0 <= y /\ y <= &6657
   ==> x rem &3329 = if y >= &3329 then y - &3329 else y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
  SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE);;

let overall_lemma = prove
 (`!x:int16.
        ival(word_add (word_sub (barred_x86 x) (word 3329))
                      (word_and (word_ishr
                                  (word_sub (barred_x86 x) (word 3329)) 15)
                                (word 3329))) =
        ival x rem &3329`,
  REWRITE_TAC[MATCH_MP lemma_rem (CONGBOUND_RULE `barred_x86 x`)] THEN
  GEN_TAC THEN MP_TAC(CONGBOUND_RULE `barred_x86 x`) THEN
  BITBLAST_TAC);;

let overall_lemma2 = SPEC_ALL overall_lemma;;
let overall_lemma3 = AP_TERM `iword:int -> (16)word` overall_lemma2 ;;
let overall_lemma4 = REWRITE_RULE[IWORD_IVAL] overall_lemma3;;

let SIMD_SIMPLIFY_TAC_LOCAL unfold_defs =
  RULE_ASSUM_TAC(CONV_RULE(SIMD_SIMPLIFY_CONV unfold_defs));;

let helper_lemma = prove
 (`!x:int16. ival(iword(ival x rem &3329):int16) = ival x rem &3329`,
  GEN_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN INT_ARITH_TAC);;

let MLKEM_REDUCE_CORRECT = prove(
  `!a x pc.
        aligned 32 a /\
        nonoverlapping (word pc, 854) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_reduce_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = word (pc + 854) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             // Registers (and memory locations) that may change after execution
             (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,512)] ,,
              MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5;
                         ZMM6; ZMM7; ZMM8; ZMM9; ZMM12])`,

  REWRITE_TAC[fst mlkem_reduce_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS] THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN

  ENSURES_INIT_TAC "s0" THEN

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add a (word n))) s0`))
            (0--15))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN


  MAP_EVERY (fun n -> X86_STEPS_TAC mlkem_reduce_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC_LOCAL[barred_x86])
            (1--166) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[GSYM barred_x86]) THEN
  SIMD_SIMPLIFY_TAC_LOCAL [] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[overall_lemma4]) THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s166" THEN
  REWRITE_TAC[GSYM barred_x86; overall_lemma4] THEN
  REWRITE_TAC[helper_lemma]
);;

let MLKEM_REDUCE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_reduce_tmc) (a, 512) /\
        nonoverlapping (stackpointer, 8) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_reduce_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
              (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(a, 512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_reduce_tmc MLKEM_REDUCE_CORRECT);;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/x86_64/src/arith_native_x86_64.h *)

let MLKEM_REDUCE_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc,LENGTH mlkem_reduce_mc) (a,512) /\
        nonoverlapping (stackpointer,8) (a,512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_reduce_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)

             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_REDUCE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_REDUCE_CORRECT
    mlkem_reduce_TMC_EXEC;;
(* Remove duplicates from memaccess_inbounds lists (s2n-bignum#350) *)
let full_spec = ONCE_DEPTH_CONV MEMACCESS_INBOUNDS_DEDUP_CONV full_spec |> concl |> rhs;;

let MLKEM_REDUCE_SAFE = time prove
 (`exists f_events.
       forall e a pc.
           aligned 32 a /\ nonoverlapping (word pc,854) (a,512)
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST mlkem_reduce_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 854) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc /\
                         memaccess_inbounds e2 [a,512] [a,512]))
               (\s s'. T)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars mlkem_reduce_TMC_EXEC);;

