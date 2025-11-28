(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication of 2-element polynomial vectors in NTT domain.      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;

let mlkem_basemul_k3_mc =
  define_assert_from_elf "mlkem_basemul_k3_mc" "x86/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x01; 0xf3; 0x01; 0xf3;
                           (* MOV (% eax) (Imm32 (word 4076991233)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x5e; 0x20;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x22;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfd; 0x6f; 0x6a; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xfd; 0x6f; 0x31;  (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,0))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x3f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x56; 0x40;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0xfd; 0x6f; 0x5e; 0x60;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xfd; 0x6f; 0x62; 0x40;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,64))) *)
  0xc5; 0xfd; 0x6f; 0x6a; 0x60;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,96))) *)
  0xc5; 0xfd; 0x6f; 0x71; 0x20;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,32))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,128))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,160))) *)
  0xc5; 0xfd; 0x6f; 0x71; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,64))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,192))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,224))) *)
  0xc5; 0xfd; 0x6f; 0x71; 0x60;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,96))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,256))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,288))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,128))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,320))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,352))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,160))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,384))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,416))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,192))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,448))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,480))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,224))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,512))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,544))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,512))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,544))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,256))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x07;  (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0x7d; 0x6f; 0x57; 0x20;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x3f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,576))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,608))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,576))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,608))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,288))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x47; 0x40;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0x7d; 0x6f; 0x57; 0x60;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,640))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,672))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,640))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,672))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,320))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,704))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,736))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,704))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,736))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,352))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,768))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,800))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,768))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,800))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,384))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,832))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,864))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,832))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,864))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,416))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,896))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,928))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,896))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,928))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,448))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,960))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,992))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,960))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,992))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,480))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1024))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1056))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1024))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1056))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,512))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x07;  (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0x7d; 0x6f; 0x57; 0x20;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x3f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1088))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x60; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1120))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x40; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1088))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x60; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1120))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,544))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x47; 0x40;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0x7d; 0x6f; 0x57; 0x60;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1152))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xa0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1184))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1152))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xa0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1184))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,576))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1216))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1248))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xc0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1216))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xe0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1248))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,608))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1280))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x20; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1312))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x00; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1280))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x20; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1312))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,640))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1344))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x60; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1376))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x40; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1344))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0x60; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1376))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,672))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1408))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xa0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1440))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x80; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1408))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xa0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1440))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,704))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1472))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,1504))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xc0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1472))) *)
  0xc5; 0xfd; 0x6f; 0xaa; 0xe0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdx,1504))) *)
  0xc5; 0xfd; 0x6f; 0xb1; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rcx,736))) *)
  0xc5; 0x75; 0xd5; 0xea;  (* VPMULLW (%_% ymm13) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0x75; 0xd5; 0xf3;  (* VPMULLW (%_% ymm14) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x5d; 0xd5; 0xfd;
                           (* VPMULLW (%_% ymm7) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x55; 0xd5; 0xcd;
                           (* VPMULLW (%_% ymm9) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xd5; 0xc6;
                           (* VPMULLW (%_% ymm8) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x5d; 0xd5; 0xd6;
                           (* VPMULLW (%_% ymm10) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0xfd; 0xe5; 0xff;  (* VPMULHW (%_% ymm7) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc9;
                           (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xc0;
                           (* VPMULHW (%_% ymm8) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0x41; 0x7d; 0xe5; 0xd2;
                           (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x55; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x4d; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x5d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xa5; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc5;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0xbd; 0xfd; 0xff;  (* VPADDW (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xc9;
                           (* VPADDW (%_% ymm9) (%_% ymm10) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm9) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_basemul_k3_tmc = define_trimmed "mlkem_basemul_k3_tmc" mlkem_basemul_k3_mc;;
let mlkem_basemul_k3_tmc_EXEC = X86_MK_CORE_EXEC_RULE mlkem_basemul_k3_tmc;;

(* Enable simplification of word_subwords by default.
   Nedded to prevent the symbolic simulation to explode
   as we add more instructions. *)
let org_extra_word_conv = !extra_word_CONV;;
extra_word_CONV := [WORD_SIMPLE_SUBWORD_CONV] @ !extra_word_CONV;;


(* (a + bX) * (c + dX) = (a*c + b*dz) + (a*d + b*c)X *)
let pmul0 = define
  `pmul0 (a: int) (b : int) (c : int) (dz : int) = b*dz + a*c`;;

let pmul0_odd = define
  `pmul0_odd (a: int) (b : int) (c : int) (dz : int) = a*c - b*dz`;;

let pmul1 = define
  `pmul1 (a: int) (b : int) (c : int) (d : int) = b*c + a*d`;;

let pmulacc0_k3 = define
  `pmulacc0_k3 (a0: int) (b0 : int) (c0 : int) (d0 : int) (dz0 : int)
               (a1: int) (b1 : int) (c1 : int) (d1 : int) (dz1 : int)
               (a2: int) (b2 : int) (c2 : int) (d2 : int) (dz2 : int) =
              pmul0 a0 b0 c0 dz0 + pmul0 a1 b1 c1 dz1 + pmul0 a2 b2 c2 dz2`;;

let pmulacc0_odd_k3 = define
  `pmulacc0_odd_k3 (a0: int) (b0 : int) (c0 : int) (d0 : int) (dz0 : int)
                   (a1: int) (b1 : int) (c1 : int) (d1 : int) (dz1 : int)
                   (a2: int) (b2 : int) (c2 : int) (d2 : int) (dz2 : int) =
              pmul0_odd a0 b0 c0 dz0 + pmul0_odd a1 b1 c1 dz1 + pmul0_odd a2 b2 c2 dz2`;;

let pmulacc1_k3 = define
  `pmulacc1_k3 (a0: int) (b0 : int) (c0 : int) (d0 : int) (dz0 : int)
               (a1: int) (b1 : int) (c1 : int) (d1 : int) (dz1 : int)
               (a2: int) (b2 : int) (c2 : int) (d2 : int) (dz2 : int) =
                 pmul1 a0 b0 c0 d0 + pmul1 a1 b1 c1 d1 + pmul1 a2 b2 c2 d2`;;

let pmulaccred0_k3 = define
  `pmulaccred0_k3 (a0: int) (b0 : int) (c0 : int) (d0 : int) (dz0 : int)
                  (a1: int) (b1 : int) (c1 : int) (d1 : int) (dz1 : int)
                  (a2: int) (b2 : int) (c2 : int) (d2 : int) (dz2 : int) =
     (&(inverse_mod 3329 65536) * pmulacc0_k3 a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2) rem &3329`;;

let pmulaccred0_odd_k3 = define
  `pmulaccred0_odd_k3 (a0: int) (b0 : int) (c0 : int) (d0 : int) (dz0 : int)
                      (a1: int) (b1 : int) (c1 : int) (d1 : int) (dz1 : int)
                      (a2: int) (b2 : int) (c2 : int) (d2 : int) (dz2 : int) =
     (&(inverse_mod 3329 65536) * pmulacc0_odd_k3 a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2) rem &3329`;;


let pmulaccred1_k3 = define
  `pmulaccred1_k3 (a0: int) (b0 : int) (c0 : int) (d0 : int) (dz0 : int)
                  (a1: int) (b1 : int) (c1 : int) (d1 : int) (dz1 : int)
                  (a2: int) (b2 : int) (c2 : int) (d2 : int) (dz2 : int) =
     (&(inverse_mod 3329 65536) * pmulacc1_k3 a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2) rem &3329`;;

let MLKEM_BASEMUL_K3_CORRECT = prove(
  `!src1 src2 src2t dst a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2 pc.
        aligned 32 src1 /\
        aligned 32 src2 /\
        aligned 32 src2t /\
        aligned 32 dst /\
        ALL (nonoverlapping (dst, 512)) [(src1, 1536); (src2, 1536); (src2t, 768)] /\
        nonoverlapping (dst, 512) (word pc, 3852)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) (BUTLAST mlkem_basemul_k3_tmc) /\
                   read RIP s = word pc /\
                   C_ARGUMENTS [dst; src1; src2; src2t] s /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (64*j + 2*i)))) s = a0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (64*j + 32 + 2*i)))) s = b0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (64*j + 2*i)))) s = c0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (64*j + 32 + 2*i)))) s = d0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (32*j + 2*i)))) s = dz0 i j) /\
                             
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (512 + 64*j + 2*i)))) s = a1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (512 + 64*j + 32 + 2*i)))) s = b1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (512 + 64*j + 2*i)))) s = c1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (512 + 64*j + 32 + 2*i)))) s = d1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (256 + 32*j + 2*i)))) s = dz1 i j) /\

                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (1024 + 64*j + 2*i)))) s = a2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (1024 + 64*j + 32 + 2*i)))) s = b2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (1024 + 64*j + 2*i)))) s = c2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (1024 + 64*j + 32 + 2*i)))) s = d2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (512 + 32*j + 2*i)))) s = dz2 i j))
              (\s. read RIP s = word (pc + 3852) /\
                   (!i. i < 16 ==> !j. j < 4
                        ==> (let j' = 2*j in
                              (abs(ival(a0 i j')) <= &2 pow 12  /\
                               abs(ival(b0 i j')) <= &2 pow 12  /\
                               abs(ival(a1 i j')) <= &2 pow 12  /\
                               abs(ival(b1 i j')) <= &2 pow 12  /\
                               abs(ival(a2 i j')) <= &2 pow 12  /\
                               abs(ival(b2 i j')) <= &2 pow 12
                               ==>
                               (ival (read(memory :> bytes16 (word_add dst (word (64*j' + 2*i)))) s)
                                ==
                                pmulaccred0_k3 (ival (a0 i j')) (ival (b0 i j')) (ival (c0 i j')) (ival (d0 i j')) (ival (dz0 i j'))
                                               (ival (a1 i j')) (ival (b1 i j')) (ival (c1 i j')) (ival (d1 i j')) (ival (dz1 i j'))
                                               (ival (a2 i j')) (ival (b2 i j')) (ival (c2 i j')) (ival (d2 i j')) (ival (dz2 i j'))
                               ) (mod &3329)))) /\

                   (!i. i < 16 ==> !j. j < 4
                        ==> (let j' = 2*j+1 in
                              (abs(ival(a0 i j')) <= &2 pow 12  /\
                               abs(ival(b0 i j')) <= &2 pow 12  /\
                               abs(ival(a1 i j')) <= &2 pow 12  /\
                               abs(ival(b1 i j')) <= &2 pow 12  /\
                               abs(ival(a2 i j')) <= &2 pow 12  /\
                               abs(ival(b2 i j')) <= &2 pow 12
                               ==>
                               (ival (read(memory :> bytes16 (word_add dst (word (64*j' + 2*i)))) s)
                                ==
                                pmulaccred0_odd_k3 (ival (a0 i j')) (ival (b0 i j')) (ival (c0 i j')) (ival (d0 i j')) (ival (dz0 i j'))
                                                   (ival (a1 i j')) (ival (b1 i j')) (ival (c1 i j')) (ival (d1 i j')) (ival (dz1 i j'))
                                                   (ival (a2 i j')) (ival (b2 i j')) (ival (c2 i j')) (ival (d2 i j')) (ival (dz2 i j'))
                               ) (mod &3329)))) /\

                   (!i. i < 16 ==> !j. j < 8
                        ==> abs(ival(a0 i j)) <= &2 pow 12  /\
                            abs(ival(b0 i j)) <= &2 pow 12  /\
                            abs(ival(a1 i j)) <= &2 pow 12  /\
                            abs(ival(b1 i j)) <= &2 pow 12  /\
                            abs(ival(a2 i j)) <= &2 pow 12  /\
                            abs(ival(b2 i j)) <= &2 pow 12
                        ==> (ival (read(memory :> bytes16 (word_add dst (word (64*j + 32 + 2*i)))) s)
                             ==
                             pmulaccred1_k3 (ival (a0 i j)) (ival (b0 i j)) (ival (c0 i j)) (ival (d0 i j)) (ival (dz0 i j))
                                            (ival (a1 i j)) (ival (b1 i j)) (ival (c1 i j)) (ival (d1 i j)) (ival (dz1 i j))
                                            (ival (a2 i j)) (ival (b2 i j)) (ival (c2 i j)) (ival (d2 i j)) (ival (dz2 i j))
                            ) (mod &3329)))
              (MAYCHANGE [events] ,,
               MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
               MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                          ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14] ,,
               MAYCHANGE [memory :> bytes(dst, 512)])`,

  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst mlkem_basemul_k3_tmc_EXEC] THEN
  REPEAT STRIP_TAC THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC(TOP_DEPTH_CONV NUM_MULT_CONV THENC
           TOP_DEPTH_CONV NUM_ADD_CONV) THEN

  ENSURES_INIT_TAC "s0" THEN

  MEMORY_256_FROM_16_TAC "src1" 64 THEN
  MEMORY_256_FROM_16_TAC "src2" 64 THEN
  MEMORY_256_FROM_16_TAC "src2t" 32 THEN

  ASM_REWRITE_TAC [WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 any) s = x`] THEN
  REPEAT STRIP_TAC THEN

  MAP_EVERY (fun n -> X86_STEPS_TAC mlkem_basemul_k3_tmc_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC [montmul_x86; montmul_odd_x86])
            (1--718) THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC
           DEPTH_CONV NUM_ADD_CONV THENC
           DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC
           DEPTH_CONV NUM_ADD_CONV THENC
           DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN

  DISCARD_STATE_TAC "s718" THEN

  REPEAT CONJ_TAC THEN
  REWRITE_TAC[pmulaccred0_k3; pmulacc0_k3; pmul0; pmulaccred0_odd_k3;
              pmulacc0_odd_k3; pmul0_odd; pmulaccred1_k3; pmulacc1_k3; pmul1] THEN
  STRIP_TAC THEN
  ASSUM_LIST((fun ths -> W(MP_TAC o CONJUNCT1 o GEN_CONGBOUND_RULE ths o
    rand o lhand o rator o snd))) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING
);;

let MLKEM_BASEMUL_K3_NOIBT_SUBROUTINE_CORRECT = prove(
  `!src1 src2 src2t dst a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2 pc stackpointer returnaddress.
        aligned 32 src1 /\
        aligned 32 src2 /\
        aligned 32 src2t /\
        aligned 32 dst /\
        ALL (nonoverlapping (dst, 512)) [(src1, 1536); (src2, 1536); (src2t, 768)] /\
        nonoverlapping (dst, 512) (word pc, LENGTH mlkem_basemul_k3_tmc) /\
        nonoverlapping (dst, 512) (stackpointer, 8)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mlkem_basemul_k3_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   C_ARGUMENTS [dst; src1; src2; src2t] s /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (64*j + 2*i)))) s = a0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (64*j + 32 + 2*i)))) s = b0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (64*j + 2*i)))) s = c0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (64*j + 32 + 2*i)))) s = d0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (32*j + 2*i)))) s = dz0 i j) /\
                             
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (512 + 64*j + 2*i)))) s = a1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (512 + 64*j + 32 + 2*i)))) s = b1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (512 + 64*j + 2*i)))) s = c1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (512 + 64*j + 32 + 2*i)))) s = d1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (256 + 32*j + 2*i)))) s = dz1 i j) /\

                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (1024 + 64*j + 2*i)))) s = a2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (1024 + 64*j + 32 + 2*i)))) s = b2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (1024 + 64*j + 2*i)))) s = c2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (1024 + 64*j + 32 + 2*i)))) s = d2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (512 + 32*j + 2*i)))) s = dz2 i j))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (!i. i < 16 ==> !j. j < 4
                        ==> (let j' = 2*j in
                              (abs(ival(a0 i j')) <= &2 pow 12  /\
                               abs(ival(b0 i j')) <= &2 pow 12  /\
                               abs(ival(a1 i j')) <= &2 pow 12  /\
                               abs(ival(b1 i j')) <= &2 pow 12  /\
                               abs(ival(a2 i j')) <= &2 pow 12  /\
                               abs(ival(b2 i j')) <= &2 pow 12
                               ==>
                               (ival (read(memory :> bytes16 (word_add dst (word (64*j' + 2*i)))) s)
                                ==
                                pmulaccred0_k3 (ival (a0 i j')) (ival (b0 i j')) (ival (c0 i j')) (ival (d0 i j')) (ival (dz0 i j'))
                                               (ival (a1 i j')) (ival (b1 i j')) (ival (c1 i j')) (ival (d1 i j')) (ival (dz1 i j'))
                                               (ival (a2 i j')) (ival (b2 i j')) (ival (c2 i j')) (ival (d2 i j')) (ival (dz2 i j'))
                               ) (mod &3329)))) /\

                   (!i. i < 16 ==> !j. j < 4
                        ==> (let j' = 2*j+1 in
                              (abs(ival(a0 i j')) <= &2 pow 12  /\
                               abs(ival(b0 i j')) <= &2 pow 12  /\
                               abs(ival(a1 i j')) <= &2 pow 12  /\
                               abs(ival(b1 i j')) <= &2 pow 12  /\
                               abs(ival(a2 i j')) <= &2 pow 12  /\
                               abs(ival(b2 i j')) <= &2 pow 12
                               ==>
                               (ival (read(memory :> bytes16 (word_add dst (word (64*j' + 2*i)))) s)
                                ==
                                pmulaccred0_odd_k3 (ival (a0 i j')) (ival (b0 i j')) (ival (c0 i j')) (ival (d0 i j')) (ival (dz0 i j'))
                                                   (ival (a1 i j')) (ival (b1 i j')) (ival (c1 i j')) (ival (d1 i j')) (ival (dz1 i j'))
                                                   (ival (a2 i j')) (ival (b2 i j')) (ival (c2 i j')) (ival (d2 i j')) (ival (dz2 i j'))
                               ) (mod &3329)))) /\

                   (!i. i < 16 ==> !j. j < 8
                        ==> abs(ival(a0 i j)) <= &2 pow 12  /\
                            abs(ival(b0 i j)) <= &2 pow 12  /\
                            abs(ival(a1 i j)) <= &2 pow 12  /\
                            abs(ival(b1 i j)) <= &2 pow 12  /\
                            abs(ival(a2 i j)) <= &2 pow 12  /\
                            abs(ival(b2 i j)) <= &2 pow 12
                        ==> (ival (read(memory :> bytes16 (word_add dst (word (64*j + 32 + 2*i)))) s)
                             ==
                             pmulaccred1_k3 (ival (a0 i j)) (ival (b0 i j)) (ival (c0 i j)) (ival (d0 i j)) (ival (dz0 i j))
                                            (ival (a1 i j)) (ival (b1 i j)) (ival (c1 i j)) (ival (d1 i j)) (ival (dz1 i j))
                                            (ival (a2 i j)) (ival (b2 i j)) (ival (c2 i j)) (ival (d2 i j)) (ival (dz2 i j))
                            ) (mod &3329)))
              (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(dst, 512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_basemul_k3_tmc MLKEM_BASEMUL_K3_CORRECT);;

let MLKEM_BASEMUL_K3_SUBROUTINE_CORRECT = prove(
  `!src1 src2 src2t dst a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2 pc stackpointer returnaddress.
        aligned 32 src1 /\
        aligned 32 src2 /\
        aligned 32 src2t /\
        aligned 32 dst /\
        ALL (nonoverlapping (dst, 512)) [(src1, 1536); (src2, 1536); (src2t, 768)] /\
        nonoverlapping (dst, 512) (word pc, LENGTH mlkem_basemul_k3_mc) /\
        nonoverlapping (dst, 512) (stackpointer, 8)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mlkem_basemul_k3_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   C_ARGUMENTS [dst; src1; src2; src2t] s /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (64*j + 2*i)))) s = a0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (64*j + 32 + 2*i)))) s = b0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (64*j + 2*i)))) s = c0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (64*j + 32 + 2*i)))) s = d0 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (32*j + 2*i)))) s = dz0 i j) /\
                             
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (512 + 64*j + 2*i)))) s = a1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (512 + 64*j + 32 + 2*i)))) s = b1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (512 + 64*j + 2*i)))) s = c1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (512 + 64*j + 32 + 2*i)))) s = d1 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (256 + 32*j + 2*i)))) s = dz1 i j) /\

                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (1024 + 64*j + 2*i)))) s = a2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src1 (word (1024 + 64*j + 32 + 2*i)))) s = b2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (1024 + 64*j + 2*i)))) s = c2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2 (word (1024 + 64*j + 32 + 2*i)))) s = d2 i j) /\
                   (!i. i < 16 ==> !j. j < 8
                        ==> read(memory :> bytes16
                             (word_add src2t (word (512 + 32*j + 2*i)))) s = dz2 i j))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   (!i. i < 16 ==> !j. j < 4
                        ==> (let j' = 2*j in
                              (abs(ival(a0 i j')) <= &2 pow 12  /\
                               abs(ival(b0 i j')) <= &2 pow 12  /\
                               abs(ival(a1 i j')) <= &2 pow 12  /\
                               abs(ival(b1 i j')) <= &2 pow 12  /\
                               abs(ival(a2 i j')) <= &2 pow 12  /\
                               abs(ival(b2 i j')) <= &2 pow 12
                               ==>
                               (ival (read(memory :> bytes16 (word_add dst (word (64*j' + 2*i)))) s)
                                ==
                                pmulaccred0_k3 (ival (a0 i j')) (ival (b0 i j')) (ival (c0 i j')) (ival (d0 i j')) (ival (dz0 i j'))
                                               (ival (a1 i j')) (ival (b1 i j')) (ival (c1 i j')) (ival (d1 i j')) (ival (dz1 i j'))
                                               (ival (a2 i j')) (ival (b2 i j')) (ival (c2 i j')) (ival (d2 i j')) (ival (dz2 i j'))
                               ) (mod &3329)))) /\

                   (!i. i < 16 ==> !j. j < 4
                        ==> (let j' = 2*j+1 in
                              (abs(ival(a0 i j')) <= &2 pow 12  /\
                               abs(ival(b0 i j')) <= &2 pow 12  /\
                               abs(ival(a1 i j')) <= &2 pow 12  /\
                               abs(ival(b1 i j')) <= &2 pow 12  /\
                               abs(ival(a2 i j')) <= &2 pow 12  /\
                               abs(ival(b2 i j')) <= &2 pow 12
                               ==>
                               (ival (read(memory :> bytes16 (word_add dst (word (64*j' + 2*i)))) s)
                                ==
                                pmulaccred0_odd_k3 (ival (a0 i j')) (ival (b0 i j')) (ival (c0 i j')) (ival (d0 i j')) (ival (dz0 i j'))
                                                   (ival (a1 i j')) (ival (b1 i j')) (ival (c1 i j')) (ival (d1 i j')) (ival (dz1 i j'))
                                                   (ival (a2 i j')) (ival (b2 i j')) (ival (c2 i j')) (ival (d2 i j')) (ival (dz2 i j'))
                               ) (mod &3329)))) /\

                   (!i. i < 16 ==> !j. j < 8
                        ==> abs(ival(a0 i j)) <= &2 pow 12  /\
                            abs(ival(b0 i j)) <= &2 pow 12  /\
                            abs(ival(a1 i j)) <= &2 pow 12  /\
                            abs(ival(b1 i j)) <= &2 pow 12  /\
                            abs(ival(a2 i j)) <= &2 pow 12  /\
                            abs(ival(b2 i j)) <= &2 pow 12
                        ==> (ival (read(memory :> bytes16 (word_add dst (word (64*j + 32 + 2*i)))) s)
                             ==
                             pmulaccred1_k3 (ival (a0 i j)) (ival (b0 i j)) (ival (c0 i j)) (ival (d0 i j)) (ival (dz0 i j))
                                            (ival (a1 i j)) (ival (b1 i j)) (ival (c1 i j)) (ival (d1 i j)) (ival (dz1 i j))
                                            (ival (a2 i j)) (ival (b2 i j)) (ival (c2 i j)) (ival (d2 i j)) (ival (dz2 i j))
                            ) (mod &3329)))
              (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(dst, 512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_BASEMUL_K3_NOIBT_SUBROUTINE_CORRECT));;

