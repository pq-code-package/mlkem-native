(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
needs "x86_64/proofs/mlkem_zetas.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_intt.o";; *)

let mlkem_intt_mc = define_assert_from_elf "mlkem_intt_mc" "x86_64/mlkem/mlkem_intt.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xa1; 0xd8; 0xa1; 0xd8;
                           (* MOV (% eax) (Imm32 (word 3634485409)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0xa1; 0x05; 0xa1; 0x05;
                           (* MOV (% eax) (Imm32 (word 94438817)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x5d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xe5; 0xe3;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x4d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xcd; 0xe5; 0xf3;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x55; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xd5; 0xe5; 0xeb;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x45; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0xc5; 0xe5; 0xfb;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0x3d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x3d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x2d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0x2d; 0xe5; 0xd3;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc5; 0x35; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x35; 0xe5; 0xcb;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0x25; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm11) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xdb;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x25; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm11) (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x63; 0xfd; 0x00; 0xbe; 0xa0; 0x03; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm15) (Memop Word256 (%% (rsi,928))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x8e; 0x60; 0x03; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm1) (Memop Word256 (%% (rsi,864))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0xc0; 0x03; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,960))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x9e; 0x80; 0x03; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm3) (Memop Word256 (%% (rsi,896))) (Imm8 (word 78)) *)
  0xc5; 0x7d; 0x6f; 0x26;  (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsi,0))) *)
  0xc4; 0x42; 0x05; 0x00; 0xfc;
                           (* VPSHUFB (%_% ymm15) (%_% ymm15) (%_% ymm12) *)
  0xc4; 0xc2; 0x75; 0x00; 0xcc;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0xc2; 0x6d; 0x00; 0xd4;
                           (* VPSHUFB (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc4; 0xc2; 0x65; 0x00; 0xdc;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x4d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm12) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xdd; 0xfd; 0xe6;  (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0x45; 0xf9; 0xed;  (* VPSUBW (%_% ymm13) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xc1; 0x1d; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm6) (%_% ymm12) (%_% ymm15) *)
  0xc5; 0xd5; 0xfd; 0xef;  (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xf0;
                           (* VPSUBW (%_% ymm14) (%_% ymm10) (%_% ymm8) *)
  0xc4; 0xc1; 0x15; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm7) (%_% ymm13) (%_% ymm15) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc2;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x25; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm9) *)
  0xc5; 0x0d; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm14) (%_% ymm1) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcb;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xd9;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm1) *)
  0xc5; 0x1d; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x15; 0xe5; 0xea;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm2) *)
  0xc5; 0x0d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm3) *)
  0xc5; 0x05; 0xe5; 0xfb;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm3) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm6) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x95; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm13) (%_% ymm7) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0x20; 0x03; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,800))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x9e; 0x40; 0x03; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm3) (Memop Word256 (%% (rsi,832))) (Imm8 (word 78)) *)
  0xc5; 0xfd; 0x6f; 0x0e;  (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,0))) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xd1;
                           (* VPSHUFB (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xe2; 0x65; 0x00; 0xd9;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x3d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe0;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc5; 0x35; 0xf9; 0xed;  (* VPSUBW (%_% ymm13) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x1d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xe9;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc5; 0x2d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm10) (%_% ymm6) *)
  0xc5; 0x15; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf2;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc5; 0x25; 0xf9; 0xff;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm7) *)
  0xc5; 0x0d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfb;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe3;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x15; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm3) *)
  0xc5; 0x0d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm3) *)
  0xc5; 0x05; 0xe5; 0xfb;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm3) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm13) (%_% ymm9) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0xe5; 0x72; 0xf5; 0x10;
                           (* VPSLLD (%_% ymm3) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xd4; 0x10;
                           (* VPSRLD (%_% ymm4) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xf7; 0x10;
                           (* VPSLLD (%_% ymm4) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x4d; 0x72; 0xf1; 0x10;
                           (* VPSLLD (%_% ymm6) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x3d; 0x0e; 0xf6; 0xaa;
                           (* VPBLENDW (%_% ymm6) (%_% ymm8) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xd0; 0x10;
                           (* VPSRLD (%_% ymm8) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x3d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm8) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xf3; 0x10;
                           (* VPSLLD (%_% ymm8) (%_% ymm11) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x2d; 0x0e; 0xc0; 0xaa;
                           (* VPBLENDW (%_% ymm8) (%_% ymm10) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x72; 0xd2; 0x10;
                           (* VPSRLD (%_% ymm10) (%_% ymm10) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x2d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0x7d; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsi,32))) *)
  0xc4; 0xe2; 0x1d; 0x36; 0x96; 0xe0; 0x02; 0x00; 0x00;
                           (* VPERMD (%_% ymm2) (%_% ymm12) (Memop Word256 (%% (rsi,736))) *)
  0xc4; 0x62; 0x1d; 0x36; 0x96; 0x00; 0x03; 0x00; 0x00;
                           (* VPERMD (%_% ymm10) (%_% ymm12) (Memop Word256 (%% (rsi,768))) *)
  0xc5; 0x55; 0xf9; 0xe3;  (* VPSUBW (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xe5; 0xfd; 0xdd;  (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0x45; 0xf9; 0xec;  (* VPSUBW (%_% ymm13) (%_% ymm7) (%_% ymm4) *)
  0xc5; 0x9d; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0xdd; 0xfd; 0xe7;  (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm7) *)
  0xc5; 0x35; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm9) (%_% ymm6) *)
  0xc5; 0x95; 0xd5; 0xfa;  (* VPMULLW (%_% ymm7) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf1;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0xc4; 0x41; 0x25; 0xf9; 0xf8;
                           (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm8) *)
  0xc5; 0x0d; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc3;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x41; 0x1d; 0xe5; 0xe2;
                           (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x15; 0xe5; 0xea;
                           (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm10) *)
  0xc4; 0x41; 0x0d; 0xe5; 0xf2;
                           (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xe5; 0xfa;
                           (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm10) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0x95; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm13) (%_% ymm7) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm14) (%_% ymm9) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x7e; 0x12; 0xd4;  (* VMOVSLDUP (%_% ymm10) (%_% ymm4) *)
  0xc4; 0x43; 0x65; 0x02; 0xd2; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm3) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xd8;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm8) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm6) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm6) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xf7;  (* VMOVSLDUP (%_% ymm6) (%_% ymm7) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xeb;
                           (* VMOVSLDUP (%_% ymm5) (%_% ymm11) *)
  0xc4; 0xe3; 0x35; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm9) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x35; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm9) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0xa0; 0x02; 0x00; 0x00; 0x1b;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,672))) (Imm8 (word 27)) *)
  0xc4; 0x63; 0xfd; 0x00; 0x8e; 0xc0; 0x02; 0x00; 0x00; 0x1b;
                           (* VPERMQ (%_% ymm9) (Memop Word256 (%% (rsi,704))) (Imm8 (word 27)) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xe2;
                           (* VPSUBW (%_% ymm12) (%_% ymm4) (%_% ymm10) *)
  0xc5; 0x2d; 0xfd; 0xd4;  (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm4) *)
  0xc5; 0x3d; 0xf9; 0xeb;  (* VPSUBW (%_% ymm13) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x9d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xd8;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm8) *)
  0xc5; 0x45; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0x15; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm13) (%_% ymm2) *)
  0xc5; 0xcd; 0xfd; 0xf7;  (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0x25; 0xf9; 0xfd;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm5) *)
  0xc5; 0x8d; 0xd5; 0xfa;  (* VPMULLW (%_% ymm7) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xeb;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x41; 0x1d; 0xe5; 0xe1;
                           (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xe5; 0xe9;
                           (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm9) *)
  0xc4; 0x41; 0x0d; 0xe5; 0xf1;
                           (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm9) *)
  0xc4; 0x41; 0x05; 0xe5; 0xf9;
                           (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm9) *)
  0xc5; 0xdd; 0xe5; 0xe0;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm4) (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc5; 0x8d; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm14) (%_% ymm7) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0x2d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc5; 0x2d; 0x6c; 0xcb;  (* VPUNPCKLQDQ (%_% ymm9) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0xad; 0x6d; 0xdb;  (* VPUNPCKHQDQ (%_% ymm3) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0x4d; 0x6c; 0xd5;  (* VPUNPCKLQDQ (%_% ymm10) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm6) (%_% ymm5) *)
  0xc4; 0xc1; 0x5d; 0x6c; 0xf0;
                           (* VPUNPCKLQDQ (%_% ymm6) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x5d; 0x6d; 0xc0;
                           (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x45; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0x60; 0x02; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,608))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xbe; 0x80; 0x02; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm7) (Memop Word256 (%% (rsi,640))) (Imm8 (word 78)) *)
  0xc4; 0x41; 0x65; 0xf9; 0xe1;
                           (* VPSUBW (%_% ymm12) (%_% ymm3) (%_% ymm9) *)
  0xc5; 0x35; 0xfd; 0xcb;  (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc4; 0x41; 0x55; 0xf9; 0xea;
                           (* VPSUBW (%_% ymm13) (%_% ymm5) (%_% ymm10) *)
  0xc5; 0x9d; 0xd5; 0xda;  (* VPMULLW (%_% ymm3) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x2d; 0xfd; 0xd5;  (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm5) *)
  0xc5; 0x3d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x95; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf0;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm8) *)
  0xc5; 0x25; 0xf9; 0xfc;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm4) *)
  0xc5; 0x0d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe3;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe7;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x15; 0xe5; 0xef;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm7) *)
  0xc5; 0x0d; 0xe5; 0xf7;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm7) *)
  0xc5; 0x05; 0xe5; 0xff;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm7) *)
  0xc5; 0xe5; 0xe5; 0xd8;  (* VPMULHW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xdb;  (* VPSUBW (%_% ymm3) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x95; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm13) (%_% ymm5) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm14) (%_% ymm8) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc3; 0x35; 0x46; 0xfa; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm9) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x35; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm9) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0x63; 0x4d; 0x46; 0xcc; 0x20;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm6) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x46; 0xe4; 0x31;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x65; 0x46; 0xf5; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm3) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x46; 0xed; 0x31;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x3d; 0x46; 0xdb; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm8) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x3d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm8) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,544))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,576))) *)
  0xc5; 0x2d; 0xf9; 0xe7;  (* VPSUBW (%_% ymm12) (%_% ymm10) (%_% ymm7) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfa;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm10) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xe9;
                           (* VPSUBW (%_% ymm13) (%_% ymm4) (%_% ymm9) *)
  0xc5; 0x1d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x35; 0xfd; 0xcc;  (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x55; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0x95; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm13) (%_% ymm2) *)
  0xc5; 0xcd; 0xfd; 0xf5;  (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0x25; 0xf9; 0xfb;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm3) *)
  0xc5; 0x8d; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xdb;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x41; 0x1d; 0xe5; 0xe0;
                           (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x15; 0xe5; 0xe8;
                           (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xe5; 0xf0;
                           (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm8) *)
  0xc4; 0x41; 0x05; 0xe5; 0xf8;
                           (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm8) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0xdd; 0xe5; 0xe0;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x95; 0xf9; 0xe4;  (* VPSUBW (%_% ymm4) (%_% ymm13) (%_% ymm4) *)
  0xc5; 0x8d; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm14) (%_% ymm5) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xfd; 0x7f; 0x3f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x4f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0x5f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm5) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm11) *)
  0xb8; 0xa1; 0xd8; 0xa1; 0xd8;
                           (* MOV (% eax) (Imm32 (word 3634485409)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0xa1; 0x05; 0xa1; 0x05;
                           (* MOV (% eax) (Imm32 (word 94438817)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0x5d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xdd; 0xe5; 0xe3;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x4d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xcd; 0xe5; 0xf3;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x55; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xd5; 0xe5; 0xeb;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xec;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x45; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0xc5; 0xe5; 0xfb;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x3d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x3d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x2d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0x2d; 0xe5; 0xd3;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc5; 0x35; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x35; 0xe5; 0xcb;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0x25; 0xd5; 0xe2;  (* VPMULLW (%_% ymm12) (%_% ymm11) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xdb;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm3) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x25; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm11) (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x63; 0xfd; 0x00; 0xbe; 0xe0; 0x01; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm15) (Memop Word256 (%% (rsi,480))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x8e; 0xa0; 0x01; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm1) (Memop Word256 (%% (rsi,416))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0x00; 0x02; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,512))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x9e; 0xc0; 0x01; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm3) (Memop Word256 (%% (rsi,448))) (Imm8 (word 78)) *)
  0xc5; 0x7d; 0x6f; 0x26;  (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsi,0))) *)
  0xc4; 0x42; 0x05; 0x00; 0xfc;
                           (* VPSHUFB (%_% ymm15) (%_% ymm15) (%_% ymm12) *)
  0xc4; 0xc2; 0x75; 0x00; 0xcc;
                           (* VPSHUFB (%_% ymm1) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0xc2; 0x6d; 0x00; 0xd4;
                           (* VPSHUFB (%_% ymm2) (%_% ymm2) (%_% ymm12) *)
  0xc4; 0xc2; 0x65; 0x00; 0xdc;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x4d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm12) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xdd; 0xfd; 0xe6;  (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0x45; 0xf9; 0xed;  (* VPSUBW (%_% ymm13) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xc1; 0x1d; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm6) (%_% ymm12) (%_% ymm15) *)
  0xc5; 0xd5; 0xfd; 0xef;  (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xf0;
                           (* VPSUBW (%_% ymm14) (%_% ymm10) (%_% ymm8) *)
  0xc4; 0xc1; 0x15; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm7) (%_% ymm13) (%_% ymm15) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc2;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x25; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm9) *)
  0xc5; 0x0d; 0xd5; 0xd1;  (* VPMULLW (%_% ymm10) (%_% ymm14) (%_% ymm1) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcb;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xd9;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm1) *)
  0xc5; 0x1d; 0xe5; 0xe2;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x15; 0xe5; 0xea;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm2) *)
  0xc5; 0x0d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm3) *)
  0xc5; 0x05; 0xe5; 0xfb;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm3) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm6) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x95; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm13) (%_% ymm7) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0x60; 0x01; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,352))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x9e; 0x80; 0x01; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm3) (Memop Word256 (%% (rsi,384))) (Imm8 (word 78)) *)
  0xc5; 0xfd; 0x6f; 0x0e;  (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,0))) *)
  0xc4; 0xe2; 0x6d; 0x00; 0xd1;
                           (* VPSHUFB (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc4; 0xe2; 0x65; 0x00; 0xd9;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x3d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe0;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc5; 0x35; 0xf9; 0xed;  (* VPSUBW (%_% ymm13) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x1d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xe9;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc5; 0x2d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm10) (%_% ymm6) *)
  0xc5; 0x15; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf2;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc5; 0x25; 0xf9; 0xff;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm7) *)
  0xc5; 0x0d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfb;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe3;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x15; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm3) *)
  0xc5; 0x0d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm3) *)
  0xc5; 0x05; 0xe5; 0xfb;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm3) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm13) (%_% ymm9) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0xe5; 0x72; 0xf5; 0x10;
                           (* VPSLLD (%_% ymm3) (%_% ymm5) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xd4; 0x10;
                           (* VPSRLD (%_% ymm4) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xf7; 0x10;
                           (* VPSLLD (%_% ymm4) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xe4; 0xaa;
                           (* VPBLENDW (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x4d; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x4d; 0x72; 0xf1; 0x10;
                           (* VPSLLD (%_% ymm6) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x3d; 0x0e; 0xf6; 0xaa;
                           (* VPBLENDW (%_% ymm6) (%_% ymm8) (%_% ymm6) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xd0; 0x10;
                           (* VPSRLD (%_% ymm8) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x3d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm8) (%_% ymm9) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x3d; 0x72; 0xf3; 0x10;
                           (* VPSLLD (%_% ymm8) (%_% ymm11) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x2d; 0x0e; 0xc0; 0xaa;
                           (* VPBLENDW (%_% ymm8) (%_% ymm10) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x72; 0xd2; 0x10;
                           (* VPSRLD (%_% ymm10) (%_% ymm10) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x2d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0x7d; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsi,32))) *)
  0xc4; 0xe2; 0x1d; 0x36; 0x96; 0x20; 0x01; 0x00; 0x00;
                           (* VPERMD (%_% ymm2) (%_% ymm12) (Memop Word256 (%% (rsi,288))) *)
  0xc4; 0x62; 0x1d; 0x36; 0x96; 0x40; 0x01; 0x00; 0x00;
                           (* VPERMD (%_% ymm10) (%_% ymm12) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x55; 0xf9; 0xe3;  (* VPSUBW (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xe5; 0xfd; 0xdd;  (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0x45; 0xf9; 0xec;  (* VPSUBW (%_% ymm13) (%_% ymm7) (%_% ymm4) *)
  0xc5; 0x9d; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0xdd; 0xfd; 0xe7;  (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm7) *)
  0xc5; 0x35; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm9) (%_% ymm6) *)
  0xc5; 0x95; 0xd5; 0xfa;  (* VPMULLW (%_% ymm7) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf1;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0xc4; 0x41; 0x25; 0xf9; 0xf8;
                           (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm8) *)
  0xc5; 0x0d; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc3;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x41; 0x1d; 0xe5; 0xe2;
                           (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x15; 0xe5; 0xea;
                           (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm10) *)
  0xc4; 0x41; 0x0d; 0xe5; 0xf2;
                           (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xe5; 0xfa;
                           (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm10) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm12) (%_% ymm5) *)
  0xc5; 0x95; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm13) (%_% ymm7) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm14) (%_% ymm9) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xc5; 0x65; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc5; 0x7e; 0x12; 0xd4;  (* VMOVSLDUP (%_% ymm10) (%_% ymm4) *)
  0xc4; 0x43; 0x65; 0x02; 0xd2; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm3) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xd8;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm8) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm6) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm6) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xf7;  (* VMOVSLDUP (%_% ymm6) (%_% ymm7) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xeb;
                           (* VMOVSLDUP (%_% ymm5) (%_% ymm11) *)
  0xc4; 0xe3; 0x35; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm9) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x35; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm9) (%_% ymm11) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0xe0; 0x00; 0x00; 0x00; 0x1b;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,224))) (Imm8 (word 27)) *)
  0xc4; 0x63; 0xfd; 0x00; 0x8e; 0x00; 0x01; 0x00; 0x00; 0x1b;
                           (* VPERMQ (%_% ymm9) (Memop Word256 (%% (rsi,256))) (Imm8 (word 27)) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xe2;
                           (* VPSUBW (%_% ymm12) (%_% ymm4) (%_% ymm10) *)
  0xc5; 0x2d; 0xfd; 0xd4;  (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm4) *)
  0xc5; 0x3d; 0xf9; 0xeb;  (* VPSUBW (%_% ymm13) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x9d; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xd8;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm8) *)
  0xc5; 0x45; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0x15; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm13) (%_% ymm2) *)
  0xc5; 0xcd; 0xfd; 0xf7;  (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0x25; 0xf9; 0xfd;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm5) *)
  0xc5; 0x8d; 0xd5; 0xfa;  (* VPMULLW (%_% ymm7) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xeb;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x41; 0x1d; 0xe5; 0xe1;
                           (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x41; 0x15; 0xe5; 0xe9;
                           (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm9) *)
  0xc4; 0x41; 0x0d; 0xe5; 0xf1;
                           (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm9) *)
  0xc4; 0x41; 0x05; 0xe5; 0xf9;
                           (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm9) *)
  0xc5; 0xdd; 0xe5; 0xe0;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm4) (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm13) (%_% ymm8) *)
  0xc5; 0x8d; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm14) (%_% ymm7) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0x2d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xd4;
                           (* VPSUBW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc5; 0x2d; 0x6c; 0xcb;  (* VPUNPCKLQDQ (%_% ymm9) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0xad; 0x6d; 0xdb;  (* VPUNPCKHQDQ (%_% ymm3) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0x4d; 0x6c; 0xd5;  (* VPUNPCKLQDQ (%_% ymm10) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm6) (%_% ymm5) *)
  0xc4; 0xc1; 0x5d; 0x6c; 0xf0;
                           (* VPUNPCKLQDQ (%_% ymm6) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x5d; 0x6d; 0xc0;
                           (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x45; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xe3; 0xfd; 0x00; 0x96; 0xa0; 0x00; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm2) (Memop Word256 (%% (rsi,160))) (Imm8 (word 78)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xbe; 0xc0; 0x00; 0x00; 0x00; 0x4e;
                           (* VPERMQ (%_% ymm7) (Memop Word256 (%% (rsi,192))) (Imm8 (word 78)) *)
  0xc4; 0x41; 0x65; 0xf9; 0xe1;
                           (* VPSUBW (%_% ymm12) (%_% ymm3) (%_% ymm9) *)
  0xc5; 0x35; 0xfd; 0xcb;  (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc4; 0x41; 0x55; 0xf9; 0xea;
                           (* VPSUBW (%_% ymm13) (%_% ymm5) (%_% ymm10) *)
  0xc5; 0x9d; 0xd5; 0xda;  (* VPMULLW (%_% ymm3) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x2d; 0xfd; 0xd5;  (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm5) *)
  0xc5; 0x3d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x95; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf0;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm8) *)
  0xc5; 0x25; 0xf9; 0xfc;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm4) *)
  0xc5; 0x0d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe3;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe7;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm7) *)
  0xc5; 0x15; 0xe5; 0xef;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm7) *)
  0xc5; 0x0d; 0xe5; 0xf7;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm7) *)
  0xc5; 0x05; 0xe5; 0xff;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm7) *)
  0xc5; 0xe5; 0xe5; 0xd8;  (* VPMULHW (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0x9d; 0xf9; 0xdb;  (* VPSUBW (%_% ymm3) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x95; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm13) (%_% ymm5) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm14) (%_% ymm8) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc3; 0x35; 0x46; 0xfa; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm9) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x35; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm9) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0x63; 0x4d; 0x46; 0xcc; 0x20;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm6) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x4d; 0x46; 0xe4; 0x31;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x65; 0x46; 0xf5; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm3) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x46; 0xed; 0x31;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x3d; 0x46; 0xdb; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm8) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x3d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm8) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x56; 0x60;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0x2d; 0xf9; 0xe7;  (* VPSUBW (%_% ymm12) (%_% ymm10) (%_% ymm7) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfa;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm10) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xe9;
                           (* VPSUBW (%_% ymm13) (%_% ymm4) (%_% ymm9) *)
  0xc5; 0x1d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x35; 0xfd; 0xcc;  (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm4) *)
  0xc5; 0x55; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0x95; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm13) (%_% ymm2) *)
  0xc5; 0xcd; 0xfd; 0xf5;  (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0x25; 0xf9; 0xfb;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm3) *)
  0xc5; 0x8d; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xdb;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x41; 0x1d; 0xe5; 0xe0;
                           (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x15; 0xe5; 0xe8;
                           (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm8) *)
  0xc4; 0x41; 0x0d; 0xe5; 0xf0;
                           (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm8) *)
  0xc4; 0x41; 0x05; 0xe5; 0xf8;
                           (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm8) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0xdd; 0xe5; 0xe0;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm12) (%_% ymm10) *)
  0xc5; 0x95; 0xf9; 0xe4;  (* VPSUBW (%_% ymm4) (%_% ymm13) (%_% ymm4) *)
  0xc5; 0x8d; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm14) (%_% ymm5) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0xc1; 0x1d; 0x71; 0xe4; 0x0a;
                           (* VPSRAW (%_% ymm12) (%_% ymm12) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xd5; 0xe0;  (* VPMULLW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfc;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm9) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm5) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,288))) *)
  0xc4; 0xe2; 0x7d; 0x59; 0x56; 0x40;
                           (* VPBROADCASTQ (%_% ymm2) (Memop Quadword (%% (rsi,64))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,352))) *)
  0xc4; 0xe2; 0x7d; 0x59; 0x5e; 0x48;
                           (* VPBROADCASTQ (%_% ymm3) (Memop Quadword (%% (rsi,72))) *)
  0xc5; 0x3d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe0;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc5; 0x35; 0xf9; 0xed;  (* VPSUBW (%_% ymm13) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x1d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xe9;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc5; 0x2d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm10) (%_% ymm6) *)
  0xc5; 0x15; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf2;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc5; 0x25; 0xf9; 0xff;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm7) *)
  0xc5; 0x0d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfb;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe3;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x15; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm3) *)
  0xc5; 0x0d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm3) *)
  0xc5; 0x05; 0xe5; 0xfb;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm3) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm13) (%_% ymm9) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0xfd; 0x7f; 0x27;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,416))) *)
  0xc4; 0xe2; 0x7d; 0x59; 0x56; 0x40;
                           (* VPBROADCASTQ (%_% ymm2) (Memop Quadword (%% (rsi,64))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,480))) *)
  0xc4; 0xe2; 0x7d; 0x59; 0x5e; 0x48;
                           (* VPBROADCASTQ (%_% ymm3) (Memop Quadword (%% (rsi,72))) *)
  0xc5; 0x3d; 0xf9; 0xe4;  (* VPSUBW (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe0;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc5; 0x35; 0xf9; 0xed;  (* VPSUBW (%_% ymm13) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x1d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xe9;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc5; 0x2d; 0xf9; 0xf6;  (* VPSUBW (%_% ymm14) (%_% ymm10) (%_% ymm6) *)
  0xc5; 0x15; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf2;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc5; 0x25; 0xf9; 0xff;  (* VPSUBW (%_% ymm15) (%_% ymm11) (%_% ymm7) *)
  0xc5; 0x0d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm14) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfb;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc5; 0x05; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm15) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe3;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0x15; 0xe5; 0xeb;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm3) *)
  0xc5; 0x0d; 0xe5; 0xf3;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm3) *)
  0xc5; 0x05; 0xe5; 0xfb;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm3) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xc8;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xd0;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x1d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x41; 0x15; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm13) (%_% ymm9) *)
  0xc4; 0x41; 0x0d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm14) (%_% ymm10) *)
  0xc4; 0x41; 0x05; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm11) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_intt_tmc = define_trimmed "mlkem_intt_tmc" mlkem_intt_mc;;
let MLKEM_INTT_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_intt_tmc;;

let LENGTH_MLKEM_INTT_TMC =
  REWRITE_CONV[mlkem_intt_tmc] `LENGTH mlkem_intt_tmc`
  |> CONV_RULE(RAND_CONV LENGTH_CONV);;

let LENGTH_QDATA_FULL =
  REWRITE_CONV[qdata_full] `LENGTH qdata_full`
  |> CONV_RULE(RAND_CONV LENGTH_CONV);;

let MLKEM_INTT_POSTAMBLE_LENGTH = new_definition
  `MLKEM_INTT_POSTAMBLE_LENGTH = 1`;;

let MLKEM_INTT_CORE_END = new_definition
  `MLKEM_INTT_CORE_END = LENGTH mlkem_intt_tmc - MLKEM_INTT_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_INTT_TMC;
              LENGTH_QDATA_FULL;
              MLKEM_INTT_CORE_END;
              MLKEM_INTT_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

let MLKEM_INTT_CORRECT = prove
  (`!a zetas (zetas_list:int16 list) x pc.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc, LENGTH mlkem_intt_tmc) (a, 512) /\
    nonoverlapping (word pc, LENGTH mlkem_intt_tmc) (zetas, LENGTH qdata_full * 2) /\
    nonoverlapping (a, 512) (zetas, LENGTH qdata_full * 2)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mlkem_intt_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
              (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = word(pc + MLKEM_INTT_CORE_END) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes16(word_add a (word(2 * i)))) s in
                      (ival zi == avx2_inverse_ntt (ival o x) i) (mod &3329) /\
                      abs(ival zi) <= &26631))
          (MAYCHANGE [events] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                      ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                      ZMM15] ,,
           MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
           MAYCHANGE [memory :> bytes(a, 512)])`,

  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN

  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  REWRITE_TAC [SOME_FLAGS; fst MLKEM_INTT_TMC_EXEC] THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `init_ymm2:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `init_ymm3:int256` `read YMM3` THEN

  ENSURES_INIT_TAC "s0" THEN

  MEMORY_256_FROM_16_TAC "a" 16 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN


  FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[qdata_full; MAP; CONS_11] THEN
  STRIP_TAC THEN

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add zetas (word n))) s0`))
            (0--38))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

  FIRST_ASSUM(MP_TAC o check
   (can (term_match [] `read (memory :> bytes256 (word_add zetas (word 64))) s0 = xxx`) o concl)) THEN
  CONV_TAC(LAND_CONV(READ_MEMORY_SPLIT_CONV 2)) THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_INTT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_ABBREV_TAC[ntt_montmul; barred_x86]
                              [ntt_montmul_add; ntt_montmul_sub])
        (1--663) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC
           DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[INT_ABS_BOUNDS; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN

  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s663" THEN

  W(fun (asl,w) ->
     let asms =
        map snd (filter (is_local_definition
          [ntt_montmul; barred_x86] o concl o snd) asl) in
     MP_TAC(end_itlist CONJ (rev asms)) THEN
     MAP_EVERY (fun t -> UNDISCH_THEN (concl t) (K ALL_TAC)) asms) THEN

  REWRITE_TAC[WORD_BLAST `word_subword (x:int32) (0, 32) = x`] THEN
  REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0, 64) = x`] THEN
  REWRITE_TAC[WORD_BLAST
   `word_subword (word_ushr (word_join (h:int16) (l:int16):int32) 16) (0, 16) = h`] THEN
  REWRITE_TAC[WORD_BLAST
   `word_subword (word_ushr (word_join (h:int32) (l:int32):int64) 32) (0, 32) = h`] THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_ushr (word_join (h:int32) (l:int32):int64) 32) (0, 16):int16 =
     word_subword h (0, 16)`] THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_ushr (word_join (h:int32) (l:int32):int64) 32) (16, 16):int16 =
     word_subword h (16, 16)`] THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_shl (word_subword (x:int32) (0, 32):int32) 16:int32) (16, 16):int16 =
     word_subword x (0, 16)`] THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_shl (word_subword (x:int32) (0, 32):int32) 16:int32) (16, 16):int16 =
     word_subword x (0, 16)`] THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_shl (x:int32) 16:int32) (16, 16):int16 =
     word_subword x (0, 16)`] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN

  STRIP_TAC THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN

  W(fun (asl,w) ->
    let lfn = undefined
    and asms =
      map snd (filter (is_local_definition [ntt_montmul; barred_x86] o concl o snd) asl) in
    let lfn' = LOCAL_CONGBOUND_RULE lfn (rev asms) in

    REPEAT(GEN_REWRITE_TAC I
     [TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN CONJ_TAC) THEN

    W(MP_TAC o ASM_CONGBOUND_RULE lfn' o rand o lhand o rator o lhand o snd) THEN
   (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 3329 65536`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
    CONV_TAC(ONCE_DEPTH_CONV AVX2_INVERSE_NTT_CONV) THEN
    REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    MATCH_MP_TAC(INT_ARITH
     `l':int <= l /\ u <= u'
      ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
    CONV_TAC INT_REDUCE_CONV]))
);;

let MLKEM_INTT_NOIBT_SUBROUTINE_CORRECT  = prove
  (`!a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc, LENGTH mlkem_intt_tmc) (a, 512) /\
    nonoverlapping (word pc, LENGTH mlkem_intt_tmc) (zetas, LENGTH qdata_full * 2) /\
    nonoverlapping (a, 512) (zetas, LENGTH qdata_full * 2) /\
    nonoverlapping (a, 512) (stackpointer, 8) /\
    nonoverlapping (zetas, LENGTH qdata_full * 2) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_intt_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
              (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes16(word_add a (word(2 * i)))) s in
                      (ival zi == avx2_inverse_ntt (ival o x) i) (mod &3329) /\
                      abs(ival zi) <= &26631))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a, 512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_intt_tmc
    (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_INTT_CORRECT)));;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/x86_64/src/arith_native_x86_64.h *)

let MLKEM_INTT_SUBROUTINE_CORRECT  = prove
  (`!a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc, LENGTH mlkem_intt_mc) (a, 512) /\
    nonoverlapping (word pc, LENGTH mlkem_intt_mc) (zetas, LENGTH qdata_full * 2) /\
    nonoverlapping (a, 512) (zetas, LENGTH qdata_full * 2) /\
    nonoverlapping (a, 512) (stackpointer, 8) /\
    nonoverlapping (zetas, LENGTH qdata_full * 2) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_intt_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
              (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes16(word_add a (word(2 * i)))) s in
                      (ival zi == avx2_inverse_ntt (ival o x) i) (mod &3329) /\
                      abs(ival zi) <= &26631))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a, 512)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
  (CONV_RULE TWEAK_CONV MLKEM_INTT_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;
needs "common/consttime_utils.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_intt" subroutine_signatures)
    MLKEM_INTT_CORRECT
    MLKEM_INTT_TMC_EXEC;;
(* Remove duplicates from memaccess_inbounds lists (s2n-bignum#350).
   full_spec mixes numeric and symbolic buffer sizes: mk_safety_spec computes
   624*2=1248 from the subroutine signature for memaccess_inbounds, but copies
   `LENGTH qdata_full * 2` verbatim from the correctness theorem's nonoverlapping
   preconditions. Normalize to numeric form so ASSERT_CONCL_TAC matches the
   hand-written goal after LENGTH_SIMPLIFY_CONV. *)
let full_spec = ONCE_DEPTH_CONV MEMACCESS_INBOUNDS_DEDUP_CONV full_spec |> concl |> rhs;;
let full_spec = LENGTH_SIMPLIFY_CONV full_spec |> concl |> rhs;;

let MLKEM_INTT_SAFE = time prove
 (`exists f_events.
       forall e a zetas pc.
           aligned 32 a /\
           aligned 32 zetas /\
           nonoverlapping (word pc,LENGTH mlkem_intt_tmc) (a,512) /\
           nonoverlapping (word pc,LENGTH mlkem_intt_tmc)
                          (zetas,LENGTH qdata_full * 2) /\
           nonoverlapping (a,512) (zetas,LENGTH qdata_full * 2)
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST mlkem_intt_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [a; zetas] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + MLKEM_INTT_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events zetas a pc /\
                         memaccess_inbounds e2
                           [a,512; zetas,LENGTH qdata_full * 2]
                           [a,512]))
               (MAYCHANGE [events] ,,
                MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                           ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                           ZMM15] ,,
                MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_INTT_TMC_EXEC);;

let MLKEM_INTT_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a zetas pc stackpointer returnaddress.
          aligned 32 a /\
          aligned 32 zetas /\
          nonoverlapping (word pc,LENGTH mlkem_intt_tmc) (a,512) /\
          nonoverlapping (word pc,LENGTH mlkem_intt_tmc)
                         (zetas,LENGTH qdata_full * 2) /\
          nonoverlapping (a,512) (zetas,LENGTH qdata_full * 2) /\
          nonoverlapping (stackpointer, 8) (a, 512)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_intt_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; zetas] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events zetas a pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [a,512; zetas,LENGTH qdata_full * 2;
                            stackpointer,8]
                           [a,512; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_intt_tmc
    (CONV_RULE
      (REWRITE_CONV[LENGTH_MLKEM_INTT_TMC;
                    MLKEM_INTT_CORE_END;
                    MLKEM_INTT_POSTAMBLE_LENGTH] THENC
       NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0])
      MLKEM_INTT_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_INTT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a zetas pc stackpointer returnaddress.
          aligned 32 a /\
          aligned 32 zetas /\
          nonoverlapping (word pc,LENGTH mlkem_intt_mc) (a,512) /\
          nonoverlapping (word pc,LENGTH mlkem_intt_mc)
                         (zetas,LENGTH qdata_full * 2) /\
          nonoverlapping (a,512) (zetas,LENGTH qdata_full * 2) /\
          nonoverlapping (stackpointer, 8) (a, 512)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_intt_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; zetas] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events zetas a pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [a,512; zetas,LENGTH qdata_full * 2;
                            stackpointer,8]
                           [a,512; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_INTT_NOIBT_SUBROUTINE_SAFE));;
