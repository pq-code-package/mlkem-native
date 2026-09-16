(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "s2n_bignum/x86/proofs/base.ml";;

needs "mlkem_native/common/mlkem_specs.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_reduce_avx2_asm.o";; *)

let mlkem_reduce_mc =
  define_assert_from_elf "mlkem_reduce_mc" "x86_64/mlkem/mlkem_reduce_avx2_asm.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0xb8; 0xaf; 0xb8; 0xaf;
                           (* MOV (% eax) (Imm32 (word 2948116408)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xb8; 0x14; 0x00; 0x14; 0x00;
                           (* MOV (% eax) (Imm32 (word 1310740)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0x02; 0x00; 0x02; 0x00;
                           (* MOV (% eax) (Imm32 (word 131074)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe4;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfd; 0xe3;  (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xe4; 0xe0;  (* VPMULHUW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xec;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfd; 0xeb;  (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xe4; 0xe8;  (* VPMULHUW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xcd; 0xd5; 0xf2;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf4;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0xcd; 0xfd; 0xf3;  (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xcd; 0xe4; 0xf0;  (* VPMULHUW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0xc5; 0xd5; 0xfa;  (* VPMULLW (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfc;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfd; 0xfb;  (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xe4; 0xf8;  (* VPMULHUW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x3d; 0xfd; 0xc3;  (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xe4; 0xc0;  (* VPMULHUW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0x35; 0xfd; 0xcb;  (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xe4; 0xc8;  (* VPMULHUW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x2d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc5; 0x2d; 0xfd; 0xd3;  (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0x2d; 0xe4; 0xd0;  (* VPMULHUW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm11) (%_% ymm1) *)
  0xc5; 0x25; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdc;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm12) *)
  0xc5; 0x25; 0xfd; 0xdb;  (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm3) *)
  0xc5; 0x25; 0xe4; 0xd8;  (* VPMULHUW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x27;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x5d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xd5; 0xe2;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xe4;
                           (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0xdd; 0xfd; 0xe3;  (* VPADDW (%_% ymm4) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xdd; 0xe4; 0xe0;  (* VPMULHUW (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x55; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xec;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0xd5; 0xfd; 0xeb;  (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xe4; 0xe8;  (* VPMULHUW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0x4d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xcd; 0xd5; 0xf2;  (* VPMULLW (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xf4;
                           (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0xcd; 0xfd; 0xf3;  (* VPADDW (%_% ymm6) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xcd; 0xe4; 0xf0;  (* VPMULHUW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0x45; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0xc5; 0xd5; 0xfa;  (* VPMULLW (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfc;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xc5; 0xfd; 0xfb;  (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xe4; 0xf8;  (* VPMULHUW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xd5; 0xc2;  (* VPMULLW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc5; 0x3d; 0xfd; 0xc3;  (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm3) *)
  0xc5; 0x3d; 0xe4; 0xc0;  (* VPMULHUW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x35; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xd5; 0xca;  (* VPMULLW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0x35; 0xfd; 0xcb;  (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm3) *)
  0xc5; 0x35; 0xe4; 0xc8;  (* VPMULHUW (%_% ymm9) (%_% ymm9) (%_% ymm0) *)
  0xc5; 0x2d; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x2d; 0xd5; 0xd2;  (* VPMULLW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc5; 0x2d; 0xfd; 0xd3;  (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm3) *)
  0xc5; 0x2d; 0xe4; 0xd0;  (* VPMULHUW (%_% ymm10) (%_% ymm10) (%_% ymm0) *)
  0xc5; 0x25; 0xe5; 0xe1;  (* VPMULHW (%_% ymm12) (%_% ymm11) (%_% ymm1) *)
  0xc5; 0x25; 0xd5; 0xda;  (* VPMULLW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdc;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm12) *)
  0xc5; 0x25; 0xfd; 0xdb;  (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm3) *)
  0xc5; 0x25; 0xe4; 0xd8;  (* VPMULHUW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm7) *)
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

let mlkem_reduce_tmc = define_trimmed "mlkem_reduce_tmc" mlkem_reduce_mc;;
let mlkem_reduce_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_reduce_tmc;;

let LENGTH_MLKEM_REDUCE_TMC =
  REWRITE_CONV[mlkem_reduce_tmc] `LENGTH mlkem_reduce_tmc`
  |> CONV_RULE(RAND_CONV LENGTH_CONV);;

let MLKEM_REDUCE_POSTAMBLE_LENGTH = new_definition
  `MLKEM_REDUCE_POSTAMBLE_LENGTH = 1`;;

let MLKEM_REDUCE_CORE_END = new_definition
  `MLKEM_REDUCE_CORE_END = LENGTH mlkem_reduce_tmc - MLKEM_REDUCE_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_REDUCE_TMC;
              MLKEM_REDUCE_CORE_END;
              MLKEM_REDUCE_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ========================================================================= *)
(* Plantard-style modular multiplication by a constant, in the AVX2          *)
(* instruction sequence suggested by Bo-Yin Yang.                            *)
(*                                                                           *)
(*   t = hi16(a*l)  u = lo16(a*h)  m = t+u  n = m+s  z = hi16u(n*q)          *)
(*                                                                           *)
(* where h*2^16 + l = W and q*W = b + 2^32*mu. The result is the canonical   *)
(* representative of a*mu modulo q, provided a*b lies in the window          *)
(*                                                                           *)
(*   q * (2^16 * (1-s) - 1)  <=  a*b  <  2^32 - s*q*2^16.                    *)
(* ========================================================================= *)

let PLANTARD_DIV_UNIQ = prove
 (`!u v:int. &65536 * v <= u /\ u < &65536 * v + &65536
             ==> u div &65536 = v`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`u:int`; `&65536:int`] INT_DIVISION) THEN
  ANTS_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  INT_ARITH_TAC);;

let PLANTARD_IVAL_SUBWORD_HI = prove
 (`!x:int32. ival(word_subword x (16,16):int16) = ival x div &2 pow 16`,
  REWRITE_TAC[GSYM DIMINDEX_16; GSYM IVAL_WORD_ISHR] THEN
  GEN_TAC THEN REWRITE_TAC[DIMINDEX_16] THEN BITBLAST_TAC);;

(* The arithmetic core: 2^16*(n*q) = 2^32*(a*mu - q*k) + (a*b - q*r +
 * 2^16*s*q), where the window puts the second summand in [0, 2^32) and so
 * makes the quotient exactly a*mu - q*k. *)

let PLANTARD_KEY = prove
 (`!q W s b mu a M r k n.
      &0 < (q:int) /\ &0 <= s /\
      q * W = b + &4294967296 * mu /\
      a * W = M * &65536 + r /\ &0 <= r /\ r < &65536 /\
      M + s = k * &65536 + n /\ &0 <= n /\ n < &65536 /\
      q * (&65536 * (&1 - s) - &1) <= a * b /\
      a * b < &4294967296 - s * q * &65536
      ==> &0 <= (n * q) div &65536 /\
          (n * q) div &65536 < q /\
          (n * q) div &65536 = a * mu - q * k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN

  (* Bounds on the two products that occur below. *)
  SUBGOAL_THEN `&0 <= (q:int) * r` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q:int) * r <= q * (&65536 - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (n:int) * q` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(n:int) * q <= (&65536 - &1) * q` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_RMUL THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN
   `&65536 * ((n:int) * q) =
    &4294967296 * (a * mu - q * k) + (a * b - q * r + &65536 * (s * q))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(q:int) * W = b + &4294967296 * mu` THEN
    UNDISCH_TAC `(a:int) * W = M * &65536 + r` THEN
    UNDISCH_TAC `(M:int) + s = k * &65536 + n` THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&0 <= (a:int) * b - q * r + &65536 * (s * q) /\
    a * b - q * r + &65536 * (s * q) < &4294967296`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `((n:int) * q) div &65536 = a * mu - q * k` ASSUME_TAC THENL
   [MATCH_MP_TAC PLANTARD_DIV_UNIQ THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN

  MP_TAC(SPECL [`(n:int) * q`; `&65536:int`] INT_DIVISION) THEN
  ANTS_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_INT_ARITH_TAC);;

(* The same with the link to n as a congruence modulo 2^16, which is all the
 * instruction sequence provides, since every intermediate step wraps. *)

let PLANTARD_MULMOD = prove
 (`!q W s b mu a n.
      &0 < (q:int) /\ &0 <= s /\ &0 <= n /\ n < &65536 /\
      q * W = b + &4294967296 * mu /\
      (n == (a * W) div &65536 + s) (mod &65536) /\
      q * (&65536 * (&1 - s) - &1) <= a * b /\
      a * b < &4294967296 - s * q * &65536
      ==> &0 <= (n * q) div &65536 /\
          (n * q) div &65536 < q /\
          ((n * q) div &65536 == a * mu) (mod q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(a:int) * W`; `&65536:int`] INT_DIVISION) THEN
  ANTS_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `d:int` o REWRITE_RULE[int_congruent] o
                check (can (term_match []
                             `((u:int) == v) (mod &65536)`) o concl)) THEN
  MP_TAC(SPECL [`q:int`; `W:int`; `s:int`; `b:int`; `mu:int`; `a:int`;
                `((a:int) * W) div &65536`; `((a:int) * W) rem &65536`;
                `--d:int`; `n:int`] PLANTARD_KEY) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INTEGER_TAC);;

(* The instruction sequence on a single 16-bit lane. *)

let plantard_seq = new_definition
 `plantard_seq (h:int16,l:int16,bias:int16,qw:int16) (x:int16) : int16 =
    word_subword
     (word_mul
       (word_zx
         (word_add
           (word_add (word_mul x h)
                     (word_subword (word_mul (word_sx x:int32) (word_sx l))
                                   (16,16)))
           bias) : int32)
       (word_zx qw))
     (16,16)`;;

(* The signed high multiplication of two 16-bit values never overflows, so
 * it is exactly the top half of the product. *)
let PLANTARD_IVAL_MULHI = prove
 (`!(x:int16) (l:int16).
     ival(word_subword (word_mul (word_sx x:int32) (word_sx l))
                       (16,16):int16) =
     (ival x * ival l) div &65536`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_mul (word_sx (x:int16):int32) (word_sx (l:int16)) =
                iword(ival x * ival l)`
  SUBST1_TAC THENL [REWRITE_TAC[word_sx; IWORD_INT_MUL]; ALL_TAC] THEN
  REWRITE_TAC[PLANTARD_IVAL_SUBWORD_HI] THEN CONV_TAC INT_REDUCE_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]);;

(* The bit pattern feeding the final multiplication. *)
let PLANTARD_VAL_MID = prove
 (`!(h:int16) (l:int16) (bias:int16) (x:int16).
     &(val(word_add (word_add (word_mul x h)
                              (word_subword
                                 (word_mul (word_sx x:int32) (word_sx l))
                                 (16,16)))
                    bias)) =
     (ival x * ival h + (ival x * ival l) div &65536 + &(val bias))
     rem &65536`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add (word_mul (x:int16) (h:int16)) (t:int16))
             (bias:int16) =
    iword(ival x * ival h + ival t + ival bias)`] THEN
  REWRITE_TAC[PLANTARD_IVAL_MULHI] THEN
  SIMP_TAC[VAL_IVAL_REM; DIMINDEX_16; INT_REM_IVAL_IWORD; LE_REFL] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC);;

(* The final, unsigned, high multiplication. *)
let PLANTARD_VAL_HI = prove
 (`!(n:int16) (qw:int16).
     val(word_subword (word_mul (word_zx n:int32) (word_zx qw))
                      (16,16):int16) =
     (val n * val qw) DIV 65536`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD_ZX;
           DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `n:int16` VAL_BOUND) THEN
  MP_TAC(ISPEC `qw:int16` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(n:int16) * val(qw:int16) < 4294967296` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `65536 * 65536` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[];
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(val(n:int16) * val(qw:int16)) DIV 65536 < 65536`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* Splitting W into its two 16-bit halves is exact. *)
let PLANTARD_SPLIT = prove
 (`!a H L. ((a:int) * (H * &65536 + L)) div &65536 =
           a * H + (a * L) div &65536`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `((a:int) * L) rem &65536` THEN
  MP_TAC(SPECL [`(a:int) * L`; `&65536:int`] INT_DIVISION) THEN
  ANTS_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;


(* Correctness for an arbitrary multiplier, which is recovered from the
 * constants rather than supplied. *)

let PLANTARD_SEQ = prove
 (`!(h:int16) (l:int16) (bias:int16) (qw:int16) (x:int16) b mu.
      &0 < (&(val qw):int) /\
      &(val qw) * (ival h * &65536 + ival l) = b + &4294967296 * mu /\
      &(val qw) * (&65536 * (&1 - &(val bias)) - &1) <= ival x * b /\
      ival x * b < &4294967296 - &(val bias) * &(val qw) * &65536
      ==> val(plantard_seq (h,l,bias,qw) x) < val qw /\
          (&(val(plantard_seq (h,l,bias,qw) x)) == ival x * mu)
          (mod &(val qw))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[plantard_seq; PLANTARD_VAL_HI] THEN
  ABBREV_TAC
   `mid:int16 =
      word_add (word_add (word_mul (x:int16) (h:int16))
                         (word_subword
                            (word_mul (word_sx x:int32) (word_sx (l:int16)))
                            (16,16)))
               (bias:int16)` THEN
  SUBGOAL_THEN `(&(val(mid:int16)):int) < &65536` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT] THEN
    MP_TAC(ISPEC `mid:int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&(val(mid:int16)):int) ==
     (ival(x:int16) * (ival(h:int16) * &65536 + ival(l:int16))) div &65536 +
     &(val(bias:int16))) (mod &65536)`
  ASSUME_TAC THENL
   [EXPAND_TAC "mid" THEN
    REWRITE_TAC[PLANTARD_VAL_MID; PLANTARD_SPLIT; INT_CONG_LREM] THEN
    INTEGER_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&(val(qw:int16)):int`;
                `ival(h:int16) * &65536 + ival(l:int16)`;
                `&(val(bias:int16)):int`; `b:int`; `mu:int`; `ival(x:int16)`;
                `&(val(mid:int16)):int`] PLANTARD_MULMOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INT_POS]; ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_DIV;
                GSYM INT_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[]]);;

(* The form intended for use: bias 2 and a small b, so that the window
 * follows from q <= 26214, which is what it permits for arbitrary int16
 * inputs. A larger modulus needs restricted inputs and PLANTARD_SEQ. *)

let PLANTARD_MULCONST = prove
 (`!(h:int16) (l:int16) (qw:int16) (x:int16) b w.
      &0 < (&(val qw):int) /\ (&(val qw):int) <= &26214 /\
      abs b <= &(val qw) /\
      &(val qw) * (ival h * &65536 + ival l) = b + &4294967296 * w
      ==> ival(plantard_seq (h,l,word 2,qw) x) =
          (ival x * w) rem &(val qw)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(ival(x:int16) * b) <= &32768 * &(val(qw:int16))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_MUL2 THEN
    ASM_REWRITE_TAC[INT_ABS_POS] THEN
    MP_TAC(ISPEC `x:int16` IVAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:int16`; `l:int16`; `word 2:int16`; `qw:int16`; `x:int16`;
                `b:int`; `w:int`] PLANTARD_SEQ) THEN
  SUBGOAL_THEN `val(word 2:int16) = 2` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    CONJ_TAC THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `ival(plantard_seq (h,l,word 2,qw) (x:int16)) =
    &(val(plantard_seq (h,l,word 2,qw) x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_EQ_VAL THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPEC `qw:int16` VAL_BOUND) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(val(plantard_seq (h,l,word 2,qw) (x:int16))):int) < &(val qw)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[INT_OF_NUM_LT]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[INT_REM_UNIQUE; INT_ABS_NUM] THEN
  ASM_REWRITE_TAC[INT_POS] THEN
  MATCH_MP_TAC(INTEGER_RULE `(x:int == y) (mod n) ==> (y == x) (mod n)`) THEN
  ASM_REWRITE_TAC[]);;

(* The reduction of one coefficient, in the shape produced by symbolically
 * executing the five vector instructions on a 16-bit lane. *)

let plantard_reduce = new_definition
 `plantard_reduce (x:int16) : int16 =
    word_subword
     (word_mul
       (word_zx
         (word_add
           (word_add (word_mul x (word 20))
                     (word_subword
                        (word_mul (word_sx x:int32) (word 4294946744))
                        (16,16)))
           (word 2)) : int32)
       (word 3329))
     (16,16)`;;

let PLANTARD_REDUCE_SEQ = prove
 (`!x:int16. plantard_reduce x =
             plantard_seq (word 20, word 44984, word 2, word 3329) x`,
  GEN_TAC THEN REWRITE_TAC[plantard_reduce; plantard_seq] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let PLANTARD_REDUCE_SPEC = prove
 (`!x:int16. ival(plantard_reduce x) = ival x rem &3329`,
  GEN_TAC THEN REWRITE_TAC[PLANTARD_REDUCE_SEQ] THEN
  MP_TAC(SPECL [`word 20:int16`; `word 44984:int16`; `word 3329:int16`;
                `x:int16`; `&1976:int`; `&1:int`] PLANTARD_MULCONST) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ANTS_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[INT_MUL_RID]);;

let MLKEM_REDUCE_CORRECT = prove(
  `!a x pc.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_reduce_tmc) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_reduce_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = word (pc + MLKEM_REDUCE_CORE_END) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             // Registers (and memory locations) that may change after execution
             (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,512)] ,,
              MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6;
                         ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[fst mlkem_reduce_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS] THEN

  (* Split quantified assumptions into separate cases *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `init_ymm2:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `init_ymm3:int256` `read YMM3` THEN

  ENSURES_INIT_TAC "s0" THEN

  (* Rewrite memory-read assumptions from 16-bit granularity
   * to 256-bit granularity. *)
  MEMORY_256_FROM_16_TAC "a" 16 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN

  (* Symbolic execution *)
  MAP_EVERY (fun n -> X86_STEPS_TAC mlkem_reduce_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[plantard_reduce])
            (1--124) THEN

  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  (* Split quantified post-condition into separate cases *)
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN

  (* Forget all assumptions *)
  POP_ASSUM_LIST (K ALL_TAC) THEN

  (* Every coefficient is an instance of the arithmetic lemma. *)
  REWRITE_TAC[PLANTARD_REDUCE_SPEC]
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
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_reduce_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_REDUCE_CORRECT));;

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

needs "s2n_bignum/x86/proofs/consttime.ml";;
needs "mlkem_native/x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_REDUCE_CORRECT
    mlkem_reduce_TMC_EXEC;;

let MLKEM_REDUCE_SAFE = time prove
 (`exists f_events.
       forall e a pc.
           aligned 32 a /\ nonoverlapping (word pc,LENGTH mlkem_reduce_tmc) (a,512)
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST mlkem_reduce_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + MLKEM_REDUCE_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc /\
                         memaccess_inbounds e2 [a,512] [a,512]))
               (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes (a,512)] ,,
              MAYCHANGE [RIP] ,,
              MAYCHANGE [RAX] ,,
              MAYCHANGE
              [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6;
               ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars mlkem_reduce_TMC_EXEC);;

let MLKEM_REDUCE_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
          aligned 32 a /\
          nonoverlapping (word pc, LENGTH mlkem_reduce_tmc) (a, 512) /\
          nonoverlapping (stackpointer, 8) (a, 512)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_reduce_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_reduce_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_REDUCE_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_REDUCE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
          aligned 32 a /\
          nonoverlapping (word pc, LENGTH mlkem_reduce_mc) (a, 512) /\
          nonoverlapping (stackpointer, 8) (a, 512)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_reduce_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,512; stackpointer,8]
                                               [a,512; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_REDUCE_NOIBT_SUBROUTINE_SAFE));;
