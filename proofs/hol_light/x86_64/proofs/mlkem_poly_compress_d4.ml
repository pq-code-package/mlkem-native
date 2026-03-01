(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 4 bits.                         *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "x86_64/proofs/mlkem_compress_common.ml";;
needs "x86_64/proofs/mlkem_compress_consts.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d4.o";; *)

let mlkem_poly_compress_d4_mc =
  define_assert_from_elf "mlkem_poly_compress_d4_mc" "x86_64/mlkem/mlkem_poly_compress_d4.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0xbf; 0x4e; 0xbf; 0x4e;
                           (* MOV (% eax) (Imm32 (word 1321160383)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x00; 0x02; 0x00; 0x02;
                           (* MOV (% eax) (Imm32 (word 33554944)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xb8; 0x0f; 0x00; 0x0f; 0x00;
                           (* MOV (% eax) (Imm32 (word 983055)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xb8; 0x01; 0x10; 0x01; 0x10;
                           (* MOV (% eax) (Imm32 (word 268505089)) *)
  0xc5; 0xf9; 0x6e; 0xd8;  (* VMOVD (%_% xmm3) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc5; 0xfd; 0x6f; 0x22;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xfd; 0x6f; 0x2e;  (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x76; 0x20;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x7e; 0x40;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x60;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x2f;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xae; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,128))) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xae; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xae; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0xbe; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xd5; 0xe5; 0xe8;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xcd; 0xe5; 0xf0;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xc5; 0xe5; 0xf8;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x3d; 0xe5; 0xc0;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc4; 0xe2; 0x55; 0x0b; 0xe9;
                           (* VPMULHRSW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x0b; 0xf1;
                           (* VPMULHRSW (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x0b; 0xf9;
                           (* VPMULHRSW (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x0b; 0xc1;
                           (* VPMULHRSW (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xd5; 0xdb; 0xea;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xcd; 0xdb; 0xf2;  (* VPAND (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xdb; 0xfa;  (* VPAND (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x3d; 0xdb; 0xc2;  (* VPAND (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xd5; 0x67; 0xee;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0x67; 0xf8;
                           (* VPACKUSWB (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xe2; 0x55; 0x04; 0xeb;
                           (* VPMADDUBSW (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0xe2; 0x45; 0x04; 0xfb;
                           (* VPMADDUBSW (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xd5; 0x67; 0xef;  (* VPACKUSWB (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xed;
                           (* VPERMD (%_% ymm5) (%_% ymm4) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_poly_compress_d4_tmc =
  define_trimmed "mlkem_poly_compress_d4_tmc" mlkem_poly_compress_d4_mc;;
let MLKEM_POLY_COMPRESS_D4_TMC_EXEC =
  X86_MK_CORE_EXEC_RULE mlkem_poly_compress_d4_tmc;;

let LENGTH_MLKEM_POLY_COMPRESS_D4_MC =
  REWRITE_CONV[mlkem_poly_compress_d4_mc] `LENGTH mlkem_poly_compress_d4_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_MLKEM_POLY_COMPRESS_D4_TMC =
  REWRITE_CONV[mlkem_poly_compress_d4_tmc] `LENGTH mlkem_poly_compress_d4_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH = new_definition
  `MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH = 1`;;

let MLKEM_POLY_COMPRESS_D4_CORE_END = new_definition
  `MLKEM_POLY_COMPRESS_D4_CORE_END =
   LENGTH mlkem_poly_compress_d4_tmc - MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLKEM_POLY_COMPRESS_D4_MC;
               LENGTH_MLKEM_POLY_COMPRESS_D4_TMC;
               MLKEM_POLY_COMPRESS_D4_CORE_END;
               MLKEM_POLY_COMPRESS_D4_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_0];;

(* ------------------------------------------------------------------------- *)
(* AVX2 implementation of compress_d4 as a word expression.                  *)
(* Like d5, d4 uses VPMULHW with constant 0x4EBF, then VPMULHRSW.           *)
(* The result is a 4-bit value in the low bits of a 16-bit word.             *)
(* ------------------------------------------------------------------------- *)

let compress_d4_avx2 = new_definition
  `compress_d4_avx2 (a:16 word) : 4 word =
   word_subword (word_and
    (word_subword
      (word_add
        (word_ushr
          (word_mul
            (word_sx
              (word_subword (word_mul (word_sx a) (word 20159) : 32 word) (16,16) : 16 word))
            (word 512) : 32 word)
          14)
        (word 1) : 32 word)
      (1,16) : 16 word)
    (word 15)) (0,4) : 4 word`;;

let compress_d4_avx2_alt = prove(
  `word_zx (compress_d4_avx2 x) : 16 word =
       (word_and
          (word_subword
             (word_add
                (word_ushr
                   (word_mul
                      (word_sx
                        (word_subword (word_mul (word_sx x) (word 20159) : 32 word) (16,16) : 16 word))
                      (word 512) : 32 word)
                   14)
                (word 1) : 32 word)
             (1,16) : 16 word)
          (word 15))`,
    REWRITE_TAC [compress_d4_avx2] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for 4-bit compression                                       *)
(* ------------------------------------------------------------------------- *)

let MULADD_16_1_JOIN = prove(
  `word_add (word_mul (word_zx (x : 4 word)) (word 1) : 32 word)
            (word_mul (word_zx (y : 4 word)) (word 16)) =
   word_zx (word_join y x : 8 word) : 32 word`,
  BITBLAST_TAC);;

let BIT_15_ZX_4_16 = WORD_BLAST `!a:4 word. bit 15 (word_zx a: 16 word) = false`;;
let BIT_15_ZX_8_32 = WORD_BLAST `!a:8 word. bit 15 (word_zx a: 32 word) = false`;;
let BIT_31_ZX_8_32 = WORD_BLAST `!a:8 word. bit 31 (word_zx a: 32 word) = false`;;
let BIT_15_ZX_8_16 = WORD_BLAST `!a:8 word. bit 15 (word_zx a: 16 word) = false`;;

let WORD_VAL_4_8 = prove(`!(x : 4 word). word (val x) : 8 word = word_zx x`, BITBLAST_TAC);;
let WORD_ZX_ZX_4_8_32 = WORD_BLAST `!(x : 4 word). word_zx (word_zx x : 8 word) : 32 word = word_zx x`;;

let MIN_ZX_4_16 = prove(
  `!a:4 word. MIN (val (word_zx a : 16 word)) 255 = val a`,
  GEN_TAC THEN
  SIMP_TAC[word_zx; VAL_WORD; DIMINDEX_16; DIMINDEX_CONV `dimindex(:4)`] THEN
  SUBGOAL_THEN `val (a:4 word) MOD 2 EXP 16 = val a` SUBST1_TAC THENL
  [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
   MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `2 EXP 4` THEN
   REWRITE_TAC[VAL_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
   MP_TAC(ISPEC `a:4 word` VAL_BOUND) THEN
   REWRITE_TAC[DIMINDEX_CONV `dimindex(:4)`] THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN ARITH_TAC] THEN
  MP_TAC(ISPEC `a:4 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:4)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN ARITH_TAC);;

let MIN_ZX_8_16 = prove(
  `!a:8 word. MIN (val (word_zx a : 16 word)) 255 = val a`,
  GEN_TAC THEN
  SIMP_TAC[word_zx; VAL_WORD; DIMINDEX_16; DIMINDEX_CONV `dimindex(:8)`] THEN
  SUBGOAL_THEN `val (a:8 word) MOD 2 EXP 16 = val a` SUBST1_TAC THENL
  [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
   MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
   REWRITE_TAC[VAL_BOUND] THEN CONV_TAC NUM_REDUCE_CONV;
   MP_TAC(ISPEC `a:8 word` VAL_BOUND) THEN
   REWRITE_TAC[DIMINDEX_CONV `dimindex(:8)`] THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN ARITH_TAC] THEN
  MP_TAC(ISPEC `a:8 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:8)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MIN] THEN ARITH_TAC);;

let WORD_SUBWORD_8_0_16 = WORD_BLAST `!(x : 8 word). word_subword x (0,16) : 16 word = word_zx x`;;

(* ------------------------------------------------------------------------- *)
(* Correctness of the per-element compression formula                        *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_CORRECT = prove(
  `!(x : 16 word). val x < 3329 ==>
   compress_d4 x = compress_d4_avx2 x`,
  let CORE = prove(
    `!(x : num). x < 3329 ==>
     compress_d4 (word x) = compress_d4_avx2 (word x)`,
    REWRITE_TAC[compress_d4; compress_d4_avx2] THEN
    BRUTE_FORCE_WITH (CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN CONV_TAC WORD_BLAST)) in
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `val(x:16 word)` CORE) THEN
  ASM_REWRITE_TAC[WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* Rewrite compress_d4_avx2 back to compress_d4                              *)
(* ------------------------------------------------------------------------- *)

let REWRITE_COMPRESS =
  let derive_instance thm tm =
    let thm' = PART_MATCH rand thm tm in
    MP thm' (EQT_ELIM(NUM_REDUCE_CONV (fst(dest_imp(concl thm')))))
  in
  (UNDISCH_THEN (`forall i. i < 256 ==> val (EL i (inlist : (16 word) list)) < 3329`) (fun thm ->
   RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (COND_REWRITE_CONV (derive_instance thm) (GSYM COMPRESS_D4_CORRECT))))
   THEN ASSUME_TAC thm
  ));;

(* ------------------------------------------------------------------------- *)
(* Main correctness theorem                                                  *)
(* d4 processes 64 coefficients per iteration (4 VMOVDQA loads),             *)
(* outputting 256 bits = 32 bytes (single VMOVDQU) per iteration.            *)
(* 4 iterations × 64 coefficients = 256 total.                              *)
(* 4 iterations × 32 bytes = 128 bytes total output.                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D4_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 128))
          [(word pc, LENGTH mlkem_poly_compress_d4_tmc); (a, 512); (data, 32)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_poly_compress_d4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d4_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = word (pc + MLKEM_POLY_COMPRESS_D4_CORE_END) /\
                read (memory :> bytes(r, 128)) s = num_of_wordlist (MAP compress_d4 inlist))
           (MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(r, 128)] ,,
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
   `read(memory :> bytes(data,32)) s0 = num_of_wordlist ((MAP iword compress_d4_data) : (8 word) list)` THEN
  REWRITE_TAC [compress_d4_data; MAP] THEN
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
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_POLY_COMPRESS_D4_TMC_EXEC [n] THEN SIMD_SIMPLIFY_TAC
    ([compress_d4_avx2_alt]
     @ map GSYM [BIT_15_ZX_4_16; MIN_ZX_4_16; GSYM ADD_ASSOC; (CONV_RULE NUM_REDUCE_CONV BYTES256_JOIN);
     WORD_VAL_4_8; WORD_ZX_ZX_4_8_32; MULADD_16_1_JOIN; BIT_31_ZX_8_32; BIT_15_ZX_8_32;
     WORD_SUBWORD_8_0_16; BIT_15_ZX_8_16; MIN_ZX_8_16; WORD_VAL])) (1 -- 105) THEN

  REWRITE_COMPRESS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  ASM_SIMP_TAC [EL_MAP; ARITH] THEN
  REPLICATE_TAC 6
   (GEN_REWRITE_TAC (ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC(ONCE_DEPTH_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES256_WBYTES] THEN
  ASM_REWRITE_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrappers                                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_COMPRESS_D4_NOIBT_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 128))
          [(word pc, LENGTH mlkem_poly_compress_d4_tmc); (a, 512); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d4_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 128)) s = num_of_wordlist (MAP compress_d4 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 128)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_compress_d4_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D4_CORRECT));;

(* NOTE: This must be kept in sync with the CBMC specification
 * in mlkem/src/native/x86_64/src/arith_native_x86_64.h *)

let MLKEM_POLY_COMPRESS_D4_SUBROUTINE_CORRECT = prove(
  `!r a data (inlist:(16 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 256 /\
      aligned 32 a /\
      aligned 32 data /\
      ALL (nonoverlapping (r, 128))
          [(word pc, LENGTH mlkem_poly_compress_d4_mc); (a, 512); (data, 32); (stackpointer, 8)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_poly_compress_d4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [r; a; data] s /\
                read (memory :> bytes(data, 32)) s =
                  num_of_wordlist ((MAP iword compress_d4_data): (8 word) list) /\
                read (memory :> bytes(a, 512)) s = num_of_wordlist inlist /\
                (!i. i < 256 ==> &0 <= ival (EL i inlist) /\ ival (EL i inlist) <= &3328))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytes(r, 128)) s = num_of_wordlist (MAP compress_d4 inlist))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 128)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_COMPRESS_D4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_poly_compress_d4" subroutine_signatures)
    MLKEM_POLY_COMPRESS_D4_CORRECT
    MLKEM_POLY_COMPRESS_D4_TMC_EXEC;;

let MLKEM_POLY_COMPRESS_D4_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,128))
           [word pc,LENGTH mlkem_poly_compress_d4_tmc; a,512; data,32]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc)
                      (BUTLAST mlkem_poly_compress_d4_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a; data] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + MLKEM_POLY_COMPRESS_D4_CORE_END) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a data r pc /\
                         memaccess_inbounds e2
                           [a,512; data,32; r,128] [r,128]))
               (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes (r,128)] ,,
              MAYCHANGE [RIP] ,,
              MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
    MLKEM_POLY_COMPRESS_D4_TMC_EXEC);;

let MLKEM_POLY_COMPRESS_D4_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,128))
           [word pc,LENGTH mlkem_poly_compress_d4_tmc; a,512; data,32;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_compress_d4_tmc /\
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
                           [a,512; data,32; r,128; stackpointer,8]
                           [r,128; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_poly_compress_d4_tmc
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLKEM_POLY_COMPRESS_D4_SAFE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_POLY_COMPRESS_D4_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a data (inlist:(16 word) list) pc stackpointer returnaddress.
           LENGTH inlist = 256 /\
           aligned 32 a /\
           aligned 32 data /\
           ALL (nonoverlapping (r,128))
           [word pc,LENGTH mlkem_poly_compress_d4_mc; a,512; data,32;
            stackpointer,8]
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mlkem_poly_compress_d4_mc /\
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
                           [a,512; data,32; r,128; stackpointer,8]
                           [r,128; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_POLY_COMPRESS_D4_NOIBT_SUBROUTINE_SAFE));;
