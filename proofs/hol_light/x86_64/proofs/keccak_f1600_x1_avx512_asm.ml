(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation for SHA3, with AVX-512VL (four rounds per        *)
(* iteration, lane k of the state in the low quadword of xmmk).              *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/base.ml";;
needs "mlkem_native/x86_64/proofs/keccak_utils.ml";;
needs "mlkem_native/x86_64/proofs/keccak_avx512_utils.ml";;

(**** print_literal_from_elf
        "x86_64/mlkem/keccak_f1600_x1_avx512_asm.o";;
 ****)

let keccak_f1600_x1_avx512_mc = define_assert_from_elf
  "keccak_f1600_x1_avx512_mc"
  "x86_64/mlkem/keccak_f1600_x1_avx512_asm.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfa; 0x7e; 0x07;  (* VMOVQ (%_% xmm0) (Memop Quadword (%% (rdi,0))) *)
  0xc5; 0xfa; 0x7e; 0x4f; 0x08;
                           (* VMOVQ (%_% xmm1) (Memop Quadword (%% (rdi,8))) *)
  0xc5; 0xfa; 0x7e; 0x57; 0x10;
                           (* VMOVQ (%_% xmm2) (Memop Quadword (%% (rdi,16))) *)
  0xc5; 0xfa; 0x7e; 0x5f; 0x18;
                           (* VMOVQ (%_% xmm3) (Memop Quadword (%% (rdi,24))) *)
  0xc5; 0xfa; 0x7e; 0x67; 0x20;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%% (rdi,32))) *)
  0xc5; 0xfa; 0x7e; 0x6f; 0x28;
                           (* VMOVQ (%_% xmm5) (Memop Quadword (%% (rdi,40))) *)
  0xc5; 0xfa; 0x7e; 0x77; 0x30;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%% (rdi,48))) *)
  0xc5; 0xfa; 0x7e; 0x7f; 0x38;
                           (* VMOVQ (%_% xmm7) (Memop Quadword (%% (rdi,56))) *)
  0xc5; 0x7a; 0x7e; 0x47; 0x40;
                           (* VMOVQ (%_% xmm8) (Memop Quadword (%% (rdi,64))) *)
  0xc5; 0x7a; 0x7e; 0x4f; 0x48;
                           (* VMOVQ (%_% xmm9) (Memop Quadword (%% (rdi,72))) *)
  0xc5; 0x7a; 0x7e; 0x57; 0x50;
                           (* VMOVQ (%_% xmm10) (Memop Quadword (%% (rdi,80))) *)
  0xc5; 0x7a; 0x7e; 0x5f; 0x58;
                           (* VMOVQ (%_% xmm11) (Memop Quadword (%% (rdi,88))) *)
  0xc5; 0x7a; 0x7e; 0x67; 0x60;
                           (* VMOVQ (%_% xmm12) (Memop Quadword (%% (rdi,96))) *)
  0xc5; 0x7a; 0x7e; 0x6f; 0x68;
                           (* VMOVQ (%_% xmm13) (Memop Quadword (%% (rdi,104))) *)
  0xc5; 0x7a; 0x7e; 0x77; 0x70;
                           (* VMOVQ (%_% xmm14) (Memop Quadword (%% (rdi,112))) *)
  0xc5; 0x7a; 0x7e; 0x7f; 0x78;
                           (* VMOVQ (%_% xmm15) (Memop Quadword (%% (rdi,120))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x47; 0x10;
                           (* VMOVQ (%_% xmm16) (Memop Quadword (%% (rdi,128))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x4f; 0x11;
                           (* VMOVQ (%_% xmm17) (Memop Quadword (%% (rdi,136))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x57; 0x12;
                           (* VMOVQ (%_% xmm18) (Memop Quadword (%% (rdi,144))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x5f; 0x13;
                           (* VMOVQ (%_% xmm19) (Memop Quadword (%% (rdi,152))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x67; 0x14;
                           (* VMOVQ (%_% xmm20) (Memop Quadword (%% (rdi,160))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x6f; 0x15;
                           (* VMOVQ (%_% xmm21) (Memop Quadword (%% (rdi,168))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x77; 0x16;
                           (* VMOVQ (%_% xmm22) (Memop Quadword (%% (rdi,176))) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6e; 0x7f; 0x17;
                           (* VMOVQ (%_% xmm23) (Memop Quadword (%% (rdi,184))) *)
  0x62; 0x61; 0xfd; 0x08; 0x6e; 0x47; 0x18;
                           (* VMOVQ (%_% xmm24) (Memop Quadword (%% (rdi,192))) *)
  0x48; 0x8d; 0x86; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rax) (%% (rsi,192)) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% xmm25) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x08; 0x25; 0xca; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm5) (%_% xmm10) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x85; 0x08; 0x25; 0xcc; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm15) (%_% xmm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% xmm26) (%_% xmm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x08; 0x25; 0xd3; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm6) (%_% xmm11) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x00; 0x25; 0xd5; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm16) (%_% xmm21) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xda;
                           (* VMOVDQA64 (%_% xmm27) (%_% xmm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xc5; 0x08; 0x25; 0xdc; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm7) (%_% xmm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm17) (%_% xmm22) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% xmm28) (%_% xmm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x08; 0x25; 0xe5; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm8) (%_% xmm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xed; 0x00; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm18) (%_% xmm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xec;
                           (* VMOVDQA64 (%_% xmm29) (%_% xmm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x08; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm9) (%_% xmm14) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xe5; 0x00; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm19) (%_% xmm24) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x9d; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x08; 0x72; 0xcd; 0x24;
                           (* VPROLQ (%_% xmm5) (%_% xmm5) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x08; 0x72; 0xca; 0x03;
                           (* VPROLQ (%_% xmm10) (%_% xmm10) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x08; 0x72; 0xcf; 0x29;
                           (* VPROLQ (%_% xmm15) (%_% xmm15) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x00; 0x72; 0xcc; 0x12;
                           (* VPROLQ (%_% xmm20) (%_% xmm20) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x08; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% xmm1) (%_% xmm1) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x08; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% xmm6) (%_% xmm6) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x08; 0x72; 0xcb; 0x0a;
                           (* VPROLQ (%_% xmm11) (%_% xmm11) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x00; 0x72; 0xc8; 0x2d;
                           (* VPROLQ (%_% xmm16) (%_% xmm16) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x00; 0x72; 0xcd; 0x02;
                           (* VPROLQ (%_% xmm21) (%_% xmm21) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x08; 0x72; 0xca; 0x3e;
                           (* VPROLQ (%_% xmm2) (%_% xmm2) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x08; 0x72; 0xcf; 0x06;
                           (* VPROLQ (%_% xmm7) (%_% xmm7) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x08; 0x72; 0xcc; 0x2b;
                           (* VPROLQ (%_% xmm12) (%_% xmm12) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x00; 0x72; 0xc9; 0x0f;
                           (* VPROLQ (%_% xmm17) (%_% xmm17) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x00; 0x72; 0xce; 0x3d;
                           (* VPROLQ (%_% xmm22) (%_% xmm22) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x08; 0x72; 0xcb; 0x1c;
                           (* VPROLQ (%_% xmm3) (%_% xmm3) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x08; 0x72; 0xc8; 0x37;
                           (* VPROLQ (%_% xmm8) (%_% xmm8) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x08; 0x72; 0xcd; 0x19;
                           (* VPROLQ (%_% xmm13) (%_% xmm13) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x00; 0x72; 0xca; 0x15;
                           (* VPROLQ (%_% xmm18) (%_% xmm18) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x00; 0x72; 0xcf; 0x38;
                           (* VPROLQ (%_% xmm23) (%_% xmm23) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x08; 0x72; 0xcc; 0x1b;
                           (* VPROLQ (%_% xmm4) (%_% xmm4) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x08; 0x72; 0xc9; 0x14;
                           (* VPROLQ (%_% xmm9) (%_% xmm9) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x08; 0x72; 0xce; 0x27;
                           (* VPROLQ (%_% xmm14) (%_% xmm14) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x00; 0x72; 0xcb; 0x08;
                           (* VPROLQ (%_% xmm19) (%_% xmm19) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x00; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% xmm24) (%_% xmm24) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xcd; 0x08; 0x25; 0xc4; 0xd2;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm6) (%_% xmm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x18; 0xef; 0x06;
                           (* VPXORQ (%_% xmm0) (%_% xmm0) (Memop Quadword (%% (rsi,0)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0xb3; 0x9d; 0x08; 0x25; 0xf2; 0xd2;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm12) (%_% xmm18) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xed; 0x00; 0x25; 0xe0; 0xd2;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm18) (%_% xmm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xbd; 0x00; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm24) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x8d; 0x00; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xb5; 0x08; 0x25; 0xda; 0xd2;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm9) (%_% xmm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xad; 0x08; 0x25; 0xc8; 0xd2;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm10) (%_% xmm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xfd; 0x00; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm16) (%_% xmm22) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xcd; 0x00; 0x25; 0xc6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm22) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm7) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xc5; 0x08; 0x25; 0xcd; 0xd2;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm7) (%_% xmm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0x95; 0x08; 0x25; 0xfb; 0xd2;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm13) (%_% xmm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xe5; 0x00; 0x25; 0xec; 0xd2;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm19) (%_% xmm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xdd; 0x00; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm20) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xd5; 0x08; 0x25; 0xe3; 0xd2;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm5) (%_% xmm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xa5; 0x08; 0x25; 0xe9; 0xd2;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm11) (%_% xmm17) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x00; 0x25; 0xdf; 0xd2;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm17) (%_% xmm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xc5; 0x00; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm23) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf8;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xbd; 0x08; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm8) (%_% xmm14) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x53; 0x8d; 0x08; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm14) (%_% xmm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0x85; 0x08; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm15) (%_% xmm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xd5; 0x00; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm21) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% xmm25) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xe5; 0x08; 0x25; 0xc9; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm3) (%_% xmm1) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xdd; 0x08; 0x25; 0xca; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm4) (%_% xmm2) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% xmm26) (%_% xmm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xb5; 0x08; 0x25; 0xd7; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm9) (%_% xmm7) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x08; 0x25; 0xd0; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm5) (%_% xmm8) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xdc;
                           (* VMOVDQA64 (%_% xmm27) (%_% xmm12) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xad; 0x08; 0x25; 0xdd; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm10) (%_% xmm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xa5; 0x08; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm11) (%_% xmm14) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xe2;
                           (* VMOVDQA64 (%_% xmm28) (%_% xmm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x00; 0x25; 0xe3; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm16) (%_% xmm19) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xf5; 0x00; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm17) (%_% xmm15) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xfd; 0x08; 0x6f; 0xe8;
                           (* VMOVDQA64 (%_% xmm29) (%_% xmm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xcd; 0x00; 0x25; 0xec; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm22) (%_% xmm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xc5; 0x00; 0x25; 0xed; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm23) (%_% xmm21) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x9d; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x08; 0x72; 0xcb; 0x24;
                           (* VPROLQ (%_% xmm3) (%_% xmm3) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x08; 0x72; 0xc9; 0x03;
                           (* VPROLQ (%_% xmm1) (%_% xmm1) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x08; 0x72; 0xcc; 0x29;
                           (* VPROLQ (%_% xmm4) (%_% xmm4) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x08; 0x72; 0xca; 0x12;
                           (* VPROLQ (%_% xmm2) (%_% xmm2) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x08; 0x72; 0xce; 0x01;
                           (* VPROLQ (%_% xmm6) (%_% xmm6) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x08; 0x72; 0xc9; 0x2c;
                           (* VPROLQ (%_% xmm9) (%_% xmm9) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x08; 0x72; 0xcf; 0x0a;
                           (* VPROLQ (%_% xmm7) (%_% xmm7) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x08; 0x72; 0xcd; 0x2d;
                           (* VPROLQ (%_% xmm5) (%_% xmm5) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x08; 0x72; 0xc8; 0x02;
                           (* VPROLQ (%_% xmm8) (%_% xmm8) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x08; 0x72; 0xcc; 0x3e;
                           (* VPROLQ (%_% xmm12) (%_% xmm12) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x08; 0x72; 0xca; 0x06;
                           (* VPROLQ (%_% xmm10) (%_% xmm10) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x08; 0x72; 0xcd; 0x2b;
                           (* VPROLQ (%_% xmm13) (%_% xmm13) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x08; 0x72; 0xcb; 0x0f;
                           (* VPROLQ (%_% xmm11) (%_% xmm11) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x08; 0x72; 0xce; 0x3d;
                           (* VPROLQ (%_% xmm14) (%_% xmm14) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x00; 0x72; 0xca; 0x1c;
                           (* VPROLQ (%_% xmm18) (%_% xmm18) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x00; 0x72; 0xc8; 0x37;
                           (* VPROLQ (%_% xmm16) (%_% xmm16) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x00; 0x72; 0xcb; 0x19;
                           (* VPROLQ (%_% xmm19) (%_% xmm19) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x00; 0x72; 0xc9; 0x15;
                           (* VPROLQ (%_% xmm17) (%_% xmm17) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x08; 0x72; 0xcf; 0x38;
                           (* VPROLQ (%_% xmm15) (%_% xmm15) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x00; 0x72; 0xc8; 0x1b;
                           (* VPROLQ (%_% xmm24) (%_% xmm24) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x00; 0x72; 0xce; 0x14;
                           (* VPROLQ (%_% xmm22) (%_% xmm22) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x00; 0x72; 0xcc; 0x27;
                           (* VPROLQ (%_% xmm20) (%_% xmm20) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x00; 0x72; 0xcf; 0x08;
                           (* VPROLQ (%_% xmm23) (%_% xmm23) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x00; 0x72; 0xcd; 0x0e;
                           (* VPROLQ (%_% xmm21) (%_% xmm21) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xb5; 0x08; 0x25; 0xc5; 0xd2;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm9) (%_% xmm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x18; 0xef; 0x46; 0x01;
                           (* VPXORQ (%_% xmm0) (%_% xmm0) (Memop Quadword (%% (rsi,8)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0x33; 0x95; 0x08; 0x25; 0xc9; 0xd2;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm13) (%_% xmm17) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x00; 0x25; 0xed; 0xd2;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm17) (%_% xmm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xd5; 0x00; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm21) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xcd; 0x00; 0x25; 0xd1; 0xd2;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm22) (%_% xmm1) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xf5; 0x08; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm1) (%_% xmm5) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xd5; 0x08; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm5) (%_% xmm14) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x08; 0x25; 0xee; 0xd2;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm14) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x00; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf6;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xfa;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm10) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xad; 0x08; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm10) (%_% xmm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xe5; 0x00; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm19) (%_% xmm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xc5; 0x00; 0x25; 0xda; 0xd2;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm23) (%_% xmm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xed; 0x08; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm2) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x00; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xfd; 0x08; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xfb;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xe5; 0x08; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm3) (%_% xmm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xc5; 0x08; 0x25; 0xdb; 0xd2;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm7) (%_% xmm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xa5; 0x08; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm11) (%_% xmm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x85; 0x08; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm15) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x00; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm12) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xf8;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm16) (Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xfd; 0x00; 0x25; 0xe4; 0xd2;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm16) (%_% xmm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xdd; 0x00; 0x25; 0xc4; 0xd2;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm20) (%_% xmm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xdd; 0x08; 0x25; 0xe0; 0xd2;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm4) (%_% xmm8) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xbd; 0x08; 0x25; 0xe6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm8) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x00; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% xmm25) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xed; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm18) (%_% xmm6) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x00; 0x25; 0xcc; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm24) (%_% xmm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% xmm26) (%_% xmm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x00; 0x25; 0xd2; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm22) (%_% xmm10) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xe5; 0x08; 0x25; 0xd0; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm3) (%_% xmm16) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xdd;
                           (* VMOVDQA64 (%_% xmm27) (%_% xmm13) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x08; 0x25; 0xdb; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm1) (%_% xmm19) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xc5; 0x08; 0x25; 0xdc; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm7) (%_% xmm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% xmm28) (%_% xmm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xd5; 0x08; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm5) (%_% xmm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xa5; 0x08; 0x25; 0xe4; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm11) (%_% xmm4) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xed;
                           (* VMOVDQA64 (%_% xmm29) (%_% xmm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0x8d; 0x08; 0x25; 0xea; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm14) (%_% xmm2) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x85; 0x08; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm15) (%_% xmm8) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x95; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x00; 0x72; 0xca; 0x24;
                           (* VPROLQ (%_% xmm18) (%_% xmm18) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x08; 0x72; 0xce; 0x03;
                           (* VPROLQ (%_% xmm6) (%_% xmm6) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x00; 0x72; 0xc8; 0x29;
                           (* VPROLQ (%_% xmm24) (%_% xmm24) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x08; 0x72; 0xcc; 0x12;
                           (* VPROLQ (%_% xmm12) (%_% xmm12) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x08; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% xmm9) (%_% xmm9) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x00; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% xmm22) (%_% xmm22) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x08; 0x72; 0xca; 0x0a;
                           (* VPROLQ (%_% xmm10) (%_% xmm10) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x08; 0x72; 0xcb; 0x2d;
                           (* VPROLQ (%_% xmm3) (%_% xmm3) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x00; 0x72; 0xc8; 0x02;
                           (* VPROLQ (%_% xmm16) (%_% xmm16) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x08; 0x72; 0xcd; 0x3e;
                           (* VPROLQ (%_% xmm13) (%_% xmm13) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x08; 0x72; 0xc9; 0x06;
                           (* VPROLQ (%_% xmm1) (%_% xmm1) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x00; 0x72; 0xcb; 0x2b;
                           (* VPROLQ (%_% xmm19) (%_% xmm19) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x08; 0x72; 0xcf; 0x0f;
                           (* VPROLQ (%_% xmm7) (%_% xmm7) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x00; 0x72; 0xcc; 0x3d;
                           (* VPROLQ (%_% xmm20) (%_% xmm20) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x00; 0x72; 0xc9; 0x1c;
                           (* VPROLQ (%_% xmm17) (%_% xmm17) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x08; 0x72; 0xcd; 0x37;
                           (* VPROLQ (%_% xmm5) (%_% xmm5) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x00; 0x72; 0xcf; 0x19;
                           (* VPROLQ (%_% xmm23) (%_% xmm23) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x08; 0x72; 0xcb; 0x15;
                           (* VPROLQ (%_% xmm11) (%_% xmm11) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x08; 0x72; 0xcc; 0x38;
                           (* VPROLQ (%_% xmm4) (%_% xmm4) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x00; 0x72; 0xcd; 0x1b;
                           (* VPROLQ (%_% xmm21) (%_% xmm21) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x08; 0x72; 0xce; 0x14;
                           (* VPROLQ (%_% xmm14) (%_% xmm14) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x08; 0x72; 0xca; 0x27;
                           (* VPROLQ (%_% xmm2) (%_% xmm2) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x08; 0x72; 0xcf; 0x08;
                           (* VPROLQ (%_% xmm15) (%_% xmm15) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x08; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% xmm8) (%_% xmm8) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xcd; 0x00; 0x25; 0xc3; 0xd2;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm22) (%_% xmm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x18; 0xef; 0x46; 0x02;
                           (* VPXORQ (%_% xmm0) (%_% xmm0) (Memop Quadword (%% (rsi,16)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0xc3; 0xe5; 0x00; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm19) (%_% xmm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xa5; 0x08; 0x25; 0xd8; 0xd2;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm11) (%_% xmm8) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xbd; 0x08; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm8) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x00; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm14) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0x8d; 0x08; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm14) (%_% xmm6) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xcd; 0x08; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm6) (%_% xmm3) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xe5; 0x08; 0x25; 0xf4; 0xd2;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm3) (%_% xmm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xdd; 0x00; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm20) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x08; 0x25; 0xcf; 0xd2;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm1) (%_% xmm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xc5; 0x00; 0x25; 0xcf; 0xd2;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm23) (%_% xmm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0x85; 0x08; 0x25; 0xfc; 0xd2;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm15) (%_% xmm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x08; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm12) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x00; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xf5;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xfa;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xed; 0x00; 0x25; 0xea; 0xd2;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm18) (%_% xmm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xad; 0x08; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm10) (%_% xmm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xc5; 0x08; 0x25; 0xd4; 0xd2;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm7) (%_% xmm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xdd; 0x08; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm4) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x00; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf5;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm13) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xd5; 0x08; 0x25; 0xea; 0xd2;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm5) (%_% xmm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xed; 0x08; 0x25; 0xe8; 0xd2;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm2) (%_% xmm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xbd; 0x00; 0x25; 0xd0; 0xd2;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm24) (%_% xmm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xfd; 0x00; 0x25; 0xc6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm16) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% xmm25) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xf5; 0x00; 0x25; 0xc9; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm17) (%_% xmm9) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x00; 0x25; 0xcd; 0x96;
                           (* VPTERNLOGQ (%_% xmm25) (%_% xmm21) (%_% xmm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% xmm26) (%_% xmm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0x8d; 0x08; 0x25; 0xd1; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm14) (%_% xmm1) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xed; 0x00; 0x25; 0xd5; 0x96;
                           (* VPTERNLOGQ (%_% xmm26) (%_% xmm18) (%_% xmm5) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xdb;
                           (* VMOVDQA64 (%_% xmm27) (%_% xmm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xcd; 0x08; 0x25; 0xdf; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm6) (%_% xmm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xad; 0x08; 0x25; 0xda; 0x96;
                           (* VPTERNLOGQ (%_% xmm27) (%_% xmm10) (%_% xmm2) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% xmm28) (%_% xmm11) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xe5; 0x08; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm3) (%_% xmm15) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xc5; 0x08; 0x25; 0xe0; 0x96;
                           (* VPTERNLOGQ (%_% xmm28) (%_% xmm7) (%_% xmm24) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xe8;
                           (* VMOVDQA64 (%_% xmm29) (%_% xmm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xdd; 0x00; 0x25; 0xec; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm20) (%_% xmm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xdd; 0x08; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% xmm29) (%_% xmm4) (%_% xmm16) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm29) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x00; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm25) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x00; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x00; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm26) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x00; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x00; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xa5; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm27) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x00; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% xmm30) (%_% xmm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x00; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x00; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm28) (%_% xmm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x00; 0x72; 0xc9; 0x24;
                           (* VPROLQ (%_% xmm17) (%_% xmm17) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x08; 0x72; 0xc9; 0x03;
                           (* VPROLQ (%_% xmm9) (%_% xmm9) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x00; 0x72; 0xcd; 0x29;
                           (* VPROLQ (%_% xmm21) (%_% xmm21) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x08; 0x72; 0xcd; 0x12;
                           (* VPROLQ (%_% xmm13) (%_% xmm13) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x00; 0x72; 0xce; 0x01;
                           (* VPROLQ (%_% xmm22) (%_% xmm22) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x08; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% xmm14) (%_% xmm14) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x08; 0x72; 0xc9; 0x0a;
                           (* VPROLQ (%_% xmm1) (%_% xmm1) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x00; 0x72; 0xca; 0x2d;
                           (* VPROLQ (%_% xmm18) (%_% xmm18) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x08; 0x72; 0xcd; 0x02;
                           (* VPROLQ (%_% xmm5) (%_% xmm5) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x00; 0x72; 0xcb; 0x3e;
                           (* VPROLQ (%_% xmm19) (%_% xmm19) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x08; 0x72; 0xce; 0x06;
                           (* VPROLQ (%_% xmm6) (%_% xmm6) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x00; 0x72; 0xcf; 0x2b;
                           (* VPROLQ (%_% xmm23) (%_% xmm23) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x08; 0x72; 0xca; 0x0f;
                           (* VPROLQ (%_% xmm10) (%_% xmm10) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x08; 0x72; 0xca; 0x3d;
                           (* VPROLQ (%_% xmm2) (%_% xmm2) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x08; 0x72; 0xcb; 0x1c;
                           (* VPROLQ (%_% xmm11) (%_% xmm11) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x08; 0x72; 0xcb; 0x37;
                           (* VPROLQ (%_% xmm3) (%_% xmm3) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x08; 0x72; 0xcf; 0x19;
                           (* VPROLQ (%_% xmm15) (%_% xmm15) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x08; 0x72; 0xcf; 0x15;
                           (* VPROLQ (%_% xmm7) (%_% xmm7) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x00; 0x72; 0xc8; 0x38;
                           (* VPROLQ (%_% xmm24) (%_% xmm24) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x08; 0x72; 0xc8; 0x1b;
                           (* VPROLQ (%_% xmm8) (%_% xmm8) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x00; 0x72; 0xcc; 0x14;
                           (* VPROLQ (%_% xmm20) (%_% xmm20) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x08; 0x72; 0xcc; 0x27;
                           (* VPROLQ (%_% xmm12) (%_% xmm12) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x08; 0x72; 0xcc; 0x08;
                           (* VPROLQ (%_% xmm4) (%_% xmm4) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x00; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% xmm16) (%_% xmm16) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm14) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0x8d; 0x08; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm0) (%_% xmm14) (%_% xmm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x18; 0xef; 0x46; 0x03;
                           (* VPXORQ (%_% xmm0) (%_% xmm0) (Memop Quadword (%% (rsi,24)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0x73; 0xc5; 0x00; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm14) (%_% xmm23) (%_% xmm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xa3; 0xc5; 0x08; 0x25; 0xf8; 0xd2;
                           (* VPTERNLOGQ (%_% xmm23) (%_% xmm7) (%_% xmm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xfd; 0x00; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% xmm7) (%_% xmm16) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x00; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm16) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm11) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xfc;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm20) (Evex_deco Unmasked No_brc) *)
  0x62; 0x53; 0xdd; 0x00; 0x25; 0xd9; 0xd2;
                           (* VPTERNLOGQ (%_% xmm11) (%_% xmm20) (%_% xmm9) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xa3; 0xb5; 0x08; 0x25; 0xe2; 0xd2;
                           (* VPTERNLOGQ (%_% xmm20) (%_% xmm9) (%_% xmm18) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xed; 0x00; 0x25; 0xca; 0xd2;
                           (* VPTERNLOGQ (%_% xmm9) (%_% xmm18) (%_% xmm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xed; 0x08; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm18) (%_% xmm2) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x00; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm2) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xf6;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xcd; 0x08; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm22) (%_% xmm6) (%_% xmm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf3; 0x85; 0x08; 0x25; 0xf4; 0xd2;
                           (* VPTERNLOGQ (%_% xmm6) (%_% xmm15) (%_% xmm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x53; 0xdd; 0x08; 0x25; 0xfd; 0xd2;
                           (* VPTERNLOGQ (%_% xmm15) (%_% xmm4) (%_% xmm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x08; 0x25; 0xe6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm4) (%_% xmm13) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x00; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% xmm13) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xf5; 0x00; 0x25; 0xc1; 0xd2;
                           (* VPTERNLOGQ (%_% xmm8) (%_% xmm17) (%_% xmm1) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xf5; 0x08; 0x25; 0xca; 0xd2;
                           (* VPTERNLOGQ (%_% xmm17) (%_% xmm1) (%_% xmm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x08; 0x25; 0xc8; 0xd2;
                           (* VPTERNLOGQ (%_% xmm1) (%_% xmm10) (%_% xmm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xbd; 0x00; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% xmm10) (%_% xmm24) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x8d; 0x00; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% xmm24) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x08; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xfb;
                           (* VMOVDQA64 (%_% xmm31) (%_% xmm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xe5; 0x08; 0x25; 0xdc; 0xd2;
                           (* VPTERNLOGQ (%_% xmm19) (%_% xmm3) (%_% xmm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0x9d; 0x08; 0x25; 0xdd; 0xd2;
                           (* VPTERNLOGQ (%_% xmm3) (%_% xmm12) (%_% xmm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xd5; 0x00; 0x25; 0xe5; 0xd2;
                           (* VPTERNLOGQ (%_% xmm12) (%_% xmm21) (%_% xmm5) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xd5; 0x08; 0x25; 0xee; 0xd2;
                           (* VPTERNLOGQ (%_% xmm21) (%_% xmm5) (%_% xmm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x00; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% xmm5) (%_% xmm30) (%_% xmm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm1) (Evex_deco Unmasked No_brc) *)
  0xc5; 0x79; 0x7f; 0xf1;  (* VMOVDQA (%_% xmm1) (%_% xmm14) *)
  0xc4; 0x41; 0x79; 0x6f; 0xf5;
                           (* VMOVDQA (%_% xmm14) (%_% xmm13) *)
  0xc5; 0x79; 0x6f; 0xec;  (* VMOVDQA (%_% xmm13) (%_% xmm4) *)
  0x62; 0xb1; 0xfd; 0x08; 0x6f; 0xe0;
                           (* VMOVDQA64 (%_% xmm4) (%_% xmm16) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x08; 0x6f; 0xc1;
                           (* VMOVDQA64 (%_% xmm16) (%_% xmm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x81; 0xfd; 0x08; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% xmm17) (%_% xmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x08; 0x6f; 0xd7;
                           (* VMOVDQA64 (%_% xmm2) (%_% xmm23) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x08; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% xmm23) (%_% xmm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfd; 0x08; 0x6f; 0xeb;
                           (* VMOVDQA64 (%_% xmm21) (%_% xmm3) (Evex_deco Unmasked No_brc) *)
  0xc5; 0xf9; 0x6f; 0xdf;  (* VMOVDQA (%_% xmm3) (%_% xmm7) *)
  0xc5; 0x79; 0x7f; 0xcf;  (* VMOVDQA (%_% xmm7) (%_% xmm9) *)
  0x62; 0x11; 0xfd; 0x08; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% xmm9) (%_% xmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x6f; 0xf5;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm5) (Evex_deco Unmasked No_brc) *)
  0xc5; 0x79; 0x7f; 0xdd;  (* VMOVDQA (%_% xmm5) (%_% xmm11) *)
  0xc5; 0x79; 0x6f; 0xde;  (* VMOVDQA (%_% xmm11) (%_% xmm6) *)
  0x62; 0xb1; 0xfd; 0x08; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% xmm6) (%_% xmm20) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x08; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% xmm20) (%_% xmm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0x81; 0xfd; 0x08; 0x6f; 0xd8;
                           (* VMOVDQA64 (%_% xmm19) (%_% xmm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xfd; 0x08; 0x6f; 0xc6;
                           (* VMOVDQA64 (%_% xmm24) (%_% xmm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x08; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% xmm30) (%_% xmm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x08; 0x6f; 0xc2;
                           (* VMOVDQA64 (%_% xmm8) (%_% xmm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x08; 0x6f; 0xd2;
                           (* VMOVDQA64 (%_% xmm18) (%_% xmm10) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x08; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% xmm10) (%_% xmm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x08; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% xmm22) (%_% xmm12) (Evex_deco Unmasked No_brc) *)
  0xc4; 0x41; 0x79; 0x6f; 0xe7;
                           (* VMOVDQA (%_% xmm12) (%_% xmm15) *)
  0x62; 0x11; 0xfd; 0x08; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% xmm15) (%_% xmm30) (Evex_deco Unmasked No_brc) *)
  0x48; 0x83; 0xc6; 0x20;  (* ADD (% rsi) (Imm8 (word 32)) *)
  0x48; 0x39; 0xc6;        (* CMP (% rsi) (% rax) *)
  0x0f; 0x85; 0x1a; 0xf4; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294964250)) *)
  0xc5; 0xf9; 0xd6; 0x07;  (* VMOVQ (Memop Quadword (%% (rdi,0))) (%_% xmm0) *)
  0xc5; 0xf9; 0xd6; 0x4f; 0x08;
                           (* VMOVQ (Memop Quadword (%% (rdi,8))) (%_% xmm1) *)
  0xc5; 0xf9; 0xd6; 0x57; 0x10;
                           (* VMOVQ (Memop Quadword (%% (rdi,16))) (%_% xmm2) *)
  0xc5; 0xf9; 0xd6; 0x5f; 0x18;
                           (* VMOVQ (Memop Quadword (%% (rdi,24))) (%_% xmm3) *)
  0xc5; 0xf9; 0xd6; 0x67; 0x20;
                           (* VMOVQ (Memop Quadword (%% (rdi,32))) (%_% xmm4) *)
  0xc5; 0xf9; 0xd6; 0x6f; 0x28;
                           (* VMOVQ (Memop Quadword (%% (rdi,40))) (%_% xmm5) *)
  0xc5; 0xf9; 0xd6; 0x77; 0x30;
                           (* VMOVQ (Memop Quadword (%% (rdi,48))) (%_% xmm6) *)
  0xc5; 0xf9; 0xd6; 0x7f; 0x38;
                           (* VMOVQ (Memop Quadword (%% (rdi,56))) (%_% xmm7) *)
  0xc5; 0x79; 0xd6; 0x47; 0x40;
                           (* VMOVQ (Memop Quadword (%% (rdi,64))) (%_% xmm8) *)
  0xc5; 0x79; 0xd6; 0x4f; 0x48;
                           (* VMOVQ (Memop Quadword (%% (rdi,72))) (%_% xmm9) *)
  0xc5; 0x79; 0xd6; 0x57; 0x50;
                           (* VMOVQ (Memop Quadword (%% (rdi,80))) (%_% xmm10) *)
  0xc5; 0x79; 0xd6; 0x5f; 0x58;
                           (* VMOVQ (Memop Quadword (%% (rdi,88))) (%_% xmm11) *)
  0xc5; 0x79; 0xd6; 0x67; 0x60;
                           (* VMOVQ (Memop Quadword (%% (rdi,96))) (%_% xmm12) *)
  0xc5; 0x79; 0xd6; 0x6f; 0x68;
                           (* VMOVQ (Memop Quadword (%% (rdi,104))) (%_% xmm13) *)
  0xc5; 0x79; 0xd6; 0x77; 0x70;
                           (* VMOVQ (Memop Quadword (%% (rdi,112))) (%_% xmm14) *)
  0xc5; 0x79; 0xd6; 0x7f; 0x78;
                           (* VMOVQ (Memop Quadword (%% (rdi,120))) (%_% xmm15) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x47; 0x10;
                           (* VMOVQ (Memop Quadword (%% (rdi,128))) (%_% xmm16) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x4f; 0x11;
                           (* VMOVQ (Memop Quadword (%% (rdi,136))) (%_% xmm17) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x57; 0x12;
                           (* VMOVQ (Memop Quadword (%% (rdi,144))) (%_% xmm18) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x5f; 0x13;
                           (* VMOVQ (Memop Quadword (%% (rdi,152))) (%_% xmm19) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x67; 0x14;
                           (* VMOVQ (Memop Quadword (%% (rdi,160))) (%_% xmm20) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x6f; 0x15;
                           (* VMOVQ (Memop Quadword (%% (rdi,168))) (%_% xmm21) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x77; 0x16;
                           (* VMOVQ (Memop Quadword (%% (rdi,176))) (%_% xmm22) *)
  0x62; 0xe1; 0xfd; 0x08; 0x7e; 0x7f; 0x17;
                           (* VMOVQ (Memop Quadword (%% (rdi,184))) (%_% xmm23) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x47; 0x18;
                           (* VMOVQ (Memop Quadword (%% (rdi,192))) (%_% xmm24) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let keccak_f1600_x1_avx512_tmc =
  define_trimmed "keccak_f1600_x1_avx512_tmc" keccak_f1600_x1_avx512_mc;;

let KECCAK_F1600_X1_AVX512_TMC_EXEC =
  X86_MK_EXEC_RULE keccak_f1600_x1_avx512_tmc;;

(* ------------------------------------------------------------------------- *)
(* The layout of the state: lane k in the low quadword of the xmm register   *)
(* given by keccak_avx512_layout0-3. The high quadwords are not kept zero    *)
(* (iota broadcasts the round constant to both quadwords of xmm0), but they  *)
(* never reach the low ones.                                                 *)
(* ------------------------------------------------------------------------- *)

let keccak_avx512_lanes = define
 `keccak_avx512_lanes (l:num list) (A:int64 list) = MAP (\k. EL k A) l`;;

let keccak_avx512_assertion =
  let regs =
    mk_list(map (fun k ->
      subst [mk_const("YMM"^string_of_int k,[]),
             `Y:(x86state,int256)component`]
       `word_subword (read (Y:(x86state,int256)component) s) (0,64)
        :int64`) (0--24),`:int64`) in
  fun layout n ->
    let tm = subst [layout,`l:num list`; n,`n:num`]
     `keccak_avx512_lanes l (keccak n A)` in
    mk_abs(`s:x86state`,
      list_mk_conj
       [`read RDI s = a`; `read RSI s = word_add rc (word(32 * i))`;
        `read RAX s = word_add rc (word 192)`;
        `wordlist_from_memory(rc,24) s = round_constants`;
        mk_eq(regs,tm)]);;

(*** Each word_subword (read YMMk s0) (0,64) = x as read YMMk s0 =
 *** word_join h<k> x, the rest of the register abbreviated
 ***)

let KECCAK_AVX512_SPLIT_LOW = prove
 (`!y:int256 x:int64.
        word_subword y (0,64) = x
        ==> y = word_join (word_subword y (64,192):192 word) x`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BLAST);;

let KECCAK_AVX512_HIGHS_TAC =
  let pat = `word_subword (read c (s0:x86state):int256) (0,64):int64 = x` in
  fun (asl,w as gl) ->
    let ths = filter (can (term_match [] pat) o concl) (map snd asl) in
    MAP_EVERY (fun th ->
      let rd = lhand(lhand(concl th)) in
      let n = name_of(rand(rator rd)) in
      let hv = mk_var("h"^String.sub n 3 (String.length n - 3),`:192 word`) in
      MP_TAC(MATCH_MP KECCAK_AVX512_SPLIT_LOW th) THEN
      ABBREV_TAC(mk_eq(hv,subst [rd,`y:int256`]
                           `word_subword (y:int256) (64,192):192 word`)) THEN
      DISCH_TAC) ths gl;;

(* ------------------------------------------------------------------------- *)
(* A round r = 1-4 of an iteration i, as in keccak_f1600_x4_avx512, with the *)
(* lanes x<k> of the state.                                                  *)
(* ------------------------------------------------------------------------- *)

(*** The round as a tactic with parameters: init after the initial state
 *** is set up, fin on the tactic that proves the final state, and side for
 *** the conjuncts other than the lanes (the loop test after round 4)
 ***)

let KECCAK_AVX512_ROUND_GEN_TAC init fin side r nsteps =
  let nin = if r = 1 then `4 * i` else
    mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral(r-1))
  and nout = if r = 4 then `4 * (i + 1)` else
    mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral r) in
  let kth = REWRITE_RULE
    [ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` nin `1`,nout))]
    (INST [nin,`n:num`] (CONJUNCT2 keccak)) in
  let rcaddr = if r = 1 then `word_add (rc:int64) (word(32 * i))` else
    subst [mk_small_numeral(8*(r-1)),`d:num`]
     `word_add (rc:int64) (word(32 * i + d))` in
  let rcgoal = subst [rcaddr,`x:int64`]
    `read (memory :> bytes64 x) s0 = rcon`
  and sn = mk_var("s"^string_of_int nsteps,`:x86state`) in
  REWRITE_TAC[kth] THEN
  MP_TAC(ISPECL [`A:int64 list`; nin] LENGTH_KECCAK) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_EQ_25] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY (fun k ->
    ABBREV_TAC(mk_eq(mk_var("x"^string_of_int k,`:int64`),
      list_mk_comb(`EL:num->int64 list->int64`,
        [mk_small_numeral k; list_mk_comb(`keccak`,[nin;`A:int64 list`])]))))
   (0--24) THEN
  ABBREV_TAC(mk_eq(`rcon:int64`,
    list_mk_comb(`EL:num->int64 list->int64`,[nin;`round_constants`]))) THEN
  REWRITE_TAC[KECCAK_ROUND_EXPLICIT] THEN
  REWRITE_TAC[keccak_avx512_lanes; keccak_avx512_layout0;
              keccak_avx512_layout1; keccak_avx512_layout2;
              keccak_avx512_layout3; MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
  ENSURES_INIT_TAC "s0" THEN init THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[round_constants; CONS_11] o
    CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV) o
    check (can (term_match [] `wordlist_from_memory(rc,24) s = l`) o
           concl)) THEN
  SUBGOAL_THEN rcgoal ASSUME_TAC THENL
   [EXPAND_TAC "rcon" THEN UNDISCH_TAC `i < 6` THEN
    SPEC_TAC(`i:num`,`i:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  KECCAK_AVX512_HIGHS_TAC THEN
  (fun gl -> keccak_avx2_lanes := 0; ALL_TAC gl) THEN
  MAP_EVERY (fun n ->
    X86_STEPS_TAC KECCAK_F1600_X1_AVX512_TMC_EXEC [n] THEN
    KECCAK_AVX512_SIMPLIFY_TAC THEN KECCAK_AVX2_LANE_ABBREV_TAC n)
   (1--nsteps) THEN
  ENSURES_FINAL_STATE_TAC THEN
  fin
   (ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[round_constants; CONS_11;
      WORDLIST_FROM_MEMORY_CONV
       (subst [sn,`s:x86state`]
         `wordlist_from_memory(rc,24) s:int64 list`)] THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64] THEN
    side THEN
    KECCAK_AVX2_EXPAND_TAC THEN
    REPEAT CONJ_TAC THEN KECCAK_AVX512_BITBLAST_TAC);;

let KECCAK_AVX512_ROUND_TAC r nsteps =
  KECCAK_AVX512_ROUND_GEN_TAC ALL_TAC I
   (if r = 4 then
      MP_TAC(SPECL [`rc:int64`; `i:num`] KECCAK_AVX512_ZF) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; KECCAK_AVX512_RSI])
    else ALL_TAC)
   r nsteps;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The x1 permutation keccak_f1600_x1_avx512.                                *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX512_FULL_ROUND_TAC r nsteps =
  KECCAK_AVX512_ROUND_GEN_TAC (TRY STRIP_EXISTS_ASSUM_TAC)
   EVENTS_SPLIT_TAC
   (if r = 4 then
      MP_TAC(SPECL [`rc:int64`; `i:num`] KECCAK_AVX512_ZF_BRANCH) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[th; KECCAK_AVX512_RSI; KECCAK_AVX512_WORD_COND])
    else ALL_TAC)
   r nsteps;;

let KECCAK_F1600_X1_AVX512_FULL = time prove
 (`exists f_events.
    forall e a rc A pc.
        nonoverlapping (a,200) (word pc,0xd0d) /\
        nonoverlapping (a,200) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x1_avx512_tmc /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A /\
                 read events s = e)
            (\s. read RIP s = word (pc + 0xd0c) /\
                 wordlist_from_memory(a,25) s = keccak 24 A /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc /\
                      memaccess_inbounds e2 [a,200; rc,192] [a,200]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17;
              ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25;
              ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,200)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil rc a pc)
       (APPEND
         (ENUMERATEL 6
           (\i. APPEND (APPEND (APPEND (f_ev_r4 rc a pc i) (f_ev_r3 rc a pc i))
                               (f_ev_r2 rc a pc i))
                       (f_ev_r1 rc a pc i)))
         (f_ev_prol rc a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `rc:int64`; `A:int64 list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `LENGTH(A:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x95` `pc + 0xc7b`
   `\i s. read RDI s = a /\
           read RSI s = word_add rc (word(32 * i)) /\
           read RAX s = word_add rc (word 192) /\
           wordlist_from_memory(rc,24) s = round_constants /\
           [word_subword (read YMM0 s) (0,64);
            word_subword (read YMM1 s) (0,64);
            word_subword (read YMM2 s) (0,64);
            word_subword (read YMM3 s) (0,64);
            word_subword (read YMM4 s) (0,64);
            word_subword (read YMM5 s) (0,64);
            word_subword (read YMM6 s) (0,64);
            word_subword (read YMM7 s) (0,64);
            word_subword (read YMM8 s) (0,64);
            word_subword (read YMM9 s) (0,64);
            word_subword (read YMM10 s) (0,64);
            word_subword (read YMM11 s) (0,64);
            word_subword (read YMM12 s) (0,64);
            word_subword (read YMM13 s) (0,64);
            word_subword (read YMM14 s) (0,64);
            word_subword (read YMM15 s) (0,64);
            word_subword (read YMM16 s) (0,64);
            word_subword (read YMM17 s) (0,64);
            word_subword (read YMM18 s) (0,64);
            word_subword (read YMM19 s) (0,64);
            word_subword (read YMM20 s) (0,64);
            word_subword (read YMM21 s) (0,64);
            word_subword (read YMM22 s) (0,64);
            word_subword (read YMM23 s) (0,64);
            word_subword (read YMM24 s) (0,64)] =
           keccak_avx512_lanes keccak_avx512_layout0 (keccak (4 * i) A)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    MP_TAC(ISPEC `A:int64 list` LENGTH_EQ_25) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[MULT_CLAUSES; keccak; keccak_avx512_lanes;
                keccak_avx512_layout0; MAP] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; WORD_ADD_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC KECCAK_F1600_X1_AVX512_TMC_EXEC (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [ENUMERATEL_ADD1] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x364`
     (keccak_avx512_assertion `keccak_avx512_layout1` `4 * i + 1`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 1 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x634`
     (keccak_avx512_assertion `keccak_avx512_layout2` `4 * i + 2`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 2 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x904`
     (keccak_avx512_assertion `keccak_avx512_layout3` `4 * i + 3`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 3 105; ALL_TAC] THEN
    KECCAK_AVX512_FULL_ROUND_TAC 4 136;

    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY (fun k ->
      ABBREV_TAC(mk_eq(mk_var("z"^string_of_int k,`:int64`),
        list_mk_comb(`EL:num->int64 list->int64`,
          [mk_small_numeral k; `keccak 24 A`])))) (0--24) THEN
    REWRITE_TAC[keccak_avx512_lanes; keccak_avx512_layout0; MAP] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    KECCAK_AVX512_HIGHS_TAC THEN
    X86_STEPS_TAC KECCAK_F1600_X1_AVX512_TMC_EXEC (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST)]);;

(*** The subroutine forms, without and with the IBT landing pad, as for
 *** KECCAK_F1600_X1_AVX512_NOIBT_SUBROUTINE_CORRECT and _SUBROUTINE_SAFE
 *** but with the frame of the former
 ***)

let KECCAK_F1600_X1_AVX512_CORRECT = prove
 (`!a rc A pc.
      nonoverlapping (a,200) (word pc,0xd0d) /\
      nonoverlapping (a,200) (rc,192)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) keccak_f1600_x1_avx512_tmc /\
                read RIP s = word pc /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A)
           (\s. read RIP s = word(pc + 0xd0c) /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE [RIP; RAX; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                       ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21;
                       ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28;
                       ZMM29; ZMM30; ZMM31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,200)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_TAC `f:int64->int64->num->(uarch_event)list`
   KECCAK_F1600_X1_AVX512_FULL THEN
  MATCH_MP_TAC(ISPEC `read events:x86state->(uarch_event)list`
                ENSURES_ANY_INITIAL) THEN
  X_GEN_TAC `e:(uarch_event)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `A:int64 list`; `pc:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_MONO_ALL) THEN
  SIMP_TAC[]);;

let KECCAK_F1600_X1_AVX512_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a rc A pc stackpointer returnaddress.
      nonoverlapping (a,200) (word pc,0xd0d) /\
      nonoverlapping (a,200) (rc,192) /\
      nonoverlapping (a,200) (stackpointer,8)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) keccak_f1600_x1_avx512_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC KECCAK_F1600_X1_AVX512_TMC_EXEC
   (CONV_RULE TWEAK_CONV KECCAK_F1600_X1_AVX512_CORRECT));;

let KECCAK_F1600_X1_AVX512_SUBROUTINE_CORRECT = prove
 (`!a rc A pc stackpointer returnaddress.
      nonoverlapping (a,200) (word pc,0xd11) /\
      nonoverlapping (a,200) (rc,192) /\
      nonoverlapping (a,200) (stackpointer,8)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) keccak_f1600_x1_avx512_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,200)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV
     KECCAK_F1600_X1_AVX512_NOIBT_SUBROUTINE_CORRECT)));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/consttime.ml";;
needs "mlkem_native/x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "keccak_f1600_x1_avx512" subroutine_signatures)
    KECCAK_F1600_X1_AVX512_CORRECT
    KECCAK_F1600_X1_AVX512_TMC_EXEC;;

(*** The events are those of the loading, of each of the 6 iterations and
 *** of the storing
 ***)

let KECCAK_F1600_X1_AVX512_SAFE = time prove
 (`exists f_events.
    forall e a rc pc.
        nonoverlapping (a,200) (word pc,0xd0d) /\
        nonoverlapping (a,200) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x1_avx512_tmc /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = word (pc + 0xd0c) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc /\
                      memaccess_inbounds e2 [a,200; rc,192] [a,200]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17;
              ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25;
              ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,200)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil rc a pc)
             (APPEND (ENUMERATEL 6 (\i. f_ev_loop rc a pc i))
                     (f_ev_prol rc a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `rc:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x95` `pc + 0xc7b`
   `\i s. read RDI s = a /\
          read RSI s = word_add rc (word(32 * i)) /\
          read RAX s = word_add rc (word 192)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false KECCAK_F1600_X1_AVX512_TMC_EXEC
      (1--26) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    KECCAK_AVX512_SAFE_SIM_TAC KECCAK_F1600_X1_AVX512_TMC_EXEC 451 THEN
    ASM_SIMP_TAC[KECCAK_AVX512_BRANCH] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[KECCAK_AVX512_RSI]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false KECCAK_F1600_X1_AVX512_TMC_EXEC
      (1--26) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let KECCAK_F1600_X1_AVX512_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a rc pc stackpointer returnaddress.
        nonoverlapping (a,200) (word pc,0xd0d) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x1_avx512_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200]))
            (\s s'. true)`,
  X86_ADD_RETURN_NOSTACK_TAC KECCAK_F1600_X1_AVX512_TMC_EXEC
   KECCAK_F1600_X1_AVX512_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let KECCAK_F1600_X1_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a rc pc stackpointer returnaddress.
        nonoverlapping (a,200) (word pc,0xd11) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x1_avx512_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   KECCAK_F1600_X1_AVX512_NOIBT_SUBROUTINE_SAFE));;
