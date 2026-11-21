(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation for SHA3, batch of four independent operations,  *)
(* with AVX-512VL (four rounds per iteration, the state in ymm0-ymm24).      *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/base.ml";;
needs "mlkem_native/x86_64/proofs/keccak_utils.ml";;
needs "mlkem_native/x86_64/proofs/keccak_avx512_utils.ml";;

(**** print_literal_from_elf
        "x86_64/mlkem/keccak_f1600_x4_avx512_asm.o";;
 ****)

let keccak_f1600_x4_avx512_mc = define_assert_from_elf
  "keccak_f1600_x4_avx512_mc"
  "x86_64/mlkem/keccak_f1600_x4_avx512_asm.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x0f;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,0)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,200)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,400)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,600)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xfc;
                           (* VPUNPCKLQDQ (%_% ymm31) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xcc;
                           (* VPUNPCKHQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xc7; 0x00;
                           (* VSHUFI64X2 (%_% ymm0) (%_% ymm29) (%_% ymm31) (Imm8 (word 0)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xc9; 0x00;
                           (* VSHUFI64X2 (%_% ymm1) (%_% ymm30) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xd7; 0x03;
                           (* VSHUFI64X2 (%_% ymm2) (%_% ymm29) (%_% ymm31) (Imm8 (word 3)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xd9; 0x03;
                           (* VSHUFI64X2 (%_% ymm3) (%_% ymm30) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x01;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,32)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,232)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,432)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,632)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xfc;
                           (* VPUNPCKLQDQ (%_% ymm31) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xcc;
                           (* VPUNPCKHQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xe7; 0x00;
                           (* VSHUFI64X2 (%_% ymm4) (%_% ymm29) (%_% ymm31) (Imm8 (word 0)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xe9; 0x00;
                           (* VSHUFI64X2 (%_% ymm5) (%_% ymm30) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x93; 0x95; 0x20; 0x43; 0xf7; 0x03;
                           (* VSHUFI64X2 (%_% ymm6) (%_% ymm29) (%_% ymm31) (Imm8 (word 3)) *)
  0x62; 0x93; 0x8d; 0x20; 0x43; 0xf9; 0x03;
                           (* VSHUFI64X2 (%_% ymm7) (%_% ymm30) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x02;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,64)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,264)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,464)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,664)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xfc;
                           (* VPUNPCKLQDQ (%_% ymm31) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xcc;
                           (* VPUNPCKHQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xc7; 0x00;
                           (* VSHUFI64X2 (%_% ymm8) (%_% ymm29) (%_% ymm31) (Imm8 (word 0)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xc9; 0x00;
                           (* VSHUFI64X2 (%_% ymm9) (%_% ymm30) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xd7; 0x03;
                           (* VSHUFI64X2 (%_% ymm10) (%_% ymm29) (%_% ymm31) (Imm8 (word 3)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xd9; 0x03;
                           (* VSHUFI64X2 (%_% ymm11) (%_% ymm30) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x03;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,96)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,296)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,496)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,696)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xfc;
                           (* VPUNPCKLQDQ (%_% ymm31) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xcc;
                           (* VPUNPCKHQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xe7; 0x00;
                           (* VSHUFI64X2 (%_% ymm12) (%_% ymm29) (%_% ymm31) (Imm8 (word 0)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xe9; 0x00;
                           (* VSHUFI64X2 (%_% ymm13) (%_% ymm30) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x13; 0x95; 0x20; 0x43; 0xf7; 0x03;
                           (* VSHUFI64X2 (%_% ymm14) (%_% ymm29) (%_% ymm31) (Imm8 (word 3)) *)
  0x62; 0x13; 0x8d; 0x20; 0x43; 0xf9; 0x03;
                           (* VSHUFI64X2 (%_% ymm15) (%_% ymm30) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x04;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,128)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,328)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,528)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,728)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xfc;
                           (* VPUNPCKLQDQ (%_% ymm31) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xcc;
                           (* VPUNPCKHQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xc7; 0x00;
                           (* VSHUFI64X2 (%_% ymm16) (%_% ymm29) (%_% ymm31) (Imm8 (word 0)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xc9; 0x00;
                           (* VSHUFI64X2 (%_% ymm17) (%_% ymm30) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xd7; 0x03;
                           (* VSHUFI64X2 (%_% ymm18) (%_% ymm29) (%_% ymm31) (Imm8 (word 3)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xd9; 0x03;
                           (* VSHUFI64X2 (%_% ymm19) (%_% ymm30) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x4f; 0x05;
                           (* VMOVDQU64 (%_% ymm25) (Memop Word256 (%% (rdi,160)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x97; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm26) (Memop Word256 (%% (rdi,360)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0x9f; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm27) (Memop Word256 (%% (rdi,560)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x6f; 0xa7; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (%_% ymm28) (Memop Word256 (%% (rdi,760)))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xb5; 0x20; 0x6c; 0xea;
                           (* VPUNPCKLQDQ (%_% ymm29) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xb5; 0x20; 0x6d; 0xf2;
                           (* VPUNPCKHQDQ (%_% ymm30) (%_% ymm25) (%_% ymm26) *)
  0x62; 0x01; 0xa5; 0x20; 0x6c; 0xfc;
                           (* VPUNPCKLQDQ (%_% ymm31) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x01; 0xa5; 0x20; 0x6d; 0xcc;
                           (* VPUNPCKHQDQ (%_% ymm25) (%_% ymm27) (%_% ymm28) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xe7; 0x00;
                           (* VSHUFI64X2 (%_% ymm20) (%_% ymm29) (%_% ymm31) (Imm8 (word 0)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xe9; 0x00;
                           (* VSHUFI64X2 (%_% ymm21) (%_% ymm30) (%_% ymm25) (Imm8 (word 0)) *)
  0x62; 0x83; 0x95; 0x20; 0x43; 0xf7; 0x03;
                           (* VSHUFI64X2 (%_% ymm22) (%_% ymm29) (%_% ymm31) (Imm8 (word 3)) *)
  0x62; 0x83; 0x8d; 0x20; 0x43; 0xf9; 0x03;
                           (* VSHUFI64X2 (%_% ymm23) (%_% ymm30) (%_% ymm25) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfd; 0x08; 0x6e; 0x47; 0x18;
                           (* VMOVQ (%_% xmm24) (Memop Quadword (%% (rdi,192))) *)
  0x62; 0x63; 0xbd; 0x00; 0x22; 0x47; 0x31; 0x01;
                           (* VPINSRQ (%_% xmm24) (%_% xmm24) (Memop Quadword (%% (rdi,392)))
(Imm8 (word 1)) *)
  0x62; 0x61; 0xfd; 0x08; 0x6e; 0x4f; 0x4a;
                           (* VMOVQ (%_% xmm25) (Memop Quadword (%% (rdi,592))) *)
  0x62; 0x63; 0xb5; 0x00; 0x22; 0x4f; 0x63; 0x01;
                           (* VPINSRQ (%_% xmm25) (%_% xmm25) (Memop Quadword (%% (rdi,792)))
(Imm8 (word 1)) *)
  0x62; 0x03; 0x3d; 0x20; 0x38; 0xc1; 0x01;
                           (* VINSERTI32X4 (%_% ymm24) (%_% ymm24) (%_% xmm25) (Imm8 (word 1)) *)
  0x48; 0x8d; 0x86; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rax) (%% (rsi,192)) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% ymm25) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x28; 0x25; 0xca; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm5) (%_% ymm10) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0x85; 0x28; 0x25; 0xcc; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm15) (%_% ymm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% ymm26) (%_% ymm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x28; 0x25; 0xd3; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm6) (%_% ymm11) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x20; 0x25; 0xd5; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm16) (%_% ymm21) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xda;
                           (* VMOVDQA64 (%_% ymm27) (%_% ymm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xc5; 0x28; 0x25; 0xdc; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm7) (%_% ymm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm17) (%_% ymm22) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% ymm28) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x28; 0x25; 0xe5; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm8) (%_% ymm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xed; 0x20; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm18) (%_% ymm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xec;
                           (* VMOVDQA64 (%_% ymm29) (%_% ymm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xb5; 0x28; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm9) (%_% ymm14) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xe5; 0x20; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm19) (%_% ymm24) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x9d; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x28; 0x72; 0xcd; 0x24;
                           (* VPROLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x28; 0x72; 0xca; 0x03;
                           (* VPROLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x28; 0x72; 0xcf; 0x29;
                           (* VPROLQ (%_% ymm15) (%_% ymm15) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x20; 0x72; 0xcc; 0x12;
                           (* VPROLQ (%_% ymm20) (%_% ymm20) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x28; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x28; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x28; 0x72; 0xcb; 0x0a;
                           (* VPROLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x20; 0x72; 0xc8; 0x2d;
                           (* VPROLQ (%_% ymm16) (%_% ymm16) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x20; 0x72; 0xcd; 0x02;
                           (* VPROLQ (%_% ymm21) (%_% ymm21) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x28; 0x72; 0xca; 0x3e;
                           (* VPROLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x28; 0x72; 0xcf; 0x06;
                           (* VPROLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x28; 0x72; 0xcc; 0x2b;
                           (* VPROLQ (%_% ymm12) (%_% ymm12) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x20; 0x72; 0xc9; 0x0f;
                           (* VPROLQ (%_% ymm17) (%_% ymm17) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x20; 0x72; 0xce; 0x3d;
                           (* VPROLQ (%_% ymm22) (%_% ymm22) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x28; 0x72; 0xcb; 0x1c;
                           (* VPROLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x28; 0x72; 0xc8; 0x37;
                           (* VPROLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x28; 0x72; 0xcd; 0x19;
                           (* VPROLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x20; 0x72; 0xca; 0x15;
                           (* VPROLQ (%_% ymm18) (%_% ymm18) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x20; 0x72; 0xcf; 0x38;
                           (* VPROLQ (%_% ymm23) (%_% ymm23) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x28; 0x72; 0xcc; 0x1b;
                           (* VPROLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x28; 0x72; 0xc9; 0x14;
                           (* VPROLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x28; 0x72; 0xce; 0x27;
                           (* VPROLQ (%_% ymm14) (%_% ymm14) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x20; 0x72; 0xcb; 0x08;
                           (* VPROLQ (%_% ymm19) (%_% ymm19) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x20; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% ymm24) (%_% ymm24) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xcd; 0x28; 0x25; 0xc4; 0xd2;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm6) (%_% ymm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x38; 0xef; 0x06;
                           (* VPXORQ (%_% ymm0) (%_% ymm0) (Memop Quadword (%% (rsi,0)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0xb3; 0x9d; 0x28; 0x25; 0xf2; 0xd2;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm12) (%_% ymm18) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xed; 0x20; 0x25; 0xe0; 0xd2;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm18) (%_% ymm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xbd; 0x20; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm24) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x8d; 0x20; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xb5; 0x28; 0x25; 0xda; 0xd2;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm9) (%_% ymm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xad; 0x28; 0x25; 0xc8; 0xd2;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm10) (%_% ymm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xfd; 0x20; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm16) (%_% ymm22) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xcd; 0x20; 0x25; 0xc6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm22) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xff;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm7) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xc5; 0x28; 0x25; 0xcd; 0xd2;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm7) (%_% ymm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0x95; 0x28; 0x25; 0xfb; 0xd2;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm13) (%_% ymm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xe5; 0x20; 0x25; 0xec; 0xd2;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm19) (%_% ymm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xdd; 0x20; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm20) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm4) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xd5; 0x28; 0x25; 0xe3; 0xd2;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm5) (%_% ymm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xa5; 0x28; 0x25; 0xe9; 0xd2;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm11) (%_% ymm17) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x20; 0x25; 0xdf; 0xd2;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm17) (%_% ymm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xc5; 0x20; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm23) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf8;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xbd; 0x28; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm8) (%_% ymm14) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x53; 0x8d; 0x28; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm14) (%_% ymm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0x85; 0x28; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm15) (%_% ymm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xd5; 0x20; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm21) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% ymm25) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xe5; 0x28; 0x25; 0xc9; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm3) (%_% ymm1) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xdd; 0x28; 0x25; 0xca; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm4) (%_% ymm2) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% ymm26) (%_% ymm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xb5; 0x28; 0x25; 0xd7; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm9) (%_% ymm7) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x28; 0x25; 0xd0; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm5) (%_% ymm8) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xdc;
                           (* VMOVDQA64 (%_% ymm27) (%_% ymm12) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xad; 0x28; 0x25; 0xdd; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm10) (%_% ymm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xa5; 0x28; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm11) (%_% ymm14) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xe2;
                           (* VMOVDQA64 (%_% ymm28) (%_% ymm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xfd; 0x20; 0x25; 0xe3; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm16) (%_% ymm19) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xf5; 0x20; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm17) (%_% ymm15) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xfd; 0x28; 0x6f; 0xe8;
                           (* VMOVDQA64 (%_% ymm29) (%_% ymm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xcd; 0x20; 0x25; 0xec; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm22) (%_% ymm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xc5; 0x20; 0x25; 0xed; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm23) (%_% ymm21) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x9d; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x28; 0x72; 0xcb; 0x24;
                           (* VPROLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x28; 0x72; 0xc9; 0x03;
                           (* VPROLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x28; 0x72; 0xcc; 0x29;
                           (* VPROLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x28; 0x72; 0xca; 0x12;
                           (* VPROLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x28; 0x72; 0xce; 0x01;
                           (* VPROLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x28; 0x72; 0xc9; 0x2c;
                           (* VPROLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x28; 0x72; 0xcf; 0x0a;
                           (* VPROLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x28; 0x72; 0xcd; 0x2d;
                           (* VPROLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x28; 0x72; 0xc8; 0x02;
                           (* VPROLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x28; 0x72; 0xcc; 0x3e;
                           (* VPROLQ (%_% ymm12) (%_% ymm12) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x28; 0x72; 0xca; 0x06;
                           (* VPROLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x28; 0x72; 0xcd; 0x2b;
                           (* VPROLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x28; 0x72; 0xcb; 0x0f;
                           (* VPROLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x28; 0x72; 0xce; 0x3d;
                           (* VPROLQ (%_% ymm14) (%_% ymm14) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x20; 0x72; 0xca; 0x1c;
                           (* VPROLQ (%_% ymm18) (%_% ymm18) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x20; 0x72; 0xc8; 0x37;
                           (* VPROLQ (%_% ymm16) (%_% ymm16) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x20; 0x72; 0xcb; 0x19;
                           (* VPROLQ (%_% ymm19) (%_% ymm19) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x20; 0x72; 0xc9; 0x15;
                           (* VPROLQ (%_% ymm17) (%_% ymm17) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x28; 0x72; 0xcf; 0x38;
                           (* VPROLQ (%_% ymm15) (%_% ymm15) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x20; 0x72; 0xc8; 0x1b;
                           (* VPROLQ (%_% ymm24) (%_% ymm24) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x20; 0x72; 0xce; 0x14;
                           (* VPROLQ (%_% ymm22) (%_% ymm22) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x20; 0x72; 0xcc; 0x27;
                           (* VPROLQ (%_% ymm20) (%_% ymm20) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x20; 0x72; 0xcf; 0x08;
                           (* VPROLQ (%_% ymm23) (%_% ymm23) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x20; 0x72; 0xcd; 0x0e;
                           (* VPROLQ (%_% ymm21) (%_% ymm21) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xb5; 0x28; 0x25; 0xc5; 0xd2;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm9) (%_% ymm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x38; 0xef; 0x46; 0x01;
                           (* VPXORQ (%_% ymm0) (%_% ymm0) (Memop Quadword (%% (rsi,8)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0x33; 0x95; 0x28; 0x25; 0xc9; 0xd2;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm13) (%_% ymm17) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x20; 0x25; 0xed; 0xd2;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm17) (%_% ymm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xd5; 0x20; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm21) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xcd; 0x20; 0x25; 0xd1; 0xd2;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm22) (%_% ymm1) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xf5; 0x28; 0x25; 0xf5; 0xd2;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm1) (%_% ymm5) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xd5; 0x28; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm5) (%_% ymm14) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x28; 0x25; 0xee; 0xd2;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm14) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x20; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf6;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xfa;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm10) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xad; 0x28; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm10) (%_% ymm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xe5; 0x20; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm19) (%_% ymm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xc5; 0x20; 0x25; 0xda; 0xd2;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm23) (%_% ymm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xed; 0x28; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm2) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x20; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfb;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xe5; 0x28; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm3) (%_% ymm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xc5; 0x28; 0x25; 0xdb; 0xd2;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm7) (%_% ymm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xa5; 0x28; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm11) (%_% ymm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x85; 0x28; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm15) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x20; 0x25; 0xff; 0xd2;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm12) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xf8;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm16) (Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xfd; 0x20; 0x25; 0xe4; 0xd2;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm16) (%_% ymm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xdd; 0x20; 0x25; 0xc4; 0xd2;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm20) (%_% ymm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xdd; 0x28; 0x25; 0xe0; 0xd2;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm4) (%_% ymm8) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xbd; 0x28; 0x25; 0xe6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm8) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x20; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% ymm25) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xed; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm18) (%_% ymm6) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xbd; 0x20; 0x25; 0xcc; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm24) (%_% ymm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xd1;
                           (* VMOVDQA64 (%_% ymm26) (%_% ymm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xcd; 0x20; 0x25; 0xd2; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm22) (%_% ymm10) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xe5; 0x28; 0x25; 0xd0; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm3) (%_% ymm16) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xdd;
                           (* VMOVDQA64 (%_% ymm27) (%_% ymm13) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xf5; 0x28; 0x25; 0xdb; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm1) (%_% ymm19) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xc5; 0x28; 0x25; 0xdc; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm7) (%_% ymm20) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xe1;
                           (* VMOVDQA64 (%_% ymm28) (%_% ymm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xd5; 0x28; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm5) (%_% ymm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xa5; 0x28; 0x25; 0xe4; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm11) (%_% ymm4) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xed;
                           (* VMOVDQA64 (%_% ymm29) (%_% ymm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0x8d; 0x28; 0x25; 0xea; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm14) (%_% ymm2) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0x85; 0x28; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm15) (%_% ymm8) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x95; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xa5; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x20; 0x72; 0xca; 0x24;
                           (* VPROLQ (%_% ymm18) (%_% ymm18) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x28; 0x72; 0xce; 0x03;
                           (* VPROLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x20; 0x72; 0xc8; 0x29;
                           (* VPROLQ (%_% ymm24) (%_% ymm24) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x28; 0x72; 0xcc; 0x12;
                           (* VPROLQ (%_% ymm12) (%_% ymm12) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x28; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x20; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% ymm22) (%_% ymm22) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x28; 0x72; 0xca; 0x0a;
                           (* VPROLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x28; 0x72; 0xcb; 0x2d;
                           (* VPROLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x20; 0x72; 0xc8; 0x02;
                           (* VPROLQ (%_% ymm16) (%_% ymm16) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x28; 0x72; 0xcd; 0x3e;
                           (* VPROLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x28; 0x72; 0xc9; 0x06;
                           (* VPROLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x20; 0x72; 0xcb; 0x2b;
                           (* VPROLQ (%_% ymm19) (%_% ymm19) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x28; 0x72; 0xcf; 0x0f;
                           (* VPROLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x20; 0x72; 0xcc; 0x3d;
                           (* VPROLQ (%_% ymm20) (%_% ymm20) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x20; 0x72; 0xc9; 0x1c;
                           (* VPROLQ (%_% ymm17) (%_% ymm17) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x28; 0x72; 0xcd; 0x37;
                           (* VPROLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x20; 0x72; 0xcf; 0x19;
                           (* VPROLQ (%_% ymm23) (%_% ymm23) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x28; 0x72; 0xcb; 0x15;
                           (* VPROLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x28; 0x72; 0xcc; 0x38;
                           (* VPROLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x20; 0x72; 0xcd; 0x1b;
                           (* VPROLQ (%_% ymm21) (%_% ymm21) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x28; 0x72; 0xce; 0x14;
                           (* VPROLQ (%_% ymm14) (%_% ymm14) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x28; 0x72; 0xca; 0x27;
                           (* VPROLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x28; 0x72; 0xcf; 0x08;
                           (* VPROLQ (%_% ymm15) (%_% ymm15) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x28; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xcd; 0x20; 0x25; 0xc3; 0xd2;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm22) (%_% ymm19) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x38; 0xef; 0x46; 0x02;
                           (* VPXORQ (%_% ymm0) (%_% ymm0) (Memop Quadword (%% (rsi,16)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0xc3; 0xe5; 0x20; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm19) (%_% ymm11) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xa5; 0x28; 0x25; 0xd8; 0xd2;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm11) (%_% ymm8) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xbd; 0x28; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm8) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x20; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm14) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0x8d; 0x28; 0x25; 0xce; 0xd2;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm14) (%_% ymm6) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xcd; 0x28; 0x25; 0xf3; 0xd2;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm6) (%_% ymm3) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xe5; 0x28; 0x25; 0xf4; 0xd2;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm3) (%_% ymm20) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xdd; 0x20; 0x25; 0xde; 0xd2;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm20) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm9) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm1) (Evex_deco Unmasked No_brc) *)
  0x62; 0x33; 0xf5; 0x28; 0x25; 0xcf; 0xd2;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm1) (%_% ymm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xd3; 0xc5; 0x20; 0x25; 0xcf; 0xd2;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm23) (%_% ymm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0x85; 0x28; 0x25; 0xfc; 0xd2;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm15) (%_% ymm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x28; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm12) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x20; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xf5;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xfa;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xed; 0x20; 0x25; 0xea; 0xd2;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm18) (%_% ymm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xe3; 0xad; 0x28; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm10) (%_% ymm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xc5; 0x28; 0x25; 0xd4; 0xd2;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm7) (%_% ymm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xdd; 0x28; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm4) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x20; 0x25; 0xe7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf5;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm13) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm5) (Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xd5; 0x28; 0x25; 0xea; 0xd2;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm5) (%_% ymm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xed; 0x28; 0x25; 0xe8; 0xd2;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm2) (%_% ymm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0xbd; 0x20; 0x25; 0xd0; 0xd2;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm24) (%_% ymm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xfd; 0x20; 0x25; 0xc6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm16) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xc8;
                           (* VMOVDQA64 (%_% ymm25) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xf5; 0x20; 0x25; 0xc9; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm17) (%_% ymm9) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xd5; 0x20; 0x25; 0xcd; 0x96;
                           (* VPTERNLOGQ (%_% ymm25) (%_% ymm21) (%_% ymm13) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% ymm26) (%_% ymm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0x8d; 0x28; 0x25; 0xd1; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm14) (%_% ymm1) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xed; 0x20; 0x25; 0xd5; 0x96;
                           (* VPTERNLOGQ (%_% ymm26) (%_% ymm18) (%_% ymm5) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xdb;
                           (* VMOVDQA64 (%_% ymm27) (%_% ymm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xcd; 0x28; 0x25; 0xdf; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm6) (%_% ymm23) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x63; 0xad; 0x28; 0x25; 0xda; 0x96;
                           (* VPTERNLOGQ (%_% ymm27) (%_% ymm10) (%_% ymm2) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% ymm28) (%_% ymm11) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xe5; 0x28; 0x25; 0xe7; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm3) (%_% ymm15) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xc5; 0x28; 0x25; 0xe0; 0x96;
                           (* VPTERNLOGQ (%_% ymm28) (%_% ymm7) (%_% ymm24) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xe8;
                           (* VMOVDQA64 (%_% ymm29) (%_% ymm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x43; 0xdd; 0x20; 0x25; 0xec; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm20) (%_% ymm12) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x23; 0xdd; 0x28; 0x25; 0xe8; 0x96;
                           (* VPTERNLOGQ (%_% ymm29) (%_% ymm4) (%_% ymm16) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xca; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm26) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x95; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x95; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm29) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcb; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm27) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xb5; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xce; 0x96;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xb5; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xb5; 0x20; 0x25; 0xee; 0x96;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm25) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcc; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm28) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xf6; 0x96;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xad; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xad; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x20; 0x25; 0xd6; 0x96;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm26) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xcd; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm29) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x20; 0x25; 0xde; 0x96;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xa5; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xa5; 0x20; 0x25; 0xfe; 0x96;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0xa5; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm27) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0x8d; 0x20; 0x72; 0xc9; 0x01;
                           (* VPROLQ (%_% ymm30) (%_% ymm25) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x9d; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x9d; 0x20; 0x25; 0xe6; 0x96;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x9d; 0x20; 0x25; 0xc6; 0x96;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm28) (%_% ymm30) (Imm8 (word 150))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xf5; 0x20; 0x72; 0xc9; 0x24;
                           (* VPROLQ (%_% ymm17) (%_% ymm17) (Imm8 (word 36)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xb5; 0x28; 0x72; 0xc9; 0x03;
                           (* VPROLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 3)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xd5; 0x20; 0x72; 0xcd; 0x29;
                           (* VPROLQ (%_% ymm21) (%_% ymm21) (Imm8 (word 41)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x95; 0x28; 0x72; 0xcd; 0x12;
                           (* VPROLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 18)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xcd; 0x20; 0x72; 0xce; 0x01;
                           (* VPROLQ (%_% ymm22) (%_% ymm22) (Imm8 (word 1)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x8d; 0x28; 0x72; 0xce; 0x2c;
                           (* VPROLQ (%_% ymm14) (%_% ymm14) (Imm8 (word 44)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xf5; 0x28; 0x72; 0xc9; 0x0a;
                           (* VPROLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 10)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xed; 0x20; 0x72; 0xca; 0x2d;
                           (* VPROLQ (%_% ymm18) (%_% ymm18) (Imm8 (word 45)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xd5; 0x28; 0x72; 0xcd; 0x02;
                           (* VPROLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 2)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xe5; 0x20; 0x72; 0xcb; 0x3e;
                           (* VPROLQ (%_% ymm19) (%_% ymm19) (Imm8 (word 62)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xcd; 0x28; 0x72; 0xce; 0x06;
                           (* VPROLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 6)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xc5; 0x20; 0x72; 0xcf; 0x2b;
                           (* VPROLQ (%_% ymm23) (%_% ymm23) (Imm8 (word 43)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xad; 0x28; 0x72; 0xca; 0x0f;
                           (* VPROLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 15)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xed; 0x28; 0x72; 0xca; 0x3d;
                           (* VPROLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 61)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xa5; 0x28; 0x72; 0xcb; 0x1c;
                           (* VPROLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 28)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xe5; 0x28; 0x72; 0xcb; 0x37;
                           (* VPROLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 55)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x85; 0x28; 0x72; 0xcf; 0x19;
                           (* VPROLQ (%_% ymm15) (%_% ymm15) (Imm8 (word 25)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xc5; 0x28; 0x72; 0xcf; 0x15;
                           (* VPROLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 21)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x91; 0xbd; 0x20; 0x72; 0xc8; 0x38;
                           (* VPROLQ (%_% ymm24) (%_% ymm24) (Imm8 (word 56)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0xbd; 0x28; 0x72; 0xc8; 0x1b;
                           (* VPROLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 27)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xdd; 0x20; 0x72; 0xcc; 0x14;
                           (* VPROLQ (%_% ymm20) (%_% ymm20) (Imm8 (word 20)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xd1; 0x9d; 0x28; 0x72; 0xcc; 0x27;
                           (* VPROLQ (%_% ymm12) (%_% ymm12) (Imm8 (word 39)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xdd; 0x28; 0x72; 0xcc; 0x08;
                           (* VPROLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 8)) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x20; 0x72; 0xc8; 0x0e;
                           (* VPROLQ (%_% ymm16) (%_% ymm16) (Imm8 (word 14)) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm0) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm14) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0x8d; 0x28; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm0) (%_% ymm14) (%_% ymm23) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf1; 0xfd; 0x38; 0xef; 0x46; 0x03;
                           (* VPXORQ (%_% ymm0) (%_% ymm0) (Memop Quadword (%% (rsi,24)))
(Evex_deco Unmasked Broadcast) *)
  0x62; 0x73; 0xc5; 0x20; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm14) (%_% ymm23) (%_% ymm7) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xa3; 0xc5; 0x28; 0x25; 0xf8; 0xd2;
                           (* VPTERNLOGQ (%_% ymm23) (%_% ymm7) (%_% ymm16) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xfd; 0x20; 0x25; 0xfe; 0xd2;
                           (* VPTERNLOGQ (%_% ymm7) (%_% ymm16) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0x8d; 0x20; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm16) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm11) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xfc;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm20) (Evex_deco Unmasked No_brc) *)
  0x62; 0x53; 0xdd; 0x20; 0x25; 0xd9; 0xd2;
                           (* VPTERNLOGQ (%_% ymm11) (%_% ymm20) (%_% ymm9) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xa3; 0xb5; 0x28; 0x25; 0xe2; 0xd2;
                           (* VPTERNLOGQ (%_% ymm20) (%_% ymm9) (%_% ymm18) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xed; 0x20; 0x25; 0xca; 0xd2;
                           (* VPTERNLOGQ (%_% ymm9) (%_% ymm18) (%_% ymm2) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xed; 0x28; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm18) (%_% ymm2) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x20; 0x25; 0xd7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm2) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xf6;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm6) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xcd; 0x28; 0x25; 0xf7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm22) (%_% ymm6) (%_% ymm15) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xf3; 0x85; 0x28; 0x25; 0xf4; 0xd2;
                           (* VPTERNLOGQ (%_% ymm6) (%_% ymm15) (%_% ymm4) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x53; 0xdd; 0x28; 0x25; 0xfd; 0xd2;
                           (* VPTERNLOGQ (%_% ymm15) (%_% ymm4) (%_% ymm13) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x95; 0x28; 0x25; 0xe6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm4) (%_% ymm13) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0x8d; 0x20; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% ymm13) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xf9;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xf5; 0x20; 0x25; 0xc1; 0xd2;
                           (* VPTERNLOGQ (%_% ymm8) (%_% ymm17) (%_% ymm1) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xf5; 0x28; 0x25; 0xca; 0xd2;
                           (* VPTERNLOGQ (%_% ymm17) (%_% ymm1) (%_% ymm10) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0xad; 0x28; 0x25; 0xc8; 0xd2;
                           (* VPTERNLOGQ (%_% ymm1) (%_% ymm10) (%_% ymm24) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x13; 0xbd; 0x20; 0x25; 0xd6; 0xd2;
                           (* VPTERNLOGQ (%_% ymm10) (%_% ymm24) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x03; 0x8d; 0x20; 0x25; 0xc7; 0xd2;
                           (* VPTERNLOGQ (%_% ymm24) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x28; 0x6f; 0xf3;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xfb;
                           (* VMOVDQA64 (%_% ymm31) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc3; 0xe5; 0x28; 0x25; 0xdc; 0xd2;
                           (* VPTERNLOGQ (%_% ymm19) (%_% ymm3) (%_% ymm12) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0xb3; 0x9d; 0x28; 0x25; 0xdd; 0xd2;
                           (* VPTERNLOGQ (%_% ymm3) (%_% ymm12) (%_% ymm21) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x73; 0xd5; 0x20; 0x25; 0xe5; 0xd2;
                           (* VPTERNLOGQ (%_% ymm12) (%_% ymm21) (%_% ymm5) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x83; 0xd5; 0x28; 0x25; 0xee; 0xd2;
                           (* VPTERNLOGQ (%_% ymm21) (%_% ymm5) (%_% ymm30) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x93; 0x8d; 0x20; 0x25; 0xef; 0xd2;
                           (* VPTERNLOGQ (%_% ymm5) (%_% ymm30) (%_% ymm31) (Imm8 (word 210))
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf1;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm1) (Evex_deco Unmasked No_brc) *)
  0xc5; 0x7d; 0x7f; 0xf1;  (* VMOVDQA (%_% ymm1) (%_% ymm14) *)
  0xc4; 0x41; 0x7d; 0x6f; 0xf5;
                           (* VMOVDQA (%_% ymm14) (%_% ymm13) *)
  0xc5; 0x7d; 0x6f; 0xec;  (* VMOVDQA (%_% ymm13) (%_% ymm4) *)
  0x62; 0xb1; 0xfd; 0x28; 0x6f; 0xe0;
                           (* VMOVDQA64 (%_% ymm4) (%_% ymm16) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x28; 0x6f; 0xc1;
                           (* VMOVDQA64 (%_% ymm16) (%_% ymm17) (Evex_deco Unmasked No_brc) *)
  0x62; 0x81; 0xfd; 0x28; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% ymm17) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf2;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm2) (Evex_deco Unmasked No_brc) *)
  0x62; 0xb1; 0xfd; 0x28; 0x6f; 0xd7;
                           (* VMOVDQA64 (%_% ymm2) (%_% ymm23) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x28; 0x6f; 0xfd;
                           (* VMOVDQA64 (%_% ymm23) (%_% ymm21) (Evex_deco Unmasked No_brc) *)
  0x62; 0xe1; 0xfd; 0x28; 0x6f; 0xeb;
                           (* VMOVDQA64 (%_% ymm21) (%_% ymm3) (Evex_deco Unmasked No_brc) *)
  0xc5; 0xfd; 0x6f; 0xdf;  (* VMOVDQA (%_% ymm3) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0xcf;  (* VMOVDQA (%_% ymm7) (%_% ymm9) *)
  0x62; 0x11; 0xfd; 0x28; 0x6f; 0xce;
                           (* VMOVDQA64 (%_% ymm9) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x28; 0x6f; 0xf5;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm5) (Evex_deco Unmasked No_brc) *)
  0xc5; 0x7d; 0x7f; 0xdd;  (* VMOVDQA (%_% ymm5) (%_% ymm11) *)
  0xc5; 0x7d; 0x6f; 0xde;  (* VMOVDQA (%_% ymm11) (%_% ymm6) *)
  0x62; 0xb1; 0xfd; 0x28; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% ymm6) (%_% ymm20) (Evex_deco Unmasked No_brc) *)
  0x62; 0xa1; 0xfd; 0x28; 0x6f; 0xe3;
                           (* VMOVDQA64 (%_% ymm20) (%_% ymm19) (Evex_deco Unmasked No_brc) *)
  0x62; 0x81; 0xfd; 0x28; 0x6f; 0xd8;
                           (* VMOVDQA64 (%_% ymm19) (%_% ymm24) (Evex_deco Unmasked No_brc) *)
  0x62; 0x01; 0xfd; 0x28; 0x6f; 0xc6;
                           (* VMOVDQA64 (%_% ymm24) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xfd; 0x28; 0x6f; 0xf0;
                           (* VMOVDQA64 (%_% ymm30) (%_% ymm8) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x28; 0x6f; 0xc2;
                           (* VMOVDQA64 (%_% ymm8) (%_% ymm18) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x28; 0x6f; 0xd2;
                           (* VMOVDQA64 (%_% ymm18) (%_% ymm10) (Evex_deco Unmasked No_brc) *)
  0x62; 0x31; 0xfd; 0x28; 0x6f; 0xd6;
                           (* VMOVDQA64 (%_% ymm10) (%_% ymm22) (Evex_deco Unmasked No_brc) *)
  0x62; 0xc1; 0xfd; 0x28; 0x6f; 0xf4;
                           (* VMOVDQA64 (%_% ymm22) (%_% ymm12) (Evex_deco Unmasked No_brc) *)
  0xc4; 0x41; 0x7d; 0x6f; 0xe7;
                           (* VMOVDQA (%_% ymm12) (%_% ymm15) *)
  0x62; 0x11; 0xfd; 0x28; 0x6f; 0xfe;
                           (* VMOVDQA64 (%_% ymm15) (%_% ymm30) (Evex_deco Unmasked No_brc) *)
  0x48; 0x83; 0xc6; 0x20;  (* ADD (% rsi) (Imm8 (word 32)) *)
  0x48; 0x39; 0xc6;        (* CMP (% rsi) (% rax) *)
  0x0f; 0x85; 0x1a; 0xf4; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294964250)) *)
  0x62; 0x61; 0xfd; 0x28; 0x6c; 0xc9;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm0) (%_% ymm1) *)
  0x62; 0x61; 0xfd; 0x28; 0x6d; 0xd1;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm0) (%_% ymm1) *)
  0x62; 0x61; 0xed; 0x28; 0x6c; 0xdb;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm2) (%_% ymm3) *)
  0x62; 0x61; 0xed; 0x28; 0x6d; 0xe3;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm2) (%_% ymm3) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xeb; 0x00;
                           (* VSHUFI64X2 (%_% ymm29) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xf4; 0x00;
                           (* VSHUFI64X2 (%_% ymm30) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xfb; 0x03;
                           (* VSHUFI64X2 (%_% ymm31) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xcc; 0x03;
                           (* VSHUFI64X2 (%_% ymm25) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x2f;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,0))) (%_% ymm29)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xb7; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,200))) (%_% ymm30)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xbf; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,400))) (%_% ymm31)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x8f; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,600))) (%_% ymm25)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xdd; 0x28; 0x6c; 0xcd;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm4) (%_% ymm5) *)
  0x62; 0x61; 0xdd; 0x28; 0x6d; 0xd5;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm4) (%_% ymm5) *)
  0x62; 0x61; 0xcd; 0x28; 0x6c; 0xdf;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm6) (%_% ymm7) *)
  0x62; 0x61; 0xcd; 0x28; 0x6d; 0xe7;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm6) (%_% ymm7) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xeb; 0x00;
                           (* VSHUFI64X2 (%_% ymm29) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xf4; 0x00;
                           (* VSHUFI64X2 (%_% ymm30) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xfb; 0x03;
                           (* VSHUFI64X2 (%_% ymm31) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xcc; 0x03;
                           (* VSHUFI64X2 (%_% ymm25) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x6f; 0x01;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,32))) (%_% ymm29)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xb7; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,232))) (%_% ymm30)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xbf; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,432))) (%_% ymm31)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x8f; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,632))) (%_% ymm25)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0xbd; 0x28; 0x6c; 0xc9;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm8) (%_% ymm9) *)
  0x62; 0x41; 0xbd; 0x28; 0x6d; 0xd1;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm8) (%_% ymm9) *)
  0x62; 0x41; 0xad; 0x28; 0x6c; 0xdb;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm10) (%_% ymm11) *)
  0x62; 0x41; 0xad; 0x28; 0x6d; 0xe3;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm10) (%_% ymm11) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xeb; 0x00;
                           (* VSHUFI64X2 (%_% ymm29) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xf4; 0x00;
                           (* VSHUFI64X2 (%_% ymm30) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xfb; 0x03;
                           (* VSHUFI64X2 (%_% ymm31) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xcc; 0x03;
                           (* VSHUFI64X2 (%_% ymm25) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x6f; 0x02;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,64))) (%_% ymm29)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xb7; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,264))) (%_% ymm30)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xbf; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,464))) (%_% ymm31)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x8f; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,664))) (%_% ymm25)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x41; 0x9d; 0x28; 0x6c; 0xcd;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm12) (%_% ymm13) *)
  0x62; 0x41; 0x9d; 0x28; 0x6d; 0xd5;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm12) (%_% ymm13) *)
  0x62; 0x41; 0x8d; 0x28; 0x6c; 0xdf;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm14) (%_% ymm15) *)
  0x62; 0x41; 0x8d; 0x28; 0x6d; 0xe7;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm14) (%_% ymm15) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xeb; 0x00;
                           (* VSHUFI64X2 (%_% ymm29) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xf4; 0x00;
                           (* VSHUFI64X2 (%_% ymm30) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xfb; 0x03;
                           (* VSHUFI64X2 (%_% ymm31) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xcc; 0x03;
                           (* VSHUFI64X2 (%_% ymm25) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x6f; 0x03;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,96))) (%_% ymm29)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xb7; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,296))) (%_% ymm30)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xbf; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,496))) (%_% ymm31)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x8f; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,696))) (%_% ymm25)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xfd; 0x20; 0x6c; 0xc9;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm16) (%_% ymm17) *)
  0x62; 0x21; 0xfd; 0x20; 0x6d; 0xd1;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm16) (%_% ymm17) *)
  0x62; 0x21; 0xed; 0x20; 0x6c; 0xdb;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm18) (%_% ymm19) *)
  0x62; 0x21; 0xed; 0x20; 0x6d; 0xe3;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm18) (%_% ymm19) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xeb; 0x00;
                           (* VSHUFI64X2 (%_% ymm29) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xf4; 0x00;
                           (* VSHUFI64X2 (%_% ymm30) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xfb; 0x03;
                           (* VSHUFI64X2 (%_% ymm31) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xcc; 0x03;
                           (* VSHUFI64X2 (%_% ymm25) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x6f; 0x04;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,128))) (%_% ymm29)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xb7; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,328))) (%_% ymm30)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xbf; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,528))) (%_% ymm31)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x8f; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,728))) (%_% ymm25)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x21; 0xdd; 0x20; 0x6c; 0xcd;
                           (* VPUNPCKLQDQ (%_% ymm25) (%_% ymm20) (%_% ymm21) *)
  0x62; 0x21; 0xdd; 0x20; 0x6d; 0xd5;
                           (* VPUNPCKHQDQ (%_% ymm26) (%_% ymm20) (%_% ymm21) *)
  0x62; 0x21; 0xcd; 0x20; 0x6c; 0xdf;
                           (* VPUNPCKLQDQ (%_% ymm27) (%_% ymm22) (%_% ymm23) *)
  0x62; 0x21; 0xcd; 0x20; 0x6d; 0xe7;
                           (* VPUNPCKHQDQ (%_% ymm28) (%_% ymm22) (%_% ymm23) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xeb; 0x00;
                           (* VSHUFI64X2 (%_% ymm29) (%_% ymm25) (%_% ymm27) (Imm8 (word 0)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xf4; 0x00;
                           (* VSHUFI64X2 (%_% ymm30) (%_% ymm26) (%_% ymm28) (Imm8 (word 0)) *)
  0x62; 0x03; 0xb5; 0x20; 0x43; 0xfb; 0x03;
                           (* VSHUFI64X2 (%_% ymm31) (%_% ymm25) (%_% ymm27) (Imm8 (word 3)) *)
  0x62; 0x03; 0xad; 0x20; 0x43; 0xcc; 0x03;
                           (* VSHUFI64X2 (%_% ymm25) (%_% ymm26) (%_% ymm28) (Imm8 (word 3)) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x6f; 0x05;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,160))) (%_% ymm29)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xb7; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,360))) (%_% ymm30)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0xbf; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,560))) (%_% ymm31)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfe; 0x28; 0x7f; 0x8f; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU64 (Memop Word256 (%% (rdi,760))) (%_% ymm25)
(Evex_deco Unmasked No_brc) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x47; 0x18;
                           (* VMOVQ (Memop Quadword (%% (rdi,192))) (%_% xmm24) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x47; 0x31; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,392))) (%_% xmm24) (Imm8 (word 1)) *)
  0x62; 0x03; 0x7d; 0x28; 0x39; 0xc1; 0x01;
                           (* VEXTRACTI32X4 (%_% xmm25) (%_% ymm24) (Imm8 (word 1)) *)
  0x62; 0x61; 0xfd; 0x08; 0x7e; 0x4f; 0x4a;
                           (* VMOVQ (Memop Quadword (%% (rdi,592))) (%_% xmm25) *)
  0x62; 0x63; 0xfd; 0x08; 0x16; 0x4f; 0x63; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,792))) (%_% xmm25) (Imm8 (word 1)) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let keccak_f1600_x4_avx512_tmc =
  define_trimmed "keccak_f1600_x4_avx512_tmc" keccak_f1600_x4_avx512_mc;;

let KECCAK_F1600_X4_AVX512_TMC_EXEC =
  X86_MK_EXEC_RULE keccak_f1600_x4_avx512_tmc;;

(* ------------------------------------------------------------------------- *)
(* The layout of the four states in ymm0-ymm24: lane k of the states, A4 in  *)
(* the top quadword down to A1 in the bottom one, is in one register, the    *)
(* register of each lane given by keccak_avx512_layout0-3.                   *)
(* ------------------------------------------------------------------------- *)

let keccak4_lane = define
 `keccak4_lane (A1:int64 list) A2 A3 A4 k =
    word_join (word_join (EL k A4) (EL k A3):int128)
              (word_join (EL k A2) (EL k A1):int128):int256`;;

let keccak4_avx512_regs = define
 `keccak4_avx512_regs (l:num list) A1 A2 A3 A4 =
    MAP (keccak4_lane A1 A2 A3 A4) l`;;

(* ------------------------------------------------------------------------- *)
(* The state between rounds: the four states after n rounds in ymm0-ymm24,   *)
(* in the layout l, with the pointers and the round constants.               *)
(* ------------------------------------------------------------------------- *)

let keccak4_avx512_assertion =
  let regs =
    mk_list(map (fun k ->
      mk_comb(mk_comb(`read:(x86state,int256)component->x86state->int256`,
                      mk_const("YMM"^string_of_int k,[])),`s:x86state`))
     (0--24),`:int256`) in
  fun layout n ->
    let tm = subst [layout,`l:num list`; n,`n:num`]
     `keccak4_avx512_regs l (keccak n A1) (keccak n A2)
                            (keccak n A3) (keccak n A4)` in
    mk_abs(`s:x86state`,
      list_mk_conj
       [`read RDI s = a`; `read RSI s = word_add rc (word(32 * i))`;
        `read RAX s = word_add rc (word 192)`;
        `wordlist_from_memory(rc,24) s = round_constants`;
        mk_eq(regs,tm)]);;

(* ------------------------------------------------------------------------- *)
(* A round r = 1-4 of an iteration i, from the state after n = 4 * i + r - 1 *)
(* rounds: the lanes x<k>_<j> of the states (k = 0-24, j = 1-4) and the      *)
(* round constant rcon, read from rsi + 8 * (r - 1), the simulation with     *)
(* the lanes abbreviated, then each lane of the new state. The fourth round  *)
(* also restores the layout and increments and tests rsi.                    *)
(* ------------------------------------------------------------------------- *)

(*** The round as a tactic with parameters: init after the initial state
 *** is set up, fin on the tactic that proves the final state, and side for
 *** the conjuncts other than the lanes (the loop test after round 4)
 ***)

let KECCAK4_AVX512_ROUND_GEN_TAC =
  let lists = [1,`A1:int64 list`; 2,`A2:int64 list`;
               3,`A3:int64 list`; 4,`A4:int64 list`] in
  fun init fin side r nsteps ->
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
    MAP_EVERY (fun (j,t) ->
      MP_TAC(ISPECL [t; nin] LENGTH_KECCAK) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LENGTH_EQ_25] THEN DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY (fun k ->
        ABBREV_TAC(mk_eq(
          mk_var("x"^string_of_int k^"_"^string_of_int j,`:int64`),
          list_mk_comb(`EL:num->int64 list->int64`,
            [mk_small_numeral k; list_mk_comb(`keccak`,[nin;t])]))))
       (0--24)) lists THEN
    ABBREV_TAC(mk_eq(`rcon:int64`,
      list_mk_comb(`EL:num->int64 list->int64`,[nin;`round_constants`]))) THEN
    REWRITE_TAC[KECCAK_ROUND_EXPLICIT] THEN
    REWRITE_TAC[keccak4_avx512_regs; keccak_avx512_layout0;
                keccak_avx512_layout1; keccak_avx512_layout2;
                keccak_avx512_layout3; MAP; keccak4_lane] THEN
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
    (fun gl -> keccak_avx2_lanes := 0; ALL_TAC gl) THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC KECCAK_F1600_X4_AVX512_TMC_EXEC [n] THEN
      KECCAK_AVX512_SIMPLIFY_TAC THEN KECCAK_AVX2_LANE_ABBREV_TAC n)
     (1--nsteps) THEN
    ENSURES_FINAL_STATE_TAC THEN
    fin
     (ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[round_constants; CONS_11;
        WORDLIST_FROM_MEMORY_CONV
         (subst [sn,`s:x86state`]
           `wordlist_from_memory(rc,24) s:int64 list`)] THEN
      ASM_REWRITE_TAC[] THEN
      side THEN
      REWRITE_TAC[KECCAK_AVX2_JOIN_EQ; GSYM CONJ_ASSOC] THEN
      KECCAK_AVX2_EXPAND_TAC THEN
      REPEAT CONJ_TAC THEN KECCAK_AVX512_BITBLAST_CACHED_TAC);;

let KECCAK4_AVX512_ROUND_TAC r nsteps =
  KECCAK4_AVX512_ROUND_GEN_TAC ALL_TAC I
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
(* The x4 permutation keccak_f1600_x4_avx512.                                *)
(* ------------------------------------------------------------------------- *)

let KECCAK4_AVX512_FULL_ROUND_TAC r nsteps =
  KECCAK4_AVX512_ROUND_GEN_TAC (TRY STRIP_EXISTS_ASSUM_TAC)
   EVENTS_SPLIT_TAC
   (if r = 4 then
      MP_TAC(SPECL [`rc:int64`; `i:num`] KECCAK_AVX512_ZF_BRANCH) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[th; KECCAK_AVX512_RSI; KECCAK_AVX512_WORD_COND])
    else ALL_TAC)
   r nsteps;;

let KECCAK_F1600_X4_AVX512_FULL = time prove
 (`exists f_events.
    forall e a rc A1 A2 A3 A4 pc.
        nonoverlapping (a,800) (word pc,0x1065) /\
        nonoverlapping (a,800) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx512_tmc /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [a; rc] s /\
                 wordlist_from_memory(rc,24) s = round_constants /\
                 wordlist_from_memory(a,25) s = A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s = A4 /\
                 read events s = e)
            (\s. read RIP s = word(pc + 0x1064) /\
                 wordlist_from_memory(a,25) s = keccak 24 A1 /\
                 wordlist_from_memory(word_add a (word 200),25) s =
                 keccak 24 A2 /\
                 wordlist_from_memory(word_add a (word 400),25) s =
                 keccak 24 A3 /\
                 wordlist_from_memory(word_add a (word 600),25) s =
                 keccak 24 A4 /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc /\
                      memaccess_inbounds e2 [a,800; rc,192] [a,800]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17;
              ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25;
              ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,800)])`,
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
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A1:int64 list`; `A2:int64 list`;
    `A3:int64 list`; `A4:int64 list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC
   `LENGTH(A1:int64 list) = 25 /\ LENGTH(A2:int64 list) = 25 /\
    LENGTH(A3:int64 list) = 25 /\ LENGTH(A4:int64 list) = 25` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x241` `pc + 0xe27`
   `\i s. read RDI s = a /\
           read RSI s = word_add rc (word(32 * i)) /\
           read RAX s = word_add rc (word 192) /\
           wordlist_from_memory(rc,24) s = round_constants /\
           [read YMM0 s; read YMM1 s; read YMM2 s; read YMM3 s; read YMM4 s;
            read YMM5 s; read YMM6 s; read YMM7 s; read YMM8 s; read YMM9 s;
            read YMM10 s; read YMM11 s; read YMM12 s; read YMM13 s;
            read YMM14 s; read YMM15 s; read YMM16 s; read YMM17 s;
            read YMM18 s; read YMM19 s; read YMM20 s; read YMM21 s;
            read YMM22 s; read YMM23 s; read YMM24 s] =
           keccak4_avx512_regs keccak_avx512_layout0
            (keccak (4 * i) A1) (keccak (4 * i) A2)
            (keccak (4 * i) A3) (keccak (4 * i) A4)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 200),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 400),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 600),25) s:int64 list`] THEN
    MAP_EVERY (fun t ->
      MP_TAC(ISPEC t LENGTH_EQ_25) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]))
     [`A1:int64 list`; `A2:int64 list`; `A3:int64 list`; `A4:int64 list`] THEN
    REWRITE_TAC[MULT_CLAUSES; keccak; keccak4_avx512_regs;
                keccak_avx512_layout0; MAP; keccak4_lane] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; WORD_ADD_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun n ->
      let tm = if n = 0 then `read (memory :> bytes256 a) s0` else
        subst [mk_small_numeral n,`n:num`]
         `read (memory :> bytes256(word_add a (word n))) s0` in
      MP_TAC(READ_MEMORY_MERGE_CONV 2 tm) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC)
     (List.concat(map (fun g -> map (fun j -> 32 * g + 200 * j) (0--3))
                      (0--5))) THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC KECCAK_F1600_X4_AVX512_TMC_EXEC [n] THEN
      KECCAK_AVX2_SIMPLIFY_TAC) (1--78) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [ENUMERATEL_ADD1] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x510`
     (keccak4_avx512_assertion `keccak_avx512_layout1` `4 * i + 1`) THEN
    CONJ_TAC THENL [KECCAK4_AVX512_FULL_ROUND_TAC 1 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x7e0`
     (keccak4_avx512_assertion `keccak_avx512_layout2` `4 * i + 2`) THEN
    CONJ_TAC THENL [KECCAK4_AVX512_FULL_ROUND_TAC 2 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xab0`
     (keccak4_avx512_assertion `keccak_avx512_layout3` `4 * i + 3`) THEN
    CONJ_TAC THENL [KECCAK4_AVX512_FULL_ROUND_TAC 3 105; ALL_TAC] THEN
    KECCAK4_AVX512_FULL_ROUND_TAC 4 136;


    CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY (fun (j,t) ->
      MP_TAC(ISPECL [t; `24`] LENGTH_KECCAK) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LENGTH_EQ_25] THEN DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY (fun k ->
        ABBREV_TAC(mk_eq(
          mk_var("z"^string_of_int k^"_"^string_of_int j,`:int64`),
          list_mk_comb(`EL:num->int64 list->int64`,
            [mk_small_numeral k; list_mk_comb(`keccak`,[`24`;t])]))))
       (0--24))
     [1,`A1:int64 list`; 2,`A2:int64 list`;
      3,`A3:int64 list`; 4,`A4:int64 list`] THEN
    REWRITE_TAC[keccak4_avx512_regs; keccak_avx512_layout0; MAP;
                keccak4_lane] THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 200),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 400),25) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(word_add a (word 600),25) s:int64 list`] THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC KECCAK_F1600_X4_AVX512_TMC_EXEC [n] THEN
      KECCAK_AVX2_SIMPLIFY_TAC) (1--78) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read (memory :> bytes256 a) s = x`) o
             concl))) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST)]);;

(*** The subroutine forms, without and with the IBT landing pad ***)

let KECCAK_F1600_X4_AVX512_CORRECT = prove
 (`!a rc A1 A2 A3 A4 pc.
      nonoverlapping (a,800) (word pc,0x1065) /\
      nonoverlapping (a,800) (rc,192)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx512_tmc /\
                read RIP s = word pc /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A1 /\
                wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                wordlist_from_memory(word_add a (word 600),25) s = A4)
           (\s. read RIP s = word(pc + 0x1064) /\
                wordlist_from_memory(a,25) s = keccak 24 A1 /\
                wordlist_from_memory(word_add a (word 200),25) s =
                keccak 24 A2 /\
                wordlist_from_memory(word_add a (word 400),25) s =
                keccak 24 A3 /\
                wordlist_from_memory(word_add a (word 600),25) s =
                keccak 24 A4)
           (MAYCHANGE [RIP; RAX; RSI] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                       ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                       ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21;
                       ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28;
                       ZMM29; ZMM30; ZMM31] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,800)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_TAC `f:int64->int64->num->(uarch_event)list`
   KECCAK_F1600_X4_AVX512_FULL THEN
  MATCH_MP_TAC(ISPEC `read events:x86state->(uarch_event)list`
                ENSURES_ANY_INITIAL) THEN
  X_GEN_TAC `e:(uarch_event)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `A1:int64 list`;
    `A2:int64 list`; `A3:int64 list`; `A4:int64 list`; `pc:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_MONO_ALL) THEN
  SIMP_TAC[]);;

let KECCAK_F1600_X4_AVX512_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a rc A1 A2 A3 A4 pc stackpointer returnaddress.
      nonoverlapping (a,800) (word pc,0x1065) /\
      nonoverlapping (a,800) (rc,192) /\
      nonoverlapping (a,800) (stackpointer,8)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx512_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A1 /\
                wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                wordlist_from_memory(word_add a (word 600),25) s = A4)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                wordlist_from_memory(a,25) s = keccak 24 A1 /\
                wordlist_from_memory(word_add a (word 200),25) s =
                keccak 24 A2 /\
                wordlist_from_memory(word_add a (word 400),25) s =
                keccak 24 A3 /\
                wordlist_from_memory(word_add a (word 600),25) s =
                keccak 24 A4)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,800)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC KECCAK_F1600_X4_AVX512_TMC_EXEC
   (CONV_RULE TWEAK_CONV KECCAK_F1600_X4_AVX512_CORRECT));;

let KECCAK_F1600_X4_AVX512_SUBROUTINE_CORRECT = prove
 (`!a rc A1 A2 A3 A4 pc stackpointer returnaddress.
      nonoverlapping (a,800) (word pc,0x1069) /\
      nonoverlapping (a,800) (rc,192) /\
      nonoverlapping (a,800) (stackpointer,8)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx512_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(rc,24) s = round_constants /\
                wordlist_from_memory(a,25) s = A1 /\
                wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                wordlist_from_memory(word_add a (word 600),25) s = A4)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                wordlist_from_memory(a,25) s = keccak 24 A1 /\
                wordlist_from_memory(word_add a (word 200),25) s =
                keccak 24 A2 /\
                wordlist_from_memory(word_add a (word 400),25) s =
                keccak 24 A3 /\
                wordlist_from_memory(word_add a (word 600),25) s =
                keccak 24 A4)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,800)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV
     KECCAK_F1600_X4_AVX512_NOIBT_SUBROUTINE_CORRECT)));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/consttime.ml";;
needs "mlkem_native/x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "keccak_f1600_x4_avx512" subroutine_signatures)
    KECCAK_F1600_X4_AVX512_CORRECT
    KECCAK_F1600_X4_AVX512_TMC_EXEC;;

(*** The events are those of the transposition, of each of the 6 iterations
 *** and of the transposition back
 ***)

let KECCAK_F1600_X4_AVX512_SAFE = time prove
 (`exists f_events.
    forall e a rc pc.
        nonoverlapping (a,800) (word pc,0x1065) /\
        nonoverlapping (a,800) (rc,192)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx512_tmc /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = word (pc + 0x1064) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc /\
                      memaccess_inbounds e2 [a,800; rc,192] [a,800]))
            (MAYCHANGE [RIP; RAX; RSI] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17;
              ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23; ZMM24; ZMM25;
              ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (a,800)])`,
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
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x241` `pc + 0xe27`
   `\i s. read RDI s = a /\
          read RSI s = word_add rc (word(32 * i)) /\
          read RAX s = word_add rc (word 192)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false KECCAK_F1600_X4_AVX512_TMC_EXEC
      (1--78) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    KECCAK_AVX512_SAFE_SIM_TAC KECCAK_F1600_X4_AVX512_TMC_EXEC 451 THEN
    ASM_SIMP_TAC[KECCAK_AVX512_BRANCH] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[KECCAK_AVX512_RSI]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false KECCAK_F1600_X4_AVX512_TMC_EXEC
      (1--78) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let KECCAK_F1600_X4_AVX512_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a rc pc stackpointer returnaddress.
        nonoverlapping (a,800) (word pc,0x1065) /\
        nonoverlapping (a,800) (rc,192) /\
        nonoverlapping (a,800) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx512_tmc /\
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
                      [a,800; rc,192; stackpointer,8]
                      [a,800]))
            (\s s'. true)`,
  X86_ADD_RETURN_NOSTACK_TAC KECCAK_F1600_X4_AVX512_TMC_EXEC
   KECCAK_F1600_X4_AVX512_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let KECCAK_F1600_X4_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e a rc pc stackpointer returnaddress.
        nonoverlapping (a,800) (word pc,0x1069) /\
        nonoverlapping (a,800) (rc,192) /\
        nonoverlapping (a,800) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx512_mc /\
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
                      [a,800; rc,192; stackpointer,8]
                      [a,800]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   KECCAK_F1600_X4_AVX512_NOIBT_SUBROUTINE_SAFE));;
