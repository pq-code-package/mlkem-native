(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 needs "x86/proofs/base.ml";;

 needs "common/keccak_spec.ml";;

(**** print_literal_from_elf "x86/sha3/keccak_f1600_x4_avx2.o";;
****)

let keccak_f1600_x4_avx2_mc = define_assert_from_elf
  "keccak_f1600_x4_avx2_mc" "x86_64/mlkem/keccak_f1600_x4_avx2.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x49; 0x89; 0xe3;        (* MOV (% r11) (% rsp) *)
  0x48; 0x83; 0xe4; 0xe0;  (* AND (% rsp) (Imm8 (word 224)) *)
  0x48; 0x81; 0xec; 0x00; 0x03; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 768)) *)
  0xc5; 0xfe; 0x6f; 0x07;  (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,200))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,400))) *)
  0xc5; 0xfe; 0x6f; 0xa7; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rdi,600))) *)
  0xc5; 0xfd; 0x6c; 0xd3;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xf5; 0x6c; 0xdc;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xfb; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm2) (%_% ymm3) (Imm8 (word 32)) *)
  0xc5; 0xf5; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm2) (%_% ymm3) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0xa7; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rdi,632))) *)
  0xc5; 0xfe; 0x7f; 0x5c; 0x24; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rsp,64))) (%_% ymm3) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xd9; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x3c; 0x24;
                           (* VMOVDQU (Memop Word256 (%% (rsp,0))) (%_% ymm7) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xf9; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x6f; 0x47; 0x20;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,432))) *)
  0xc5; 0xfe; 0x7f; 0x5c; 0x24; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rsp,96))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,232))) *)
  0xc5; 0xfe; 0x7f; 0x7c; 0x24; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rsp,32))) (%_% ymm7) *)
  0xc5; 0xfd; 0x6c; 0xd3;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xf5; 0x6c; 0xdc;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xfb; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm2) (%_% ymm3) (Imm8 (word 32)) *)
  0xc5; 0xf5; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm2) (%_% ymm3) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0xa7; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rdi,664))) *)
  0xc4; 0x63; 0x7d; 0x46; 0xf1; 0x31;
                           (* VPERM2I128 (%_% ymm14) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,128))) (%_% ymm7) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xf9; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x6f; 0x47; 0x40;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,464))) *)
  0xc5; 0xfe; 0x7f; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,192))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,264))) *)
  0xc4; 0x41; 0x7e; 0x6f; 0xd6;
                           (* VMOVDQU (%_% ymm10) (%_% ymm14) *)
  0xc5; 0xfe; 0x7f; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,160))) (%_% ymm7) *)
  0xc5; 0xfd; 0x6c; 0xd3;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xf5; 0x6c; 0xdc;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm1) (%_% ymm4) *)
  0xc5; 0xf5; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0x63; 0x6d; 0x46; 0xdb; 0x20;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm2) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm2) (%_% ymm3) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xf9; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x7f; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,256))) (%_% ymm3) *)
  0xc4; 0x63; 0x7d; 0x46; 0xc1; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,296))) *)
  0xc5; 0xfe; 0x6f; 0x47; 0x60;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,496))) *)
  0xc5; 0xfe; 0x7f; 0xbc; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,224))) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x6f; 0xf3;
                           (* VMOVDQU (%_% ymm14) (%_% ymm11) *)
  0xc5; 0xfe; 0x6f; 0xa7; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rdi,696))) *)
  0xc5; 0xfe; 0x6f; 0xaf; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm5) (Memop Word256 (%% (rdi,760))) *)
  0xc5; 0xfd; 0x6c; 0xd3;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xf5; 0x6c; 0xdc;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm1) (%_% ymm4) *)
  0xc5; 0xf5; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc5; 0xfe; 0x6f; 0xa7; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rdi,728))) *)
  0xc4; 0x63; 0x6d; 0x46; 0xfb; 0x20;
                           (* VPERM2I128 (%_% ymm15) (%_% ymm2) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm2) (%_% ymm3) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xf9; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc4; 0x63; 0x7d; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,320))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,328))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,528))) *)
  0xc5; 0xfe; 0x7f; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,288))) (%_% ymm7) *)
  0xc5; 0xfd; 0x6c; 0xd3;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xf5; 0x6c; 0xdc;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm1) (%_% ymm4) *)
  0xc5; 0xf5; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm1) (%_% ymm4) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xfb; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm2) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0x63; 0x6d; 0x46; 0xeb; 0x31;
                           (* VPERM2I128 (%_% ymm13) (%_% ymm2) (%_% ymm3) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xd9; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0xbc; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,352))) (%_% ymm7) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xf9; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x6f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,560))) *)
  0xc5; 0xfe; 0x7f; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,416))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,360))) *)
  0xc5; 0xf5; 0x6c; 0xe5;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm1) (%_% ymm5) *)
  0xc5; 0xf5; 0x6d; 0xcd;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm1) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xbc; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,384))) (%_% ymm7) *)
  0xc5; 0xfd; 0x6c; 0xd3;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x63; 0x6d; 0x46; 0xe4; 0x20;
                           (* VPERM2I128 (%_% ymm12) (%_% ymm2) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xd9; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xfc; 0x31;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm2) (%_% ymm4) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xe1; 0x31;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfa; 0x7e; 0x87; 0x50; 0x02; 0x00; 0x00;
                           (* VMOVQ (%_% xmm0) (Memop Quadword (%% (rdi,592))) *)
  0xc5; 0xfa; 0x7e; 0x8f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm1) (Memop Quadword (%% (rdi,192))) *)
  0xc5; 0x7e; 0x7f; 0xa4; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,448))) (%_% ymm12) *)
  0xc5; 0xfe; 0x7f; 0xa4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,480))) (%_% ymm4) *)
  0xc4; 0xe3; 0xf9; 0x22; 0x87; 0x18; 0x03; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm0) (%_% xmm0) (Memop Quadword (%% (rdi,792))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0xf1; 0x22; 0x8f; 0x88; 0x01; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm1) (%_% xmm1) (Memop Quadword (%% (rdi,392))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x75; 0x38; 0xd0; 0x01;
                           (* VINSERTI128 (%_% ymm2) (%_% ymm1) (%_% xmm0) (Imm8 (word 1)) *)
  0x49; 0xc7; 0xc2; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm32 (word 0)) *)
  0xc5; 0xfe; 0x6f; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,160))) *)
  0xc5; 0xb5; 0xef; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm0) (%_% ymm9) (Memop Word256 (%% (rsp,448))) *)
  0xc5; 0x7e; 0x7f; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,512))) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x6f; 0xca;
                           (* VMOVDQU (%_% ymm9) (%_% ymm10) *)
  0xc5; 0x7e; 0x6f; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm11) (Memop Word256 (%% (rsp,192))) *)
  0xc5; 0x7e; 0x6f; 0xa4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm12) (Memop Word256 (%% (rsp,352))) *)
  0xc5; 0xfe; 0x7f; 0x9c; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,576))) (%_% ymm3) *)
  0xc5; 0xdd; 0xef; 0x8c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm1) (%_% ymm4) (Memop Word256 (%% (rsp,256))) *)
  0xc5; 0x7e; 0x6f; 0x54; 0x24; 0x40;
                           (* VMOVDQU (%_% ymm10) (Memop Word256 (%% (rsp,64))) *)
  0xc5; 0xfe; 0x7f; 0xa4; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,544))) (%_% ymm4) *)
  0xc5; 0x1d; 0xef; 0xe3;  (* VPXOR (%_% ymm12) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x74; 0x24; 0x20;
                           (* VMOVDQU (%_% ymm6) (Memop Word256 (%% (rsp,32))) *)
  0xc5; 0xfe; 0x6f; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,320))) *)
  0xc5; 0x7e; 0x7f; 0xb4; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,672))) (%_% ymm14) *)
  0xc5; 0xfd; 0xef; 0xc1;  (* VPXOR (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xc1; 0x25; 0xef; 0xc8;
                           (* VPXOR (%_% ymm1) (%_% ymm11) (%_% ymm8) *)
  0xc5; 0x45; 0xef; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm11) (%_% ymm7) (Memop Word256 (%% (rsp,384))) *)
  0xc5; 0x7e; 0x7f; 0x94; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,640))) (%_% ymm10) *)
  0xc5; 0x1d; 0xef; 0xe1;  (* VPXOR (%_% ymm12) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xc1; 0x35; 0xef; 0xcf;
                           (* VPXOR (%_% ymm1) (%_% ymm9) (%_% ymm15) *)
  0xc5; 0xfe; 0x6f; 0x9c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rsp,224))) *)
  0xc5; 0x7e; 0x7f; 0x84; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,608))) (%_% ymm8) *)
  0xc5; 0x25; 0xef; 0xd9;  (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm1) *)
  0xc5; 0x8d; 0xef; 0x8c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm1) (%_% ymm14) (Memop Word256 (%% (rsp,288))) *)
  0xc5; 0x1d; 0xef; 0xe6;  (* VPXOR (%_% ymm12) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0x7e; 0x6f; 0x44; 0x24; 0x60;
                           (* VMOVDQU (%_% ymm8) (Memop Word256 (%% (rsp,96))) *)
  0xc4; 0x41; 0x25; 0xef; 0xda;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm10) *)
  0xc5; 0x15; 0xef; 0x94; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm10) (%_% ymm13) (Memop Word256 (%% (rsp,480))) *)
  0xc5; 0xe5; 0xef; 0xdc;  (* VPXOR (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xfe; 0x7f; 0xa4; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,704))) (%_% ymm4) *)
  0xc4; 0xc1; 0x5d; 0x73; 0xd4; 0x3f;
                           (* VPSRLQ (%_% ymm4) (%_% ymm12) (Imm8 (word 63)) *)
  0xc4; 0xc1; 0x55; 0x73; 0xd3; 0x3f;
                           (* VPSRLQ (%_% ymm5) (%_% ymm11) (Imm8 (word 63)) *)
  0xc5; 0xfd; 0xef; 0x04; 0x24;
                           (* VPXOR (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rsp,0))) *)
  0xc5; 0x2d; 0xef; 0xd1;  (* VPXOR (%_% ymm10) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0xfe; 0x6f; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rsp,128))) *)
  0xc4; 0x41; 0x2d; 0xef; 0xd0;
                           (* VPXOR (%_% ymm10) (%_% ymm10) (%_% ymm8) *)
  0xc5; 0x7e; 0x6f; 0xf1;  (* VMOVDQU (%_% ymm14) (%_% ymm1) *)
  0xc5; 0xed; 0xef; 0x8c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm1) (%_% ymm2) (Memop Word256 (%% (rsp,416))) *)
  0xc5; 0x7e; 0x7f; 0xb4; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,736))) (%_% ymm14) *)
  0xc5; 0xf5; 0xef; 0xcb;  (* VPXOR (%_% ymm1) (%_% ymm1) (%_% ymm3) *)
  0xc4; 0xc1; 0x65; 0x73; 0xf4; 0x01;
                           (* VPSLLQ (%_% ymm3) (%_% ymm12) (Imm8 (word 1)) *)
  0xc5; 0xe5; 0xeb; 0xdc;  (* VPOR (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0xc1; 0x5d; 0x73; 0xf3; 0x01;
                           (* VPSLLQ (%_% ymm4) (%_% ymm11) (Imm8 (word 1)) *)
  0xc4; 0xc1; 0x75; 0xef; 0xce;
                           (* VPXOR (%_% ymm1) (%_% ymm1) (%_% ymm14) *)
  0xc5; 0xdd; 0xeb; 0xe5;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm5) *)
  0xc4; 0xc1; 0x0d; 0x73; 0xd2; 0x3f;
                           (* VPSRLQ (%_% ymm14) (%_% ymm10) (Imm8 (word 63)) *)
  0xc5; 0xe5; 0xef; 0xd9;  (* VPXOR (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x55; 0x73; 0xf2; 0x01;
                           (* VPSLLQ (%_% ymm5) (%_% ymm10) (Imm8 (word 1)) *)
  0xc5; 0xdd; 0xef; 0xe0;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xeb; 0xee;
                           (* VPOR (%_% ymm5) (%_% ymm5) (%_% ymm14) *)
  0xc5; 0xdd; 0xef; 0xf6;  (* VPXOR (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x55; 0xef; 0xec;
                           (* VPXOR (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc5; 0x9d; 0x73; 0xd1; 0x3f;
                           (* VPSRLQ (%_% ymm12) (%_% ymm1) (Imm8 (word 63)) *)
  0xc5; 0xf5; 0x73; 0xf1; 0x01;
                           (* VPSLLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 1)) *)
  0xc5; 0xd5; 0xef; 0xff;  (* VPXOR (%_% ymm7) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x55; 0xef; 0xc9;
                           (* VPXOR (%_% ymm9) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x75; 0xeb; 0xcc;
                           (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm12) *)
  0xc5; 0x65; 0xef; 0x24; 0x24;
                           (* VPXOR (%_% ymm12) (%_% ymm3) (Memop Word256 (%% (rsp,0))) *)
  0xc4; 0xc1; 0x75; 0xef; 0xcb;
                           (* VPXOR (%_% ymm1) (%_% ymm1) (%_% ymm11) *)
  0xc5; 0xa5; 0x73; 0xd0; 0x3f;
                           (* VPSRLQ (%_% ymm11) (%_% ymm0) (Imm8 (word 63)) *)
  0xc5; 0xfd; 0x73; 0xf0; 0x01;
                           (* VPSLLQ (%_% ymm0) (%_% ymm0) (Imm8 (word 1)) *)
  0xc4; 0x41; 0x75; 0xef; 0xed;
                           (* VPXOR (%_% ymm13) (%_% ymm1) (%_% ymm13) *)
  0xc4; 0x41; 0x75; 0xef; 0xc0;
                           (* VPXOR (%_% ymm8) (%_% ymm1) (%_% ymm8) *)
  0xc4; 0xc1; 0x7d; 0xeb; 0xc3;
                           (* VPOR (%_% ymm0) (%_% ymm0) (%_% ymm11) *)
  0xc4; 0xc1; 0x7d; 0xef; 0xc2;
                           (* VPXOR (%_% ymm0) (%_% ymm0) (%_% ymm10) *)
  0xc5; 0x5d; 0xef; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm10) (%_% ymm4) (Memop Word256 (%% (rsp,192))) *)
  0xc5; 0xfd; 0xef; 0xd2;  (* VPXOR (%_% ymm2) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd2; 0x14;
                           (* VPSRLQ (%_% ymm11) (%_% ymm10) (Imm8 (word 20)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x2c;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 44)) *)
  0xc4; 0x41; 0x2d; 0xeb; 0xd3;
                           (* VPOR (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x55; 0xef; 0xdf;
                           (* VPXOR (%_% ymm11) (%_% ymm5) (%_% ymm15) *)
  0xc4; 0x62; 0x7d; 0x59; 0x3e;
                           (* VPBROADCASTQ (%_% ymm15) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xc1; 0x0d; 0x73; 0xd3; 0x15;
                           (* VPSRLQ (%_% ymm14) (%_% ymm11) (Imm8 (word 21)) *)
  0xc4; 0xc1; 0x25; 0x73; 0xf3; 0x2b;
                           (* VPSLLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 43)) *)
  0xc4; 0x41; 0x25; 0xeb; 0xde;
                           (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm14) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xf3;
                           (* VPANDN (%_% ymm14) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x0d; 0xef; 0xf7;
                           (* VPXOR (%_% ymm14) (%_% ymm14) (%_% ymm15) *)
  0xc4; 0x41; 0x0d; 0xef; 0xfc;
                           (* VPXOR (%_% ymm15) (%_% ymm14) (%_% ymm12) *)
  0xc4; 0xc1; 0x0d; 0x73; 0xd5; 0x2b;
                           (* VPSRLQ (%_% ymm14) (%_% ymm13) (Imm8 (word 43)) *)
  0xc4; 0xc1; 0x15; 0x73; 0xf5; 0x15;
                           (* VPSLLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 21)) *)
  0xc5; 0x7e; 0x7f; 0x3c; 0x24;
                           (* VMOVDQU (Memop Word256 (%% (rsp,0))) (%_% ymm15) *)
  0xc4; 0x41; 0x15; 0xeb; 0xee;
                           (* VPOR (%_% ymm13) (%_% ymm13) (%_% ymm14) *)
  0xc4; 0x41; 0x25; 0xdf; 0xf5;
                           (* VPANDN (%_% ymm14) (%_% ymm11) (%_% ymm13) *)
  0xc4; 0x41; 0x0d; 0xef; 0xfa;
                           (* VPXOR (%_% ymm15) (%_% ymm14) (%_% ymm10) *)
  0xc5; 0x8d; 0x73; 0xd2; 0x32;
                           (* VPSRLQ (%_% ymm14) (%_% ymm2) (Imm8 (word 50)) *)
  0xc5; 0xed; 0x73; 0xf2; 0x0e;
                           (* VPSLLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 14)) *)
  0xc5; 0x7e; 0x7f; 0x7c; 0x24; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rsp,32))) (%_% ymm15) *)
  0xc4; 0xc1; 0x6d; 0xeb; 0xd6;
                           (* VPOR (%_% ymm2) (%_% ymm2) (%_% ymm14) *)
  0xc5; 0x15; 0xdf; 0xf2;  (* VPANDN (%_% ymm14) (%_% ymm13) (%_% ymm2) *)
  0xc4; 0x41; 0x0d; 0xef; 0xdb;
                           (* VPXOR (%_% ymm11) (%_% ymm14) (%_% ymm11) *)
  0xc5; 0x7e; 0x7f; 0x5c; 0x24; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rsp,64))) (%_% ymm11) *)
  0xc4; 0x41; 0x6d; 0xdf; 0xdc;
                           (* VPANDN (%_% ymm11) (%_% ymm2) (%_% ymm12) *)
  0xc4; 0x41; 0x1d; 0xdf; 0xe2;
                           (* VPANDN (%_% ymm12) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x25; 0xef; 0xdd;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm13) *)
  0xc5; 0x7e; 0x7f; 0x5c; 0x24; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rsp,96))) (%_% ymm11) *)
  0xc5; 0x1d; 0xef; 0xda;  (* VPXOR (%_% ymm11) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0xc1; 0x6d; 0x73; 0xd0; 0x24;
                           (* VPSRLQ (%_% ymm2) (%_% ymm8) (Imm8 (word 36)) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xf0; 0x1c;
                           (* VPSLLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 28)) *)
  0xc5; 0x7e; 0x7f; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,128))) (%_% ymm11) *)
  0xc5; 0x3d; 0xeb; 0xc2;  (* VPOR (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xfd; 0xef; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm2) (%_% ymm0) (Memop Word256 (%% (rsp,224))) *)
  0xc5; 0xad; 0x73; 0xd2; 0x2c;
                           (* VPSRLQ (%_% ymm10) (%_% ymm2) (Imm8 (word 44)) *)
  0xc5; 0xed; 0x73; 0xf2; 0x14;
                           (* VPSLLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 20)) *)
  0xc4; 0xc1; 0x6d; 0xeb; 0xd2;
                           (* VPOR (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc5; 0x65; 0xef; 0x94; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm10) (%_% ymm3) (Memop Word256 (%% (rsp,256))) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd2; 0x3d;
                           (* VPSRLQ (%_% ymm11) (%_% ymm10) (Imm8 (word 61)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x03;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 3)) *)
  0xc4; 0x41; 0x2d; 0xeb; 0xd3;
                           (* VPOR (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x6d; 0xdf; 0xda;
                           (* VPANDN (%_% ymm11) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0x41; 0x25; 0xef; 0xd8;
                           (* VPXOR (%_% ymm11) (%_% ymm11) (%_% ymm8) *)
  0xc5; 0x7e; 0x7f; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,160))) (%_% ymm11) *)
  0xc5; 0x5d; 0xef; 0x9c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm11) (%_% ymm4) (Memop Word256 (%% (rsp,352))) *)
  0xc4; 0xc1; 0x1d; 0x73; 0xd3; 0x13;
                           (* VPSRLQ (%_% ymm12) (%_% ymm11) (Imm8 (word 19)) *)
  0xc4; 0xc1; 0x25; 0x73; 0xf3; 0x2d;
                           (* VPSLLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 45)) *)
  0xc4; 0x41; 0x25; 0xeb; 0xdc;
                           (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm12) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xe3;
                           (* VPANDN (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc5; 0x1d; 0xef; 0xe2;  (* VPXOR (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x7e; 0x7f; 0xa4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,192))) (%_% ymm12) *)
  0xc5; 0x9d; 0x73; 0xd7; 0x03;
                           (* VPSRLQ (%_% ymm12) (%_% ymm7) (Imm8 (word 3)) *)
  0xc5; 0xc5; 0x73; 0xf7; 0x3d;
                           (* VPSLLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 61)) *)
  0xc4; 0xc1; 0x45; 0xeb; 0xfc;
                           (* VPOR (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0x25; 0xdf; 0xe7;  (* VPANDN (%_% ymm12) (%_% ymm11) (%_% ymm7) *)
  0xc4; 0x41; 0x1d; 0xef; 0xd2;
                           (* VPXOR (%_% ymm10) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x41; 0x45; 0xdf; 0xe0;
                           (* VPANDN (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc5; 0x3d; 0xdf; 0xc2;  (* VPANDN (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xed; 0x73; 0xd6; 0x3f;
                           (* VPSRLQ (%_% ymm2) (%_% ymm6) (Imm8 (word 63)) *)
  0xc5; 0xcd; 0x73; 0xf6; 0x01;
                           (* VPSLLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 1)) *)
  0xc4; 0x41; 0x1d; 0xef; 0xf3;
                           (* VPXOR (%_% ymm14) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0xcd; 0xeb; 0xf2;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0xc1; 0x6d; 0x73; 0xd1; 0x3a;
                           (* VPSRLQ (%_% ymm2) (%_% ymm9) (Imm8 (word 58)) *)
  0xc5; 0x3d; 0xef; 0xe7;  (* VPXOR (%_% ymm12) (%_% ymm8) (%_% ymm7) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x06;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 6)) *)
  0xc5; 0x7e; 0x7f; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,224))) (%_% ymm12) *)
  0xc5; 0xfd; 0xef; 0xbc; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm7) (%_% ymm0) (Memop Word256 (%% (rsp,416))) *)
  0xc5; 0x35; 0xeb; 0xca;  (* VPOR (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0xf5; 0xef; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm2) (%_% ymm1) (Memop Word256 (%% (rsp,288))) *)
  0xc4; 0xe2; 0x45; 0x00; 0x3a;
                           (* VPSHUFB (%_% ymm7) (%_% ymm7) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0xa5; 0x73; 0xd2; 0x27;
                           (* VPSRLQ (%_% ymm11) (%_% ymm2) (Imm8 (word 39)) *)
  0xc5; 0xed; 0x73; 0xf2; 0x19;
                           (* VPSLLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 25)) *)
  0xc5; 0x25; 0xeb; 0xda;  (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0xc1; 0x35; 0xdf; 0xd3;
                           (* VPANDN (%_% ymm2) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0x25; 0xdf; 0xc7;  (* VPANDN (%_% ymm8) (%_% ymm11) (%_% ymm7) *)
  0xc5; 0x6d; 0xef; 0xe6;  (* VPXOR (%_% ymm12) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xe5; 0xef; 0x94; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm2) (%_% ymm3) (Memop Word256 (%% (rsp,448))) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc1;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm9) *)
  0xc5; 0x7e; 0x7f; 0xa4; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,256))) (%_% ymm12) *)
  0xc5; 0x9d; 0x73; 0xd2; 0x2e;
                           (* VPSRLQ (%_% ymm12) (%_% ymm2) (Imm8 (word 46)) *)
  0xc5; 0xed; 0x73; 0xf2; 0x12;
                           (* VPSLLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 18)) *)
  0xc5; 0x9d; 0xeb; 0xd2;  (* VPOR (%_% ymm2) (%_% ymm12) (%_% ymm2) *)
  0xc5; 0x45; 0xdf; 0xe2;  (* VPANDN (%_% ymm12) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x41; 0x1d; 0xef; 0xfb;
                           (* VPXOR (%_% ymm15) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0x6d; 0xdf; 0xde;  (* VPANDN (%_% ymm11) (%_% ymm2) (%_% ymm6) *)
  0xc4; 0xc1; 0x4d; 0xdf; 0xf1;
                           (* VPANDN (%_% ymm6) (%_% ymm6) (%_% ymm9) *)
  0xc5; 0x25; 0xef; 0xe7;  (* VPXOR (%_% ymm12) (%_% ymm11) (%_% ymm7) *)
  0xc5; 0x7e; 0x7f; 0xa4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,288))) (%_% ymm12) *)
  0xc5; 0x4d; 0xef; 0xe2;  (* VPXOR (%_% ymm12) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xfd; 0xef; 0xb4; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm0) (Memop Word256 (%% (rsp,736))) *)
  0xc5; 0xfd; 0xef; 0x84; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rsp,704))) *)
  0xc5; 0x7e; 0x7f; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,320))) (%_% ymm12) *)
  0xc5; 0xed; 0x73; 0xd6; 0x25;
                           (* VPSRLQ (%_% ymm2) (%_% ymm6) (Imm8 (word 37)) *)
  0xc5; 0xcd; 0x73; 0xf6; 0x1b;
                           (* VPSLLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 27)) *)
  0xc5; 0xed; 0xeb; 0xd6;  (* VPOR (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xe5; 0xef; 0xb4; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm3) (Memop Word256 (%% (rsp,544))) *)
  0xc5; 0xe5; 0xef; 0x9c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rsp,512))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x1c;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 28)) *)
  0xc5; 0xcd; 0x73; 0xf6; 0x24;
                           (* VPSLLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 36)) *)
  0xc5; 0xc5; 0xeb; 0xfe;  (* VPOR (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xdd; 0xef; 0xb4; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm4) (Memop Word256 (%% (rsp,608))) *)
  0xc5; 0xdd; 0xef; 0xa4; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm4) (%_% ymm4) (Memop Word256 (%% (rsp,576))) *)
  0xc5; 0x9d; 0x73; 0xd6; 0x36;
                           (* VPSRLQ (%_% ymm12) (%_% ymm6) (Imm8 (word 54)) *)
  0xc5; 0xcd; 0x73; 0xf6; 0x0a;
                           (* VPSLLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 10)) *)
  0xc5; 0x1d; 0xeb; 0xe6;  (* VPOR (%_% ymm12) (%_% ymm12) (%_% ymm6) *)
  0xc5; 0xd5; 0xef; 0xb4; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm5) (Memop Word256 (%% (rsp,384))) *)
  0xc5; 0xd5; 0xef; 0xac; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm5) (%_% ymm5) (Memop Word256 (%% (rsp,640))) *)
  0xc4; 0x41; 0x45; 0xdf; 0xcc;
                           (* VPANDN (%_% ymm9) (%_% ymm7) (%_% ymm12) *)
  0xc5; 0xa5; 0x73; 0xd6; 0x31;
                           (* VPSRLQ (%_% ymm11) (%_% ymm6) (Imm8 (word 49)) *)
  0xc5; 0xcd; 0x73; 0xf6; 0x0f;
                           (* VPSLLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0x35; 0xef; 0xca;  (* VPXOR (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x25; 0xeb; 0xde;  (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm6) *)
  0xc4; 0xc1; 0x1d; 0xdf; 0xf3;
                           (* VPANDN (%_% ymm6) (%_% ymm12) (%_% ymm11) *)
  0xc5; 0xcd; 0xef; 0xf7;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xfe; 0x7f; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,352))) (%_% ymm6) *)
  0xc5; 0xf5; 0xef; 0xb4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm1) (Memop Word256 (%% (rsp,480))) *)
  0xc5; 0xf5; 0xef; 0x8c; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm1) (%_% ymm1) (Memop Word256 (%% (rsp,672))) *)
  0xc4; 0xe2; 0x4d; 0x00; 0x31;
                           (* VPSHUFB (%_% ymm6) (%_% ymm6) (Memop Word256 (%% (rcx,0))) *)
  0xc5; 0x25; 0xdf; 0xee;  (* VPANDN (%_% ymm13) (%_% ymm11) (%_% ymm6) *)
  0xc4; 0x41; 0x15; 0xef; 0xec;
                           (* VPXOR (%_% ymm13) (%_% ymm13) (%_% ymm12) *)
  0xc5; 0x7e; 0x7f; 0xac; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,384))) (%_% ymm13) *)
  0xc5; 0x4d; 0xdf; 0xea;  (* VPANDN (%_% ymm13) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xed; 0xdf; 0xd7;  (* VPANDN (%_% ymm2) (%_% ymm2) (%_% ymm7) *)
  0xc5; 0xed; 0xef; 0xd6;  (* VPXOR (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xcd; 0x73; 0xd4; 0x3e;
                           (* VPSRLQ (%_% ymm6) (%_% ymm4) (Imm8 (word 62)) *)
  0xc4; 0x41; 0x15; 0xef; 0xeb;
                           (* VPXOR (%_% ymm13) (%_% ymm13) (%_% ymm11) *)
  0xc5; 0xfe; 0x7f; 0x94; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,416))) (%_% ymm2) *)
  0xc5; 0xed; 0x73; 0xd5; 0x02;
                           (* VPSRLQ (%_% ymm2) (%_% ymm5) (Imm8 (word 2)) *)
  0xc5; 0xd5; 0x73; 0xf5; 0x3e;
                           (* VPSLLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 62)) *)
  0xc5; 0xed; 0xeb; 0xd5;  (* VPOR (%_% ymm2) (%_% ymm2) (%_% ymm5) *)
  0xc5; 0xd5; 0x73; 0xd1; 0x09;
                           (* VPSRLQ (%_% ymm5) (%_% ymm1) (Imm8 (word 9)) *)
  0xc5; 0xf5; 0x73; 0xf1; 0x37;
                           (* VPSLLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 55)) *)
  0xc5; 0xdd; 0x73; 0xf4; 0x02;
                           (* VPSLLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 2)) *)
  0xc5; 0xd5; 0xeb; 0xc9;  (* VPOR (%_% ymm1) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0x73; 0xd0; 0x19;
                           (* VPSRLQ (%_% ymm5) (%_% ymm0) (Imm8 (word 25)) *)
  0xc5; 0xcd; 0xeb; 0xe4;  (* VPOR (%_% ymm4) (%_% ymm6) (%_% ymm4) *)
  0xc5; 0xfd; 0x73; 0xf0; 0x27;
                           (* VPSLLQ (%_% ymm0) (%_% ymm0) (Imm8 (word 39)) *)
  0xc5; 0xd5; 0xeb; 0xe8;  (* VPOR (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xf5; 0xdf; 0xc5;  (* VPANDN (%_% ymm0) (%_% ymm1) (%_% ymm5) *)
  0xc5; 0xfd; 0xef; 0xc2;  (* VPXOR (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,448))) (%_% ymm0) *)
  0xc5; 0xfd; 0x73; 0xd3; 0x17;
                           (* VPSRLQ (%_% ymm0) (%_% ymm3) (Imm8 (word 23)) *)
  0xc5; 0xe5; 0x73; 0xf3; 0x29;
                           (* VPSLLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 41)) *)
  0xc5; 0xfd; 0xeb; 0xc3;  (* VPOR (%_% ymm0) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xfd; 0xdf; 0xfc;  (* VPANDN (%_% ymm7) (%_% ymm0) (%_% ymm4) *)
  0xc5; 0xd5; 0xdf; 0xd8;  (* VPANDN (%_% ymm3) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xc5; 0xef; 0xfd;  (* VPXOR (%_% ymm7) (%_% ymm7) (%_% ymm5) *)
  0xc5; 0xdd; 0xdf; 0xea;  (* VPANDN (%_% ymm5) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xed; 0xdf; 0xd1;  (* VPANDN (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xd5; 0xef; 0xe8;  (* VPXOR (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xe5; 0xef; 0xd9;  (* VPXOR (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xed; 0xef; 0xd4;  (* VPXOR (%_% ymm2) (%_% ymm2) (%_% ymm4) *)
  0xc5; 0xfe; 0x7f; 0xac; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,480))) (%_% ymm5) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
  0x49; 0x83; 0xc2; 0x01;  (* ADD (% r10) (Imm8 (word 1)) *)
  0x49; 0x83; 0xfa; 0x18;  (* CMP (% r10) (Imm8 (word 24)) *)
  0x0f; 0x85; 0xfe; 0xfa; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966014)) *)
  0xc5; 0xfe; 0x6f; 0x24; 0x24;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,0))) *)
  0xc5; 0xfe; 0x6f; 0x6c; 0x24; 0x40;
                           (* VMOVDQU (%_% ymm5) (Memop Word256 (%% (rsp,64))) *)
  0xc5; 0xfe; 0x6f; 0x44; 0x24; 0x20;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rsp,32))) *)
  0xc5; 0xfe; 0x6f; 0x4c; 0x24; 0x60;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rsp,96))) *)
  0xc5; 0x7e; 0x6f; 0xa4; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm12) (Memop Word256 (%% (rsp,448))) *)
  0xc5; 0xfe; 0x7f; 0x94; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rsp,448))) (%_% ymm2) *)
  0xc5; 0xdd; 0x6c; 0xd0;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0x6d; 0xc0;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xd5; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0x6d; 0xc9;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xf4; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm2) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xd4; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm2) (%_% ymm4) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,128))) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xe9; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xc1; 0x31;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x37;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm6) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,200))) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,400))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x87; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,600))) (%_% ymm0) *)
  0xc5; 0xfe; 0x6f; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rsp,160))) *)
  0xc5; 0xdd; 0x6c; 0xd0;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0x6d; 0xc8;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x6f; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rsp,192))) *)
  0xc4; 0xc1; 0x7d; 0x6c; 0xe2;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm10) *)
  0xc4; 0xc1; 0x7d; 0x6d; 0xc2;
                           (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm10) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xf4; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm2) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x75; 0x46; 0xe8; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm1) (%_% ymm0) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xd4; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm2) (%_% ymm4) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,224))) *)
  0xc4; 0xe3; 0x75; 0x46; 0xc8; 0x31;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm1) (%_% ymm0) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rsp,256))) *)
  0xc5; 0xfe; 0x7f; 0x97; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,432))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,632))) (%_% ymm1) *)
  0xc5; 0x8d; 0x6c; 0xd4;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm14) (%_% ymm4) *)
  0xc5; 0x8d; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm14) (%_% ymm4) *)
  0xc4; 0xc1; 0x7d; 0x6c; 0xe0;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm8) *)
  0xc4; 0xc1; 0x7d; 0x6d; 0xc0;
                           (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm8) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm6) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,232))) (%_% ymm5) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xf4; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm2) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x75; 0x46; 0xe8; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm1) (%_% ymm0) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xd4; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm2) (%_% ymm4) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x75; 0x46; 0xc8; 0x31;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm1) (%_% ymm0) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0xa4; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,288))) *)
  0xc5; 0xfe; 0x6f; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rsp,320))) *)
  0xc5; 0xfe; 0x7f; 0x97; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,464))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,664))) (%_% ymm1) *)
  0xc5; 0x85; 0x6c; 0xd4;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm15) (%_% ymm4) *)
  0xc5; 0x85; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm15) (%_% ymm4) *)
  0xc4; 0xc1; 0x7d; 0x6c; 0xe1;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm9) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,264))) (%_% ymm5) *)
  0xc4; 0xc1; 0x7d; 0x6d; 0xc1;
                           (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm0) (%_% ymm9) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xf4; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm2) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xd4; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm2) (%_% ymm4) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x75; 0x46; 0xe8; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm1) (%_% ymm0) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x6f; 0xa4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,352))) *)
  0xc4; 0xe3; 0x75; 0x46; 0xc8; 0x31;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm1) (%_% ymm0) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rsp,384))) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,296))) (%_% ymm5) *)
  0xc5; 0xfe; 0x6f; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm5) (Memop Word256 (%% (rsp,416))) *)
  0xc5; 0xfe; 0x7f; 0x97; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,496))) (%_% ymm2) *)
  0xc5; 0xdd; 0x6c; 0xd0;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xdd; 0x6d; 0xc0;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0x95; 0x6c; 0xe5;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm13) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x77; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xf4; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm2) (%_% ymm4) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,696))) (%_% ymm1) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xd4; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm2) (%_% ymm4) (Imm8 (word 49)) *)
  0xc5; 0x95; 0x6d; 0xcd;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm13) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm6) *)
  0xc5; 0xfe; 0x6f; 0xa4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm4) (Memop Word256 (%% (rsp,480))) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xe9; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xc1; 0x31;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,528))) (%_% ymm2) *)
  0xc5; 0x9d; 0x6c; 0xd3;  (* VPUNPCKLQDQ (%_% ymm2) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0x87; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,728))) (%_% ymm0) *)
  0xc5; 0x9d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm0) (%_% ymm12) (%_% ymm3) *)
  0xc5; 0xc5; 0x6c; 0xdc;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm7) (%_% ymm4) *)
  0xc5; 0xc5; 0x6d; 0xcc;  (* VPUNPCKHQDQ (%_% ymm1) (%_% ymm7) (%_% ymm4) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,328))) (%_% ymm5) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xeb; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm2) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x6d; 0x46; 0xd3; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm2) (%_% ymm3) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x6f; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rsp,448))) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm0) (%_% ymm1) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x7d; 0x46; 0xc1; 0x31;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm0) (%_% ymm1) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm5) *)
  0xc4; 0xc3; 0x7d; 0x39; 0xdf; 0x01;
                           (* VEXTRACTI128 (%_% xmm15) (%_% ymm3) (Imm8 (word 1)) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,360))) (%_% ymm4) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,560))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x87; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,760))) (%_% ymm0) *)
  0xc5; 0xf9; 0xd6; 0x9f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,192))) (%_% xmm3) *)
  0xc5; 0xf9; 0x17; 0x9f; 0x88; 0x01; 0x00; 0x00;
                           (* VMOVHPD (Memop Quadword (%% (rdi,392))) (%_% xmm3) *)
  0xc5; 0x79; 0xd6; 0xbf; 0x50; 0x02; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,592))) (%_% xmm15) *)
  0xc5; 0x79; 0x17; 0xbf; 0x18; 0x03; 0x00; 0x00;
                           (* VMOVHPD (Memop Quadword (%% (rdi,792))) (%_% xmm15) *)
  0x4c; 0x89; 0xdc;        (* MOV (% rsp) (% r11) *)
  0xc3                     (* RET *)
];;

let keccak_f1600_x4_avx2_tmc = define_trimmed "keccak_f1600_x4_avx2_tmc" keccak_f1600_x4_avx2_mc;;

let KECCAK_F1600_X4_AVX2_EXEC = X86_MK_CORE_EXEC_RULE keccak_f1600_x4_avx2_tmc;;

let KECCAK_F1600_X4_AVX2_CORRECT = prove
  (`!rc_pointer:int64 bitstate_in:int64 rho8_ptr:int64 rho56_ptr:int64 A1 A2 A3 A4 pc:num stackpointer:int64.
  PAIRWISE (nonoverlapping_modulo (2 EXP 64))
  [(pc, 0x9d9);
   (val stackpointer, 0x300);
   (val bitstate_in, 800);
   (val rc_pointer, 192);
   (val rho8_ptr, 32);
   (val rho56_ptr, 32)]
  ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST keccak_f1600_x4_avx2_tmc) /\
              read RIP s = word (pc + 0xe) /\
              read RSP s = stackpointer /\
              read RDI s = bitstate_in /\
              C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(rho8_ptr,4) s = rho8_constant /\
              wordlist_from_memory(rho56_ptr,4) s = rho56_constant /\
              wordlist_from_memory(bitstate_in,25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4)
             (\s. read RIP s = word(pc + 0x9d5) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
                  wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
                  wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4)
           (MAYCHANGE [RIP; R10; RSI] ,, 
            MAYCHANGE[ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,, 
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (stackpointer, 0x300)],,
            MAYCHANGE [memory :> bytes (bitstate_in, 800)])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`rc_pointer:int64`;`bitstate_in:int64`;`rho8_ptr:int64`;`rho56_ptr:int64`;`A1:int64 list`;`A2:int64 list`;`A3:int64 list`;`A4:int64 list`] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[PAIRWISE; C_ARGUMENTS; ALL] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

   ASM_CASES_TAC `LENGTH(A1:int64 list) = 25 /\ 
   LENGTH(A2:int64 list) = 25 /\
   LENGTH(A3:int64 list) = 25 /\
   LENGTH(A4:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN 
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PAUP_TAC `0` `24` `pc + 0x26f` `pc + 0x76b`
  `\i s.
      (read R10 s = word i /\
       read RDI s = bitstate_in /\
       read RSP s = stackpointer /\
       read RDX s = rho8_ptr /\
       read RCX s = rho56_ptr /\
       read RSI s = word_add rc_pointer (word (8 * i)) /\
       wordlist_from_memory(rho8_ptr,4) s = rho8_constant /\
       wordlist_from_memory(rho56_ptr,4) s = rho56_constant /\
       wordlist_from_memory(rc_pointer,24) s = round_constants /\
       (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
        (wordlist_from_memory(word_add stackpointer (word 0x0),7) s)
        (CONS (read YMM10 s) []))
        (CONS (read YMM14 s) []))
        (wordlist_from_memory(word_add stackpointer (word 0xe0),2) s))
        (CONS (read YMM8 s) []))
        (CONS (read YMM15 s) []))
        (wordlist_from_memory(word_add stackpointer (word 0x120),2) s))
        (CONS (read YMM9 s) []))
        (wordlist_from_memory(word_add stackpointer (word 0x160),2) s))
        (CONS (read YMM13 s) []))
        (wordlist_from_memory(word_add stackpointer (word 0x1a0),2) s))
        (CONS (read YMM3 s) []))
        (CONS (read YMM7 s) []))
        (wordlist_from_memory(word_add stackpointer (word 0x1e0),1) s))
        (CONS (read YMM2 s) [])) =
       (MAP2 word_join ((MAP2 word_join (keccak (i) A4) (keccak (i) A3)):int128 list)
                ((MAP2 word_join (keccak (i) A2) (keccak (i) A1)):int128 list)):int256 list) /\
       (read ZF s <=> i = 24)` THEN
  REPEAT CONJ_TAC THENL 
    [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[rho56_constant; rho8_constant; round_constants; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,100) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho8_ptr,4) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho56_ptr,4) s:int64 list`] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[APPEND] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 100)) s0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 0 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 200 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 400 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 600 25 THEN
    MEMORY_256_FROM_64_TAC "rho8_ptr" 0 4 THEN
    MEMORY_256_FROM_64_TAC "rho56_ptr" 0 4 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN 
    REPEAT STRIP_TAC THEN
    X86_STEPS_TAC KECCAK_F1600_X4_AVX2_EXEC (1--96) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL 
    [PURE_ONCE_REWRITE_TAC[ARITH_RULE `8 * 0 = 0`] THEN
        REWRITE_TAC[WORD_ADD_0];
        ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_64] THEN
        ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_128] THEN
        EXPAND_TAC "A1" THEN
        EXPAND_TAC "A2" THEN
        EXPAND_TAC "A3" THEN
        EXPAND_TAC "A4" THEN
        REWRITE_TAC[keccak] THEN 
        REWRITE_TAC[MAP2] THEN
        REWRITE_TAC[CONS_11] THEN
        CONV_TAC WORD_BLAST];

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN

    REWRITE_TAC[rho56_constant; rho8_constant; round_constants; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,100) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho8_ptr,1) s:int256 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho56_ptr,1) s:int256 list`] THEN
    REWRITE_TAC[APPEND] THEN
    MP_TAC(ISPECL [`A1:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN

    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc_pointer (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]; 
      ALL_TAC] THEN
    
    ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_64] THEN
    ASM_REWRITE_TAC [WORD_SUBWORD_JOIN_EXTRACT_128] THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 100)) s0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 0 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 200 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 400 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 600 25 THEN
    MEMORY_256_FROM_64_TAC "rho8_ptr" 0 4 THEN
    MEMORY_256_FROM_64_TAC "rho56_ptr" 0 4 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT STRIP_TAC THEN
    X86_STEPS_TAC KECCAK_F1600_X4_AVX2_EXEC (1--223) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
      [REWRITE_TAC[WORD_ADD];
      CONV_TAC WORD_BLAST;
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE]) THEN
      REWRITE_TAC[keccak; keccak_round] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN 
      REWRITE_TAC[MAP2; CONS_11] THEN
       CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN BITBLAST_TAC;

      REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551593):int64 = 
              word_sub x (word 23)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN 
      REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT; ARITH_RULE `23 < 2 EXP 64`] THEN
      CONJ_TAC THENL 
        [UNDISCH_TAC `i < 24` THEN ARITH_TAC; 
        ARITH_TAC]];

    (*** The trivial loop-back goal ***)

   X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN

    REWRITE_TAC[rho56_constant; rho8_constant; round_constants; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,100) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho8_ptr,1) s:int256 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho56_ptr,1) s:int256 list`] THEN
    REWRITE_TAC[APPEND] THEN
    MP_TAC(ISPECL [`A1:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN 
    REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 100)) s0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 0 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 200 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 400 25 THEN
    MEMORY_256_FROM_64_TAC "bitstate_in" 600 25 THEN
    MEMORY_256_FROM_64_TAC "rho8_ptr" 0 4 THEN
    MEMORY_256_FROM_64_TAC "rho56_ptr" 0 4 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT STRIP_TAC THEN
    X86_STEPS_TAC KECCAK_F1600_X4_AVX2_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN 
    ASM_REWRITE_TAC[];

    (*** The tail of logical not operation and writeback ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,100) s:int64 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho8_ptr,1) s:int256 list`;
                WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rho56_ptr,1) s:int256 list`] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[APPEND] THEN
    MP_TAC(ISPECL [`A1:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A2:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A3:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A4:int64 list`; `24:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN 
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [keccak; keccak_round] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC KECCAK_F1600_X4_AVX2_EXEC (1--96) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    BITBLAST_TAC]);;


let KECCAK_F1600_X4_AVX2_FULL_EXEC = X86_MK_EXEC_RULE keccak_f1600_x4_avx2_tmc;;

let KECCAK_F1600_X4_AVX2_NOIBT_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 rho8_ptr:int64 rho56_ptr:int64 A1 A2 A3 A4 pc:num stackpointer:int64 returnaddress.
  PAIRWISE (nonoverlapping_modulo (2 EXP 64))
    [(pc, LENGTH keccak_f1600_x4_avx2_tmc);
    (val (word_sub stackpointer (word 0x31f)), 0x31f);
    (val bitstate_in, 800);
    (val rc_pointer, 192);
    (val rho8_ptr, 32);
    (val rho56_ptr, 32)] /\
  nonoverlapping_modulo (2 EXP 64)
    (val bitstate_in, 800)
    (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx2_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr] s /\
              wordlist_from_memory(rc_pointer, 24) s = round_constants /\
              wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
              wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
              wordlist_from_memory(bitstate_in, 25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = A4)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = keccak 24 A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = keccak 24 A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = keccak 24 A4)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 800);
                     memory :> bytes(word_sub stackpointer (word 0x31f), 0x31f)])`,
  REPLICATE_TAC 9 GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  WORD_FORALL_OFFSET_TAC 0x31f THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[PAIRWISE; ALL; C_ARGUMENTS] THEN
  REWRITE_TAC[fst KECCAK_F1600_X4_AVX2_FULL_EXEC] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REPEAT STRIP_TAC THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC KECCAK_F1600_X4_AVX2_FULL_EXEC (1--3) THEN
  ABBREV_TAC
   `delta =
    val(word_sub (word 31)
                 (word_and (word_add stackpointer (word 0x31f)) (word 31)):int64)` THEN
  SUBGOAL_THEN `delta <= 31` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN CONV_TAC BITBLAST_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_sub (word_and (word_add stackpointer (word 0x31f)) (word 0xffffffffffffffe0))
            (word 0x300):int64 =
    word_add stackpointer (word delta)`
  SUBST_ALL_TAC THENL
    [EXPAND_TAC "delta" THEN CONV_TAC BITBLAST_RULE; ALL_TAC] THEN
 
  MP_TAC(SPECL
   [`rc_pointer:int64`; `bitstate_in:int64`; `rho8_ptr:int64`; `rho56_ptr:int64`;
    `A1:int64 list`; `A2:int64 list`; `A3:int64 list`; `A4:int64 list`;
    `pc:num`; `word_add stackpointer (word delta):int64`]
   KECCAK_F1600_X4_AVX2_CORRECT) THEN
  ANTS_TAC THENL [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN REWRITE_TAC[PAIRWISE; ALL; C_ARGUMENTS] THEN REPEAT NONOVERLAPPING_TAC; ALL_TAC] THEN

  REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC[] THEN

  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  X86_BIGSTEP_TAC KECCAK_F1600_X4_AVX2_FULL_EXEC "s4" THENL
   [MATCH_MP_TAC BYTES_LOADED_BUTLAST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X86_STEPS_TAC KECCAK_F1600_X4_AVX2_FULL_EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let KECCAK_F1600_X4_AVX2_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 rho8_ptr:int64 rho56_ptr:int64 A1 A2 A3 A4 pc:num stackpointer:int64 returnaddress.
  PAIRWISE (nonoverlapping_modulo (2 EXP 64))
    [(pc, LENGTH keccak_f1600_x4_avx2_mc);
    (val (word_sub stackpointer (word 0x31f)), 0x31f);
    (val bitstate_in, 800);
    (val rc_pointer, 192);
    (val rho8_ptr, 32);
    (val rho56_ptr, 32)] /\
  nonoverlapping_modulo (2 EXP 64)
    (val bitstate_in, 800)
    (val (word_sub stackpointer (word 0x31f)), 0x31f + 8)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) keccak_f1600_x4_avx2_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [bitstate_in; rc_pointer; rho8_ptr; rho56_ptr] s /\
              wordlist_from_memory(rc_pointer, 24) s = round_constants /\
              wordlist_from_memory(rho8_ptr, 4) s = rho8_constant /\
              wordlist_from_memory(rho56_ptr, 4) s = rho56_constant /\
              wordlist_from_memory(bitstate_in, 25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = A4)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              wordlist_from_memory(bitstate_in, 25) s = keccak 24 A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200), 25) s = keccak 24 A2 /\
              wordlist_from_memory(word_add bitstate_in (word 400), 25) s = keccak 24 A3 /\
              wordlist_from_memory(word_add bitstate_in (word 600), 25) s = keccak 24 A4)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 800);
                     memory :> bytes(word_sub stackpointer (word 0x31f), 0x31f)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV NUM_ADD_CONV THENC
                   ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV THENC
                   REWRITE_CONV[PAIRWISE; ALL] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV KECCAK_F1600_X4_AVX2_NOIBT_SUBROUTINE_CORRECT)));;
