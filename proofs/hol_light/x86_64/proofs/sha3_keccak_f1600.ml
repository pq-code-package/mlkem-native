(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 needs "x86/proofs/base.ml";;
 needs "common/keccak_spec.ml";;

(**** print_literal_from_elf "x86_64/mlkem/sha3_keccak_f1600.o";;
****)

let sha3_keccak_f1600_mc = define_assert_from_elf
  "sha3_keccak_f1600_mc" "x86_64/mlkem/sha3_keccak_f1600.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xd0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 208)) *)
  0x48; 0xf7; 0x57; 0x08;  (* NOT (Memop Quadword (%% (rdi,8))) *)
  0x48; 0xf7; 0x57; 0x10;  (* NOT (Memop Quadword (%% (rdi,16))) *)
  0x48; 0xf7; 0x57; 0x40;  (* NOT (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xf7; 0x57; 0x60;  (* NOT (Memop Quadword (%% (rdi,96))) *)
  0x48; 0xf7; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,136))) *)
  0x48; 0xf7; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,160))) *)
  0x4c; 0x8d; 0x3c; 0x24;  (* LEA (% r15) (%% (rsp,0)) *)
  0x48; 0x8b; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,160))) *)
  0x48; 0x8b; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0x8b; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rdi,176))) *)
  0x48; 0x8b; 0x97; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,184))) *)
  0x48; 0x8b; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rdi,192))) *)
  0x49; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Imm32 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r8) *)
  0x4c; 0x8b; 0x07;        (* MOV (% r8) (Memop Quadword (%% (rdi,0))) *)
  0x4c; 0x8b; 0x4f; 0x30;  (* MOV (% r9) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x8b; 0x57; 0x60;  (* MOV (% r10) (Memop Quadword (%% (rdi,96))) *)
  0x4c; 0x8b; 0x9f; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,144))) *)
  0x48; 0x33; 0x4f; 0x10;  (* XOR (% rcx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x57; 0x18;  (* XOR (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
  0x48; 0x33; 0x5f; 0x08;  (* XOR (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x33; 0x4f; 0x38;  (* XOR (% rcx) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x33; 0x47; 0x28;  (* XOR (% rax) (Memop Quadword (%% (rdi,40))) *)
  0x49; 0x89; 0xec;        (* MOV (% r12) (% rbp) *)
  0x48; 0x33; 0x6f; 0x20;  (* XOR (% rbp) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x31; 0xd1;        (* XOR (% rcx) (% r10) *)
  0x48; 0x33; 0x47; 0x50;  (* XOR (% rax) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x33; 0x57; 0x40;  (* XOR (% rdx) (Memop Quadword (%% (rdi,64))) *)
  0x4c; 0x31; 0xcb;        (* XOR (% rbx) (% r9) *)
  0x48; 0x33; 0x6f; 0x48;  (* XOR (% rbp) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x33; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,136))) *)
  0x48; 0x33; 0x47; 0x78;  (* XOR (% rax) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x33; 0x57; 0x68;  (* XOR (% rdx) (Memop Quadword (%% (rdi,104))) *)
  0x48; 0x33; 0x5f; 0x58;  (* XOR (% rbx) (Memop Quadword (%% (rdi,88))) *)
  0x48; 0x33; 0x6f; 0x70;  (* XOR (% rbp) (Memop Quadword (%% (rdi,112))) *)
  0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
  0x48; 0xd1; 0xc1;        (* ROL (% rcx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x4c; 0x31; 0xda;        (* XOR (% rdx) (% r11) *)
  0x48; 0xd1; 0xc0;        (* ROL (% rax) (Imm8 (word 1)) *)
  0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
  0x48; 0x33; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* XOR (% rbx) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0xd1; 0xc2;        (* ROL (% rdx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
  0x48; 0x33; 0xaf; 0x98; 0x00; 0x00; 0x00;
                           (* XOR (% rbp) (Memop Quadword (%% (rdi,152))) *)
  0x48; 0xd1; 0xc3;        (* ROL (% rbx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0xd1; 0xc5;        (* ROL (% rbp) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xed;        (* XOR (% rbp) (% r13) *)
  0x49; 0x31; 0xc9;        (* XOR (% r9) (% rcx) *)
  0x49; 0x31; 0xd2;        (* XOR (% r10) (% rdx) *)
  0x49; 0xc1; 0xc1; 0x2c;  (* ROL (% r9) (Imm8 (word 44)) *)
  0x49; 0x31; 0xeb;        (* XOR (% r11) (% rbp) *)
  0x49; 0x31; 0xc4;        (* XOR (% r12) (% rax) *)
  0x49; 0xc1; 0xc2; 0x2b;  (* ROL (% r10) (Imm8 (word 43)) *)
  0x49; 0x31; 0xd8;        (* XOR (% r8) (% rbx) *)
  0x4d; 0x89; 0xcd;        (* MOV (% r13) (% r9) *)
  0x49; 0xc1; 0xc3; 0x15;  (* ROL (% r11) (Imm8 (word 21)) *)
  0x4d; 0x09; 0xd1;        (* OR (% r9) (% r10) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x49; 0xc1; 0xc4; 0x0e;  (* ROL (% r12) (Imm8 (word 14)) *)
  0x4c; 0x33; 0x0e;        (* XOR (% r9) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4d; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (r15,0))) (% r9) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x89; 0x67; 0x10;  (* MOV (Memop Quadword (%% (r15,16))) (% r12) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4c; 0x8b; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4d; 0x31; 0xea;        (* XOR (% r10) (% r13) *)
  0x4d; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (r15,8))) (% r10) *)
  0x4d; 0x21; 0xc5;        (* AND (% r13) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rdi,72))) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x8b; 0x57; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rdi,80))) *)
  0x4d; 0x89; 0x6f; 0x20;  (* MOV (Memop Quadword (%% (r15,32))) (% r13) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x47; 0x18;  (* MOV (% r8) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,128))) *)
  0x4d; 0x89; 0x77; 0x18;  (* MOV (Memop Quadword (%% (r15,24))) (% r14) *)
  0x49; 0x31; 0xe8;        (* XOR (% r8) (% rbp) *)
  0x49; 0x31; 0xd4;        (* XOR (% r12) (% rdx) *)
  0x49; 0xc1; 0xc0; 0x1c;  (* ROL (% r8) (Imm8 (word 28)) *)
  0x49; 0x31; 0xcb;        (* XOR (% r11) (% rcx) *)
  0x49; 0x31; 0xc1;        (* XOR (% r9) (% rax) *)
  0x49; 0xc1; 0xc4; 0x3d;  (* ROL (% r12) (Imm8 (word 61)) *)
  0x49; 0xc1; 0xc3; 0x2d;  (* ROL (% r11) (Imm8 (word 45)) *)
  0x49; 0x31; 0xda;        (* XOR (% r10) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x14;  (* ROL (% r9) (Imm8 (word 20)) *)
  0x4d; 0x89; 0xc5;        (* MOV (% r13) (% r8) *)
  0x4d; 0x09; 0xe0;        (* OR (% r8) (% r12) *)
  0x49; 0xc1; 0xc2; 0x03;  (* ROL (% r10) (Imm8 (word 3)) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (r15,64))) (% r8) *)
  0x4d; 0x89; 0xce;        (* MOV (% r14) (% r9) *)
  0x4d; 0x21; 0xe9;        (* AND (% r9) (% r13) *)
  0x4c; 0x8b; 0x47; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4d; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (r15,72))) (% r9) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4c; 0x8b; 0x4f; 0x38;  (* MOV (% r9) (Memop Quadword (%% (rdi,56))) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x4d; 0x89; 0x67; 0x38;  (* MOV (Memop Quadword (%% (r15,56))) (% r12) *)
  0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
  0x4c; 0x8b; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,160))) *)
  0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
  0x4d; 0x89; 0x5f; 0x30;  (* MOV (Memop Quadword (%% (r15,48))) (% r11) *)
  0x4d; 0x09; 0xd6;        (* OR (% r14) (% r10) *)
  0x4c; 0x8b; 0x57; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rdi,104))) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4c; 0x8b; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,152))) *)
  0x4d; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (r15,40))) (% r14) *)
  0x49; 0x31; 0xea;        (* XOR (% r10) (% rbp) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x49; 0xc1; 0xc2; 0x19;  (* ROL (% r10) (Imm8 (word 25)) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x49; 0xc1; 0xc3; 0x08;  (* ROL (% r11) (Imm8 (word 8)) *)
  0x49; 0x31; 0xdc;        (* XOR (% r12) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x06;  (* ROL (% r9) (Imm8 (word 6)) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x49; 0xc1; 0xc4; 0x12;  (* ROL (% r12) (Imm8 (word 18)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x49; 0xd1; 0xc0;        (* ROL (% r8) (Imm8 (word 1)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x57; 0x58;  (* MOV (Memop Quadword (%% (r15,88))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x8b; 0x57; 0x58;  (* MOV (% r10) (Memop Quadword (%% (rdi,88))) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0x67; 0x60;  (* MOV (Memop Quadword (%% (r15,96))) (% r12) *)
  0x4d; 0x09; 0xcd;        (* OR (% r13) (% r9) *)
  0x4c; 0x8b; 0xa7; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,184))) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x50;  (* MOV (Memop Quadword (%% (r15,80))) (% r13) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x4f; 0x70;  (* MOV (Memop Quadword (%% (r15,112))) (% r9) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,136))) *)
  0x4d; 0x89; 0x77; 0x68;  (* MOV (Memop Quadword (%% (r15,104))) (% r14) *)
  0x4c; 0x8b; 0x47; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rdi,32))) *)
  0x49; 0x31; 0xca;        (* XOR (% r10) (% rcx) *)
  0x49; 0x31; 0xd3;        (* XOR (% r11) (% rdx) *)
  0x49; 0xc1; 0xc2; 0x0a;  (* ROL (% r10) (Imm8 (word 10)) *)
  0x49; 0x31; 0xd9;        (* XOR (% r9) (% rbx) *)
  0x49; 0xc1; 0xc3; 0x0f;  (* ROL (% r11) (Imm8 (word 15)) *)
  0x49; 0x31; 0xec;        (* XOR (% r12) (% rbp) *)
  0x49; 0xc1; 0xc1; 0x24;  (* ROL (% r9) (Imm8 (word 36)) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x49; 0xc1; 0xc4; 0x38;  (* ROL (% r12) (Imm8 (word 56)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x49; 0xc1; 0xc0; 0x1b;  (* ROL (% r8) (Imm8 (word 27)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,128))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0xa7; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,136))) (% r12) *)
  0x4d; 0x21; 0xcd;        (* AND (% r13) (% r9) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x78;  (* MOV (Memop Quadword (%% (r15,120))) (% r13) *)
  0x4d; 0x09; 0xc1;        (* OR (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x8f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,152))) (% r9) *)
  0x4d; 0x21; 0xf0;        (* AND (% r8) (% r14) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,144))) (% r8) *)
  0x48; 0x33; 0x57; 0x10;  (* XOR (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x6f; 0x40;  (* XOR (% rbp) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xc1; 0xc2; 0x3e;  (* ROL (% rdx) (Imm8 (word 62)) *)
  0x48; 0x33; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0xc1; 0xc5; 0x37;  (* ROL (% rbp) (Imm8 (word 55)) *)
  0x48; 0x33; 0x47; 0x70;  (* XOR (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0xc1; 0xc1; 0x02;  (* ROL (% rcx) (Imm8 (word 2)) *)
  0x48; 0x33; 0x5f; 0x78;  (* XOR (% rbx) (Memop Quadword (%% (rdi,120))) *)
  0x4c; 0x87; 0xff;        (* XCHG (% r15) (% rdi) *)
  0x48; 0xc1; 0xc0; 0x27;  (* ROL (% rax) (Imm8 (word 39)) *)
  0x48; 0xc1; 0xc3; 0x29;  (* ROL (% rbx) (Imm8 (word 41)) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0x21; 0xea;        (* AND (% rdx) (% rbp) *)
  0x48; 0xf7; 0xd5;        (* NOT (% rbp) *)
  0x48; 0x31; 0xca;        (* XOR (% rdx) (% rcx) *)
  0x48; 0x89; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rdx) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x48; 0x89; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rax) *)
  0x49; 0x09; 0xcd;        (* OR (% r13) (% rcx) *)
  0x49; 0x31; 0xdd;        (* XOR (% r13) (% rbx) *)
  0x4c; 0x89; 0xaf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r13) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
  0x48; 0x89; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rcx) *)
  0x4c; 0x09; 0xf3;        (* OR (% rbx) (% r14) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0x89; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rbx) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x48; 0x8d; 0x76; 0x08;  (* LEA (% rsi) (%% (rsi,8)) *)
  0x4c; 0x8b; 0x07;        (* MOV (% r8) (Memop Quadword (%% (rdi,0))) *)
  0x4c; 0x8b; 0x4f; 0x30;  (* MOV (% r9) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x8b; 0x57; 0x60;  (* MOV (% r10) (Memop Quadword (%% (rdi,96))) *)
  0x4c; 0x8b; 0x9f; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,144))) *)
  0x48; 0x33; 0x4f; 0x10;  (* XOR (% rcx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x57; 0x18;  (* XOR (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
  0x48; 0x33; 0x5f; 0x08;  (* XOR (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x33; 0x4f; 0x38;  (* XOR (% rcx) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x33; 0x47; 0x28;  (* XOR (% rax) (Memop Quadword (%% (rdi,40))) *)
  0x49; 0x89; 0xec;        (* MOV (% r12) (% rbp) *)
  0x48; 0x33; 0x6f; 0x20;  (* XOR (% rbp) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x31; 0xd1;        (* XOR (% rcx) (% r10) *)
  0x48; 0x33; 0x47; 0x50;  (* XOR (% rax) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x33; 0x57; 0x40;  (* XOR (% rdx) (Memop Quadword (%% (rdi,64))) *)
  0x4c; 0x31; 0xcb;        (* XOR (% rbx) (% r9) *)
  0x48; 0x33; 0x6f; 0x48;  (* XOR (% rbp) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x33; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,136))) *)
  0x48; 0x33; 0x47; 0x78;  (* XOR (% rax) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x33; 0x57; 0x68;  (* XOR (% rdx) (Memop Quadword (%% (rdi,104))) *)
  0x48; 0x33; 0x5f; 0x58;  (* XOR (% rbx) (Memop Quadword (%% (rdi,88))) *)
  0x48; 0x33; 0x6f; 0x70;  (* XOR (% rbp) (Memop Quadword (%% (rdi,112))) *)
  0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
  0x48; 0xd1; 0xc1;        (* ROL (% rcx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x4c; 0x31; 0xda;        (* XOR (% rdx) (% r11) *)
  0x48; 0xd1; 0xc0;        (* ROL (% rax) (Imm8 (word 1)) *)
  0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
  0x48; 0x33; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* XOR (% rbx) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0xd1; 0xc2;        (* ROL (% rdx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
  0x48; 0x33; 0xaf; 0x98; 0x00; 0x00; 0x00;
                           (* XOR (% rbp) (Memop Quadword (%% (rdi,152))) *)
  0x48; 0xd1; 0xc3;        (* ROL (% rbx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0xd1; 0xc5;        (* ROL (% rbp) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xed;        (* XOR (% rbp) (% r13) *)
  0x49; 0x31; 0xc9;        (* XOR (% r9) (% rcx) *)
  0x49; 0x31; 0xd2;        (* XOR (% r10) (% rdx) *)
  0x49; 0xc1; 0xc1; 0x2c;  (* ROL (% r9) (Imm8 (word 44)) *)
  0x49; 0x31; 0xeb;        (* XOR (% r11) (% rbp) *)
  0x49; 0x31; 0xc4;        (* XOR (% r12) (% rax) *)
  0x49; 0xc1; 0xc2; 0x2b;  (* ROL (% r10) (Imm8 (word 43)) *)
  0x49; 0x31; 0xd8;        (* XOR (% r8) (% rbx) *)
  0x4d; 0x89; 0xcd;        (* MOV (% r13) (% r9) *)
  0x49; 0xc1; 0xc3; 0x15;  (* ROL (% r11) (Imm8 (word 21)) *)
  0x4d; 0x09; 0xd1;        (* OR (% r9) (% r10) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x49; 0xc1; 0xc4; 0x0e;  (* ROL (% r12) (Imm8 (word 14)) *)
  0x4c; 0x33; 0x0e;        (* XOR (% r9) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4d; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (r15,0))) (% r9) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x89; 0x67; 0x10;  (* MOV (Memop Quadword (%% (r15,16))) (% r12) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4c; 0x8b; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4d; 0x31; 0xea;        (* XOR (% r10) (% r13) *)
  0x4d; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (r15,8))) (% r10) *)
  0x4d; 0x21; 0xc5;        (* AND (% r13) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rdi,72))) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x8b; 0x57; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rdi,80))) *)
  0x4d; 0x89; 0x6f; 0x20;  (* MOV (Memop Quadword (%% (r15,32))) (% r13) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x47; 0x18;  (* MOV (% r8) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,128))) *)
  0x4d; 0x89; 0x77; 0x18;  (* MOV (Memop Quadword (%% (r15,24))) (% r14) *)
  0x49; 0x31; 0xe8;        (* XOR (% r8) (% rbp) *)
  0x49; 0x31; 0xd4;        (* XOR (% r12) (% rdx) *)
  0x49; 0xc1; 0xc0; 0x1c;  (* ROL (% r8) (Imm8 (word 28)) *)
  0x49; 0x31; 0xcb;        (* XOR (% r11) (% rcx) *)
  0x49; 0x31; 0xc1;        (* XOR (% r9) (% rax) *)
  0x49; 0xc1; 0xc4; 0x3d;  (* ROL (% r12) (Imm8 (word 61)) *)
  0x49; 0xc1; 0xc3; 0x2d;  (* ROL (% r11) (Imm8 (word 45)) *)
  0x49; 0x31; 0xda;        (* XOR (% r10) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x14;  (* ROL (% r9) (Imm8 (word 20)) *)
  0x4d; 0x89; 0xc5;        (* MOV (% r13) (% r8) *)
  0x4d; 0x09; 0xe0;        (* OR (% r8) (% r12) *)
  0x49; 0xc1; 0xc2; 0x03;  (* ROL (% r10) (Imm8 (word 3)) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (r15,64))) (% r8) *)
  0x4d; 0x89; 0xce;        (* MOV (% r14) (% r9) *)
  0x4d; 0x21; 0xe9;        (* AND (% r9) (% r13) *)
  0x4c; 0x8b; 0x47; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4d; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (r15,72))) (% r9) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4c; 0x8b; 0x4f; 0x38;  (* MOV (% r9) (Memop Quadword (%% (rdi,56))) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x4d; 0x89; 0x67; 0x38;  (* MOV (Memop Quadword (%% (r15,56))) (% r12) *)
  0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
  0x4c; 0x8b; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,160))) *)
  0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
  0x4d; 0x89; 0x5f; 0x30;  (* MOV (Memop Quadword (%% (r15,48))) (% r11) *)
  0x4d; 0x09; 0xd6;        (* OR (% r14) (% r10) *)
  0x4c; 0x8b; 0x57; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rdi,104))) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4c; 0x8b; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,152))) *)
  0x4d; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (r15,40))) (% r14) *)
  0x49; 0x31; 0xea;        (* XOR (% r10) (% rbp) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x49; 0xc1; 0xc2; 0x19;  (* ROL (% r10) (Imm8 (word 25)) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x49; 0xc1; 0xc3; 0x08;  (* ROL (% r11) (Imm8 (word 8)) *)
  0x49; 0x31; 0xdc;        (* XOR (% r12) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x06;  (* ROL (% r9) (Imm8 (word 6)) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x49; 0xc1; 0xc4; 0x12;  (* ROL (% r12) (Imm8 (word 18)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x49; 0xd1; 0xc0;        (* ROL (% r8) (Imm8 (word 1)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x57; 0x58;  (* MOV (Memop Quadword (%% (r15,88))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x8b; 0x57; 0x58;  (* MOV (% r10) (Memop Quadword (%% (rdi,88))) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0x67; 0x60;  (* MOV (Memop Quadword (%% (r15,96))) (% r12) *)
  0x4d; 0x09; 0xcd;        (* OR (% r13) (% r9) *)
  0x4c; 0x8b; 0xa7; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,184))) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x50;  (* MOV (Memop Quadword (%% (r15,80))) (% r13) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x4f; 0x70;  (* MOV (Memop Quadword (%% (r15,112))) (% r9) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,136))) *)
  0x4d; 0x89; 0x77; 0x68;  (* MOV (Memop Quadword (%% (r15,104))) (% r14) *)
  0x4c; 0x8b; 0x47; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rdi,32))) *)
  0x49; 0x31; 0xca;        (* XOR (% r10) (% rcx) *)
  0x49; 0x31; 0xd3;        (* XOR (% r11) (% rdx) *)
  0x49; 0xc1; 0xc2; 0x0a;  (* ROL (% r10) (Imm8 (word 10)) *)
  0x49; 0x31; 0xd9;        (* XOR (% r9) (% rbx) *)
  0x49; 0xc1; 0xc3; 0x0f;  (* ROL (% r11) (Imm8 (word 15)) *)
  0x49; 0x31; 0xec;        (* XOR (% r12) (% rbp) *)
  0x49; 0xc1; 0xc1; 0x24;  (* ROL (% r9) (Imm8 (word 36)) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x49; 0xc1; 0xc4; 0x38;  (* ROL (% r12) (Imm8 (word 56)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x49; 0xc1; 0xc0; 0x1b;  (* ROL (% r8) (Imm8 (word 27)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,128))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0xa7; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,136))) (% r12) *)
  0x4d; 0x21; 0xcd;        (* AND (% r13) (% r9) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x78;  (* MOV (Memop Quadword (%% (r15,120))) (% r13) *)
  0x4d; 0x09; 0xc1;        (* OR (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x8f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,152))) (% r9) *)
  0x4d; 0x21; 0xf0;        (* AND (% r8) (% r14) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,144))) (% r8) *)
  0x48; 0x33; 0x57; 0x10;  (* XOR (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x6f; 0x40;  (* XOR (% rbp) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xc1; 0xc2; 0x3e;  (* ROL (% rdx) (Imm8 (word 62)) *)
  0x48; 0x33; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0xc1; 0xc5; 0x37;  (* ROL (% rbp) (Imm8 (word 55)) *)
  0x48; 0x33; 0x47; 0x70;  (* XOR (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0xc1; 0xc1; 0x02;  (* ROL (% rcx) (Imm8 (word 2)) *)
  0x48; 0x33; 0x5f; 0x78;  (* XOR (% rbx) (Memop Quadword (%% (rdi,120))) *)
  0x4c; 0x87; 0xff;        (* XCHG (% r15) (% rdi) *)
  0x48; 0xc1; 0xc0; 0x27;  (* ROL (% rax) (Imm8 (word 39)) *)
  0x48; 0xc1; 0xc3; 0x29;  (* ROL (% rbx) (Imm8 (word 41)) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0x21; 0xea;        (* AND (% rdx) (% rbp) *)
  0x48; 0xf7; 0xd5;        (* NOT (% rbp) *)
  0x48; 0x31; 0xca;        (* XOR (% rdx) (% rcx) *)
  0x48; 0x89; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rdx) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x48; 0x89; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rax) *)
  0x49; 0x09; 0xcd;        (* OR (% r13) (% rcx) *)
  0x49; 0x31; 0xdd;        (* XOR (% r13) (% rbx) *)
  0x4c; 0x89; 0xaf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r13) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
  0x48; 0x89; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rcx) *)
  0x4c; 0x09; 0xf3;        (* OR (% rbx) (% r14) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0x89; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rbx) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x48; 0x8d; 0x76; 0x08;  (* LEA (% rsi) (%% (rsi,8)) *)
  0x4c; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,200))) *)
  0x49; 0x83; 0xc0; 0x02;  (* ADD (% r8) (Imm8 (word 2)) *)
  0x49; 0x83; 0xf8; 0x18;  (* CMP (% r8) (Imm8 (word 24)) *)
  0x0f; 0x85; 0x2a; 0xfa; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965802)) *)
  0x48; 0x8d; 0xb6; 0x40; 0xff; 0xff; 0xff;
                           (* LEA (% rsi) (%% (rsi,18446744073709551424)) *)
  0x48; 0xf7; 0x57; 0x08;  (* NOT (Memop Quadword (%% (rdi,8))) *)
  0x48; 0xf7; 0x57; 0x10;  (* NOT (Memop Quadword (%% (rdi,16))) *)
  0x48; 0xf7; 0x57; 0x40;  (* NOT (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xf7; 0x57; 0x60;  (* NOT (Memop Quadword (%% (rdi,96))) *)
  0x48; 0xf7; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,136))) *)
  0x48; 0xf7; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,160))) *)
  0x48; 0x81; 0xc4; 0xd0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 208)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let sha3_keccak_f1600_tmc = define_trimmed "sha3_keccak_f1600_tmc" sha3_keccak_f1600_mc;;

let SHA3_KECCAK_F1600_EXEC = X86_MK_CORE_EXEC_RULE sha3_keccak_f1600_tmc;;

(* ------------------------------------------------------------------------- *)
(* Additional definitions and tactics used in proof.                         *)
(* ------------------------------------------------------------------------- *)

 let WORD_ROL_NOT_SYM = prove
 (`!(x:N word) n. word_rol (word_not x) n = word_not (word_rol x n)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ROL; BIT_WORD_NOT] THEN
  REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
  ASM_SIMP_TAC[TAUT `(p /\ q <=> q) <=> q ==> p`] THEN
  ASM_ARITH_TAC);;

  let WORD_NEG_EL_DEMORGAN = prove(
  `!(p:N word) (q:N word). 
    (word_or p (word_not q)) = word_not(word_and (word_not p) q)`,
    REPEAT GEN_TAC THEN
    WORD_BITWISE_TAC);;

let SHA3_KECCAK_F1600_CORRECT = prove
  (`!rc_pointer:int64 bitstate_in:int64 A pc:num stackpointer:int64.
  nonoverlapping_modulo (2 EXP 64) (pc, 0x66a) (val  stackpointer, 208) /\
  nonoverlapping_modulo (2 EXP 64) (pc, 0x66a) (val bitstate_in, 200) /\
  nonoverlapping_modulo (2 EXP 64) (pc, 0x66a) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val stackpointer, 208) /\
  nonoverlapping_modulo (2 EXP 64) (val stackpointer, 208) (val rc_pointer,192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak_f1600_tmc) /\
              read RIP s = word (pc + 0x11) /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A)
             (\s. read RIP s = word(pc + 0x658) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP; 
                      R8; R9; R10; R11; R12; R13; R14; R15; RDI; RSI] ,, 
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (stackpointer, 208)],,
            MAYCHANGE [memory :> bytes (bitstate_in, 200)])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`rc_pointer:int64`; `bitstate_in:int64`;`A:int64 list`] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `LENGTH(A:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN 
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PAUP_TAC `0` `12` `pc + 0x5d` `pc + 0x62d`
  `\i s.
      (read R8 s = word (2*i) /\
       read RDI s = bitstate_in /\
       read RSP s = stackpointer /\
       read R15 s = stackpointer /\
       read RAX s = (read (memory :> bytes64 (word_add bitstate_in (word 160))) s) /\
       read RBX s = (read (memory :> bytes64 (word_add bitstate_in (word 168))) s) /\
       read RCX s = (read (memory :> bytes64 (word_add bitstate_in (word 176))) s) /\
       read RDX s = (read (memory :> bytes64 (word_add bitstate_in (word 184))) s) /\
       read RBP s = (read (memory :> bytes64 (word_add bitstate_in (word 192))) s) /\
       read RSI s = word_add rc_pointer (word (16 * i)) /\
       wordlist_from_memory(rc_pointer,24) s = round_constants /\
       wordlist_from_memory(bitstate_in,25) s = 
          MAP2 (\(x:bool) (y:(64)word). (if x then (word_not y) else y)) (
          [false; true;  true;  false; false; 
          false; false; false; true;  false; 
          false; false; true;  false; false; 
          false; false; true;  false; false;
          true;  false; false; false; false]) (keccak (2*i) A))  /\
      (read ZF s <=> i = 12)` THEN
  REPEAT CONJ_TAC THENL 
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 25)) s0` THEN

    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    REPEAT CONJ_TAC THENL 
    [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    EXPAND_TAC "A" THEN
    PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * 0 = 0`] THEN
    REWRITE_TAC[keccak] THEN 
    REWRITE_TAC[MAP2]];

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `2 * i`; `2 * i + 1`] THEN
    MP_TAC(WORD_RULE
        `word_add (word (2 * i)) (word 1):int64 = word(2 * i + 1)`) THEN
    DISCH_TAC THEN

    CONV_TAC(RATOR_CONV(LAND_CONV
      (ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THENC
      ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN

    ASM_REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `2 * i`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN 
    REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2] THEN
    REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 25)) s0` THEN
      
    SUBGOAL_THEN
      `read (memory :> bytes64 (word_add rc_pointer (word(8 * i)))) s0 =
      EL i round_constants /\
      read (memory :> bytes64 (word_add rc_pointer (word(2 * 8 * i)))) s0 =
      EL (2 * i) round_constants /\
      read (memory :> bytes64 (word_add rc_pointer (word(16 * i)))) s0 =
      EL (2 * i) round_constants /\
      read (memory :> bytes64 (word_add (word_add rc_pointer (word(16 * i))) (word(8)))) s0 =
      EL (2 * i + 1) round_constants`
    ASSUME_TAC THENL
      [UNDISCH_TAC `i < 12` THEN SPEC_TAC(`i:num`,`i:num`) THEN
       CONV_TAC EXPAND_CASES_CONV THEN
       REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN 
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
       CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
       REWRITE_TAC[];
       ALL_TAC] THEN 

    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--394) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
    [CONV_TAC WORD_RULE;
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`] THEN
      REWRITE_TAC[keccak] THEN 
      FIRST_X_ASSUM(fun th ->
        REWRITE_TAC [SYM th]) THEN
      REWRITE_TAC[keccak_round] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      REWRITE_TAC[round_constants; MAP2] THEN REWRITE_TAC[CONS_11] THEN                    
      REWRITE_TAC[WORD_XOR_NOT;WORD_ROL_NOT_SYM] THEN 
      REWRITE_TAC[WORD_NEG_EL_DEMORGAN;WORD_NOT_NOT] THEN
      REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;

      REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551594):int64 = 
              word_sub x (word 22)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN 
      REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`22 < 2 EXP 64`] THEN
      CONJ_TAC THENL 
      [UNDISCH_TAC `i < 12` 
        THEN ARITH_TAC;
        ARITH_TAC]];

    (*** The trivial loop-back goal ***)
    
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The tail of logical not operation and writeback ***)

    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(RATOR_CONV(LAND_CONV
     (ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THENC
      ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN
    REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2] THEN
    REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_NOT_NOT]]);;

let SHA3_KECCAK_F1600_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A pc:num stackpointer:int64 returnaddress.
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val (word_sub stackpointer (word 256)), 256) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val bitstate_in, 200) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val rc_pointer, 192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val (word_sub stackpointer (word 256)), 264) /\
 nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 256)), 256) (val rc_pointer,192)
 ==> ensures x86
         (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_tmc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 200);
                     memory :> bytes(word_sub stackpointer (word 256),256)])`,
let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_STACK_TAC sha3_keccak_f1600_tmc
    (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_CORRECT)
  `[RBX; RBP; R12; R13; R14; R15]` 256);;

let SHA3_KECCAK_F1600_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A pc:num stackpointer:int64 returnaddress.
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_mc) (val (word_sub stackpointer (word 256)), 256) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_mc) (val bitstate_in, 200) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_mc) (val rc_pointer, 192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val (word_sub stackpointer (word 256)), 264) /\
 nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 256)), 256) (val rc_pointer,192)
 ==> ensures x86
         (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_mc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 200);
                     memory :> bytes(word_sub stackpointer (word 256),256)])`,
let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE 
    (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_NOIBT_SUBROUTINE_CORRECT)));;
