(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;

needs "proofs/mlkem_specs.ml";;
needs "proofs/mlkem_utils.ml";;

(**** print_literal_from_elf "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o";;
 ****)


let poly_basemul_acc_montgomery_cached_k2_mc = define_assert_from_elf
    "poly_basemul_acc_montgomery_cached_k2_mc" "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o"
(*** BYTECODE START ***)
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x5281a02e;       (* arm_MOV W14 (rvalue (word 3329)) *)
  0x4e020dc0;       (* arm_DUP_GEN Q0 X14 16 128 *)
  0x52819fee;       (* arm_MOV W14 (rvalue (word 3327)) *)
  0x4e020dc2;       (* arm_DUP_GEN Q2 X14 16 128 *)
  0x91080024;       (* arm_ADD X4 X1 (rvalue (word 512)) *)
  0x91080045;       (* arm_ADD X5 X2 (rvalue (word 512)) *)
  0x91040066;       (* arm_ADD X6 X3 (rvalue (word 256)) *)
  0xd280020d;       (* arm_MOV X13 (rvalue (word 16)) *)
  0x3cc2042c;       (* arm_LDR Q12 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0029;       (* arm_LDR Q9 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20456;       (* arm_LDR Q22 X2 (Postimmediate_Offset (word 32)) *)
  0x3cdf005e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204a6;       (* arm_LDR Q6 X5 (Postimmediate_Offset (word 32)) *)
  0x3dc00487;       (* arm_LDR Q7 X4 (Immediate_Offset (word 16)) *)
  0x3cc20488;       (* arm_LDR Q8 X4 (Postimmediate_Offset (word 32)) *)
  0x3cdf00b7;       (* arm_LDR Q23 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e491990;       (* arm_UZP1 Q16 Q12 Q9 16 *)
  0x4e49598e;       (* arm_UZP2 Q14 Q12 Q9 16 *)
  0x4e5e5acd;       (* arm_UZP2 Q13 Q22 Q30 16 *)
  0x4e5e1ad2;       (* arm_UZP1 Q18 Q22 Q30 16 *)
  0x4cdf747b;       (* arm_LDR Q27 X3 (Postimmediate_Offset (word 16)) *)
  0x4cdf74d1;       (* arm_LDR Q17 X6 (Postimmediate_Offset (word 16)) *)
  0x4e72c204;       (* arm_SMULL2_VEC Q4 Q16 Q18 16 *)
  0x3dc0043f;       (* arm_LDR Q31 X1 (Immediate_Offset (word 16)) *)
  0x0e6dc213;       (* arm_SMULL_VEC Q19 Q16 Q13 16 *)
  0x3cc20438;       (* arm_LDR Q24 X1 (Postimmediate_Offset (word 32)) *)
  0x0e7281d3;       (* arm_SMLAL_VEC Q19 Q14 Q18 16 *)
  0x3cc20456;       (* arm_LDR Q22 X2 (Postimmediate_Offset (word 32)) *)
  0x4e7b81c4;       (* arm_SMLAL2_VEC Q4 Q14 Q27 16 *)
  0x4e5758c5;       (* arm_UZP2 Q5 Q6 Q23 16 *)
  0x4e6dc21d;       (* arm_SMULL2_VEC Q29 Q16 Q13 16 *)
  0x4e47591a;       (* arm_UZP2 Q26 Q8 Q7 16 *)
  0x4e7281dd;       (* arm_SMLAL2_VEC Q29 Q14 Q18 16 *)
  0x4e5f1b1e;       (* arm_UZP1 Q30 Q24 Q31 16 *)
  0x4e471908;       (* arm_UZP1 Q8 Q8 Q7 16 *)
  0x0e72c20b;       (* arm_SMULL_VEC Q11 Q16 Q18 16 *)
  0x0e7b81cb;       (* arm_SMLAL_VEC Q11 Q14 Q27 16 *)
  0x3cdf0041;       (* arm_LDR Q1 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e5718dc;       (* arm_UZP1 Q28 Q6 Q23 16 *)
  0x4e65811d;       (* arm_SMLAL2_VEC Q29 Q8 Q5 16 *)
  0x3cc204b9;       (* arm_LDR Q25 X5 (Postimmediate_Offset (word 32)) *)
  0x0e658113;       (* arm_SMLAL_VEC Q19 Q8 Q5 16 *)
  0x3dc00483;       (* arm_LDR Q3 X4 (Immediate_Offset (word 16)) *)
  0x4e7c835d;       (* arm_SMLAL2_VEC Q29 Q26 Q28 16 *)
  0x4e411adb;       (* arm_UZP1 Q27 Q22 Q1 16 *)
  0x0e7c8353;       (* arm_SMLAL_VEC Q19 Q26 Q28 16 *)
  0x3cc2048c;       (* arm_LDR Q12 X4 (Postimmediate_Offset (word 32)) *)
  0x4e7c8104;       (* arm_SMLAL2_VEC Q4 Q8 Q28 16 *)
  0x3cdf00b5;       (* arm_LDR Q21 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e718344;       (* arm_SMLAL2_VEC Q4 Q26 Q17 16 *)
  0x0e7c810b;       (* arm_SMLAL_VEC Q11 Q8 Q28 16 *)
  0x4cdf74cf;       (* arm_LDR Q15 X6 (Postimmediate_Offset (word 16)) *)
  0x0e71834b;       (* arm_SMLAL_VEC Q11 Q26 Q17 16 *)
  0x4cdf7474;       (* arm_LDR Q20 X3 (Postimmediate_Offset (word 16)) *)
  0x4e5d1a7c;       (* arm_UZP1 Q28 Q19 Q29 16 *)
  0x4e7bc3d7;       (* arm_SMULL2_VEC Q23 Q30 Q27 16 *)
  0x0e7bc3da;       (* arm_SMULL_VEC Q26 Q30 Q27 16 *)
  0x4e415ad0;       (* arm_UZP2 Q16 Q22 Q1 16 *)
  0x4e629f9c;       (* arm_MUL_VEC Q28 Q28 Q2 16 128 *)
  0x4e44196a;       (* arm_UZP1 Q10 Q11 Q4 16 *)
  0x4e70c3c8;       (* arm_SMULL2_VEC Q8 Q30 Q16 16 *)
  0x4e629d4d;       (* arm_MUL_VEC Q13 Q10 Q2 16 128 *)
  0x0e608393;       (* arm_SMLAL_VEC Q19 Q28 Q0 16 *)
  0x4e60839d;       (* arm_SMLAL2_VEC Q29 Q28 Q0 16 *)
  0x0e70c3d2;       (* arm_SMULL_VEC Q18 Q30 Q16 16 *)
  0x4e551b3e;       (* arm_UZP1 Q30 Q25 Q21 16 *)
  0x0e6081ab;       (* arm_SMLAL_VEC Q11 Q13 Q0 16 *)
  0x4e5f5b06;       (* arm_UZP2 Q6 Q24 Q31 16 *)
  0x4e431990;       (* arm_UZP1 Q16 Q12 Q3 16 *)
  0x4e6081a4;       (* arm_SMLAL2_VEC Q4 Q13 Q0 16 *)
  0x4e555b31;       (* arm_UZP2 Q17 Q25 Q21 16 *)
  0x4e7b80c8;       (* arm_SMLAL2_VEC Q8 Q6 Q27 16 *)
  0x4e43598c;       (* arm_UZP2 Q12 Q12 Q3 16 *)
  0x0e7b80d2;       (* arm_SMLAL_VEC Q18 Q6 Q27 16 *)
  0x4e5d5a69;       (* arm_UZP2 Q9 Q19 Q29 16 *)
  0x4e718208;       (* arm_SMLAL2_VEC Q8 Q16 Q17 16 *)
  0x4e7e8188;       (* arm_SMLAL2_VEC Q8 Q12 Q30 16 *)
  0x4e445973;       (* arm_UZP2 Q19 Q11 Q4 16 *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x0e718212;       (* arm_SMLAL_VEC Q18 Q16 Q17 16 *)
  0x3cc20487;       (* arm_LDR Q7 X4 (Postimmediate_Offset (word 32)) *)
  0x3dc0044a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 16)) *)
  0x0e7e8192;       (* arm_SMLAL_VEC Q18 Q12 Q30 16 *)
  0x4e7480d7;       (* arm_SMLAL2_VEC Q23 Q6 Q20 16 *)
  0x3cc2044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 32)) *)
  0x4e7e8217;       (* arm_SMLAL2_VEC Q23 Q16 Q30 16 *)
  0x4e493a79;       (* arm_ZIP1 Q25 Q19 Q9 16 128 *)
  0x4e497a63;       (* arm_ZIP2 Q3 Q19 Q9 16 128 *)
  0x4e6f8197;       (* arm_SMLAL2_VEC Q23 Q12 Q15 16 *)
  0x0e7480da;       (* arm_SMLAL_VEC Q26 Q6 Q20 16 *)
  0x4e481a45;       (* arm_UZP1 Q5 Q18 Q8 16 *)
  0x4e4a59d5;       (* arm_UZP2 Q21 Q14 Q10 16 *)
  0x0e7e821a;       (* arm_SMLAL_VEC Q26 Q16 Q30 16 *)
  0x3c820419;       (* arm_STR Q25 X0 (Postimmediate_Offset (word 32)) *)
  0x4e629cbd;       (* arm_MUL_VEC Q29 Q5 Q2 16 128 *)
  0x4e4a19d8;       (* arm_UZP1 Q24 Q14 Q10 16 *)
  0x3c9f0003;       (* arm_STR Q3 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e6f819a;       (* arm_SMLAL_VEC Q26 Q12 Q15 16 *)
  0x4cdf74cf;       (* arm_LDR Q15 X6 (Postimmediate_Offset (word 16)) *)
  0x3dc0043c;       (* arm_LDR Q28 X1 (Immediate_Offset (word 16)) *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc204ad;       (* arm_LDR Q13 X5 (Postimmediate_Offset (word 32)) *)
  0x3cdf009b;       (* arm_LDR Q27 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e6083a8;       (* arm_SMLAL2_VEC Q8 Q29 Q0 16 *)
  0x3cdf00b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e6083b2;       (* arm_SMLAL_VEC Q18 Q29 Q0 16 *)
  0x4e571b44;       (* arm_UZP1 Q4 Q26 Q23 16 *)
  0x4e5c1961;       (* arm_UZP1 Q1 Q11 Q28 16 *)
  0x4e5c5966;       (* arm_UZP2 Q6 Q11 Q28 16 *)
  0x4e5b18f0;       (* arm_UZP1 Q16 Q7 Q27 16 *)
  0x4e629c9f;       (* arm_MUL_VEC Q31 Q4 Q2 16 128 *)
  0x4e5659b1;       (* arm_UZP2 Q17 Q13 Q22 16 *)
  0x4cdf7474;       (* arm_LDR Q20 X3 (Postimmediate_Offset (word 16)) *)
  0x4e485a49;       (* arm_UZP2 Q9 Q18 Q8 16 *)
  0x4e75c028;       (* arm_SMULL2_VEC Q8 Q1 Q21 16 *)
  0x4e5619be;       (* arm_UZP1 Q30 Q13 Q22 16 *)
  0x4e7880c8;       (* arm_SMLAL2_VEC Q8 Q6 Q24 16 *)
  0x4e718208;       (* arm_SMLAL2_VEC Q8 Q16 Q17 16 *)
  0x4e5b58ec;       (* arm_UZP2 Q12 Q7 Q27 16 *)
  0x0e6083fa;       (* arm_SMLAL_VEC Q26 Q31 Q0 16 *)
  0x4e6083f7;       (* arm_SMLAL2_VEC Q23 Q31 Q0 16 *)
  0x0e75c032;       (* arm_SMULL_VEC Q18 Q1 Q21 16 *)
  0x0e7880d2;       (* arm_SMLAL_VEC Q18 Q6 Q24 16 *)
  0x4e7e8188;       (* arm_SMLAL2_VEC Q8 Q12 Q30 16 *)
  0x4e575b53;       (* arm_UZP2 Q19 Q26 Q23 16 *)
  0x4e78c037;       (* arm_SMULL2_VEC Q23 Q1 Q24 16 *)
  0x0e78c03a;       (* arm_SMULL_VEC Q26 Q1 Q24 16 *)
  0xf10005ad;       (* arm_SUBS X13 X13 (rvalue (word 1)) *)
  0xb5fff9ed;       (* arm_CBNZ X13 (word 2096956) *)
  0x0e7480da;       (* arm_SMLAL_VEC Q26 Q6 Q20 16 *)
  0x4e7480d7;       (* arm_SMLAL2_VEC Q23 Q6 Q20 16 *)
  0x0e7e821a;       (* arm_SMLAL_VEC Q26 Q16 Q30 16 *)
  0x4e7e8217;       (* arm_SMLAL2_VEC Q23 Q16 Q30 16 *)
  0x0e6f819a;       (* arm_SMLAL_VEC Q26 Q12 Q15 16 *)
  0x4e6f8197;       (* arm_SMLAL2_VEC Q23 Q12 Q15 16 *)
  0x0e718212;       (* arm_SMLAL_VEC Q18 Q16 Q17 16 *)
  0x0e7e8192;       (* arm_SMLAL_VEC Q18 Q12 Q30 16 *)
  0x4e493a6c;       (* arm_ZIP1 Q12 Q19 Q9 16 128 *)
  0x3c82040c;       (* arm_STR Q12 X0 (Postimmediate_Offset (word 32)) *)
  0x4e571b4c;       (* arm_UZP1 Q12 Q26 Q23 16 *)
  0x4e629d86;       (* arm_MUL_VEC Q6 Q12 Q2 16 128 *)
  0x4e481a4c;       (* arm_UZP1 Q12 Q18 Q8 16 *)
  0x4e629d8c;       (* arm_MUL_VEC Q12 Q12 Q2 16 128 *)
  0x0e6080da;       (* arm_SMLAL_VEC Q26 Q6 Q0 16 *)
  0x4e6080d7;       (* arm_SMLAL2_VEC Q23 Q6 Q0 16 *)
  0x4e608188;       (* arm_SMLAL2_VEC Q8 Q12 Q0 16 *)
  0x0e608192;       (* arm_SMLAL_VEC Q18 Q12 Q0 16 *)
  0x4e497a6c;       (* arm_ZIP2 Q12 Q19 Q9 16 128 *)
  0x4e575b46;       (* arm_UZP2 Q6 Q26 Q23 16 *)
  0x3c9f000c;       (* arm_STR Q12 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e485a4c;       (* arm_UZP2 Q12 Q18 Q8 16 *)
  0x4e4c78c1;       (* arm_ZIP2 Q1 Q6 Q12 16 128 *)
  0x4e4c38cc;       (* arm_ZIP1 Q12 Q6 Q12 16 128 *)
  0x3d800401;       (* arm_STR Q1 X0 (Immediate_Offset (word 16)) *)
  0x3c82040c;       (* arm_STR Q12 X0 (Postimmediate_Offset (word 32)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc2 = define
    `pmull_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
      pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc2 = define
    `pmul_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
     (&(inverse_mod 3329 65536) *
      pmull_acc2 x00 x01 y00 y01 x10 x11 y10 y11) rem &3329`;;

let basemul2_even = define
   `basemul2_even x0 y0 y0t x1 y1 y1t = \i.
      pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
                (y0 (2 * i)) (y0t i)
                (x1 (2 * i)) (x1 (2 * i + 1))
                (y1 (2 * i)) (y1t i)
   `;;

let basemul2_odd = define
 `basemul2_odd x0 y0 x1 y1 = \i.
    pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i + 1)) (y0 (2 * i))
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i + 1)) (y1 (2 * i))
 `;;

let poly_basemul_acc_montgomery_cached_k2_EXEC = ARM_MK_EXEC_RULE poly_basemul_acc_montgomery_cached_k2_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_MC =
  REWRITE_CONV[poly_basemul_acc_montgomery_cached_k2_mc] `LENGTH poly_basemul_acc_montgomery_cached_k2_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_PREAMBLE_LENGTH = new_definition
  `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_PREAMBLE_LENGTH = 20`;;

let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_POSTAMBLE_LENGTH = new_definition
  `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_POSTAMBLE_LENGTH = 24`;;

let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_START = new_definition
  `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_START = POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_PREAMBLE_LENGTH`;;

let POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_END = new_definition
  `POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_END = LENGTH poly_basemul_acc_montgomery_cached_k2_mc - POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_MC;
              POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_START; POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_END;
              POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_PREAMBLE_LENGTH; POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Hacky tweaking conversion to write away non-free state component reads.   *)
(* ------------------------------------------------------------------------- *)

let lemma = prove
 (`!base size s n.
        n + 2 <= size
        ==> read(memory :> bytes16(word_add base (word n))) s =
            word((read (memory :> bytes(base,size)) s DIV 2 EXP (8 * n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SPEC_TAC(`read memory s`,`m:int64->byte`) THEN GEN_TAC THEN
  REWRITE_TAC[READ_BYTES_DIV] THEN
  REWRITE_TAC[bytes16; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_16] THEN
  REWRITE_TAC[ARITH_RULE `16 = 8 * 2`; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `n + 2 <= size ==> MIN (size - n) 2 = MIN 2 2`]);;

let BOUNDED_QUANT_READ_MEM = prove
 (`(!x base s.
     (!i. i < n
          ==> read(memory :> bytes16(word_add base (word(2 * i)))) s =
              x i) <=>
     (!i. i < n
          ==> word((read(memory :> bytes(base,2 * n)) s DIV 2 EXP (16 * i))) =
              x i)) /\
   (!x p base s.
     (!i. i < n
          ==> (ival(read(memory :> bytes16(word_add base (word(2 * i)))) s) ==
               x i) (mod p)) <=>
     (!i. i < n
          ==> (ival(word((read(memory :> bytes(base,2 * n)) s DIV 2 EXP (16 * i))):int16) ==
               x i) (mod p))) /\
   (!x p c base s.
     (!i. i < n /\ c i
          ==> (ival(read(memory :> bytes16(word_add base (word(2 * i)))) s) ==
               x i) (mod p)) <=>
     (!i. i < n /\ c i
          ==> (ival(word((read(memory :> bytes(base,2 * n)) s DIV 2 EXP (16 * i))):int16) ==
               x i) (mod p)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`base:int64`; `2 * n`] lemma) THEN
  SIMP_TAC[ARITH_RULE `2 * i + 2 <= 2 * n <=> i < n`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * i = 16 * i`]);;

let even_odd_split_lemma = prove
 (`(!i. i < 128 ==> P (4 * i) i /\ Q(4 * i + 2) i) <=>
   (!i. i < 256 /\ EVEN i ==> P(2 * i) (i DIV 2)) /\
   (!i. i < 256 /\ ODD i ==> Q(2 * i) (i DIV 2))`,
  REWRITE_TAC[IMP_CONJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let TWEAK_CONV =
  REWRITE_CONV[even_odd_split_lemma] THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_RULE
    `word_add x (word(a + b)) = word_add (word_add x (word a)) (word b)`] THENC
  REWRITE_CONV[BOUNDED_QUANT_READ_MEM] THENC
  NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let poly_basemul_acc_montgomery_cached_k2_GOAL = `forall srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc.
     ALL (nonoverlapping (dst, 512))
         [(word pc, LENGTH poly_basemul_acc_montgomery_cached_k2_mc); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) poly_basemul_acc_montgomery_cached_k2_mc /\
            read PC s = word (pc + POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_START)  /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (2 * i)))) s = x0 i)       /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (2 * i)))) s = y0 i)       /\
            (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (2 * i)))) s = y0t i)      /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read PC s = word (pc + POLY_BASEMUL_ACC_MONTGOMERY_CACHED_K2_CORE_END) /\
            ((!i. i < 256 ==> abs(ival(x0 i)) <= &2 pow 12 /\  abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16(word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t) i) (mod &3329) /\
                          (ival(read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1) (ival o y1) i) (mod &3329))))
       // Register and memory footprint
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])
   `;;

 (* ------------------------------------------------------------------------- *)
 (* Proof                                                                     *)
 (* ------------------------------------------------------------------------- *)

let poly_basemul_acc_montgomery_cached_k2_SPEC = prove(poly_basemul_acc_montgomery_cached_k2_GOAL,
     CONV_TAC LENGTH_SIMPLIFY_CONV THEN
     REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
       MODIFIABLE_SIMD_REGS;
       NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst poly_basemul_acc_montgomery_cached_k2_EXEC] THEN
     REPEAT STRIP_TAC THEN

     (* Split quantified assumptions into separate cases *)
     CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
     CONV_TAC((ONCE_DEPTH_CONV NUM_MULT_CONV) THENC (ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN

     (* Initialize symbolic execution *)
     ENSURES_INIT_TAC "s0" THEN

     (* Rewrite memory-read assumptions from 16-bit granularity
      * to 128-bit granularity. *)
     MEMORY_128_FROM_16_TAC "srcA" 64 THEN
     MEMORY_128_FROM_16_TAC "srcB" 64 THEN
     MEMORY_128_FROM_16_TAC "srcBt" 32 THEN
     ASM_REWRITE_TAC [WORD_ADD_0] THEN
     (* Forget original shape of assumption *)
     DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcA) s = x`] THEN
     DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcB) s = x`] THEN
     DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 srcBt) s = x`] THEN

     (* Symbolic execution
        Note that we simplify eagerly after every step.
        This reduces the proof time *)
     REPEAT STRIP_TAC THEN
     MAP_UNTIL_TARGET_PC (fun n -> ARM_STEPS_TAC poly_basemul_acc_montgomery_cached_k2_EXEC [n] THEN
                (SIMD_SIMPLIFY_TAC [montred])) 1 THEN

     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN STRIP_TAC THEN
     REPEAT CONJ_TAC THEN
     ASM_REWRITE_TAC [] THEN

     (* Reverse restructuring *)
     REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
       CONV_RULE (SIMD_SIMPLIFY_CONV []) o
       CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
       check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

     (* Split quantified post-condition into separate cases *)
     CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV
              THENC (TRY_CONV (ONCE_DEPTH_CONV NUM_ADD_CONV))) THEN
     CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
     ASM_REWRITE_TAC [WORD_ADD_0] THEN

     (* Forget all state-related assumptions, but keep bounds at least *)
     DISCARD_STATE_TAC "s805" THEN

     (* Split into one congruence goals per index. *)
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[basemul2_even; basemul2_odd;
                 pmul_acc2; pmull_acc2; pmull; o_THM] THEN
     CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN

     (* Solve the congruence goals *)

    ASSUM_LIST((fun ths -> W(MP_TAC o CONJUNCT1 o GEN_CONGBOUND_RULE ths o
      rand o lhand o rator o snd))) THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC INT_RING
);;

(* NOTE: This needs to be kept in sync with the CBMC spec in
 * mlkem/native/aarch64/src/arith_native_aarch64.h *)
let poly_basemul_acc_montgomery_cached_k2_SPEC' = prove(
   `forall srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc returnaddress stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(dst, 512); (word_sub stackpointer (word 64),64)]
        [(word pc, LENGTH poly_basemul_acc_montgomery_cached_k2_mc); (srcA, 1024); (srcB, 1024); (srcBt, 512)] /\
      nonoverlapping (dst,512) (word_sub stackpointer (word 64),64)
      ==>
      ensures arm
      (\s. // Assert that poly_basemul_acc_montgomery_cached_k2 is loaded at PC
        aligned_bytes_loaded s (word pc) poly_basemul_acc_montgomery_cached_k2_mc /\
        read PC s = word pc /\
        read SP s = stackpointer /\
        read X30 s = returnaddress /\
        C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
        // Give names to in-memory data to be
        // able to refer to them in the post-condition
        (!i. i < 256 ==> read(memory :> bytes16(word_add srcA (word (2 * i)))) s = x0 i) /\
        (!i. i < 256 ==> read(memory :> bytes16(word_add srcB (word (2 * i)))) s = y0 i) /\
        (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (2 * i)))) s = y0t i) /\
        (!i. i < 256 ==> read(memory :> bytes16(word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
        (!i. i < 256 ==> read(memory :> bytes16(word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
        (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (256 + 2 * i)))) s = y1t i)
      )
      (\s. read PC s = returnaddress /\
           ((!i. i < 256 ==> abs(ival(x0 i)) <= &2 pow 12 /\  abs(ival(x1 i)) <= &2 pow 12)
            ==>  (!i. i < 128
                      ==> (ival(read(memory :> bytes16(word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t) i) (mod &3329) /\
                          (ival(read(memory :> bytes16(word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1) (ival o y1) i) (mod &3329)))
      )
      // Register and memory footprint
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(dst, 512);
                 memory :> bytes(word_sub stackpointer (word 64),64)])`,
  REWRITE_TAC[fst poly_basemul_acc_montgomery_cached_k2_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) poly_basemul_acc_montgomery_cached_k2_EXEC
     (REWRITE_RULE[fst poly_basemul_acc_montgomery_cached_k2_EXEC] (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV poly_basemul_acc_montgomery_cached_k2_SPEC)))
      `[D8; D9; D10; D11; D12; D13; D14; D15]` 64  THEN
   WORD_ARITH_TAC)
;;
