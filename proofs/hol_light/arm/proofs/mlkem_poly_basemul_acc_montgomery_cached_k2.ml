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
  0x3dc00439;       (* arm_LDR Q25 X1 (Immediate_Offset (word 16)) *)
  0x3cc20426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc2044c;       (* arm_LDR Q12 X2 (Postimmediate_Offset (word 32)) *)
  0x3cdf0054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc20487;       (* arm_LDR Q7 X4 (Postimmediate_Offset (word 32)) *)
  0x3cdf008a;       (* arm_LDR Q10 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204ae;       (* arm_LDR Q14 X5 (Postimmediate_Offset (word 32)) *)
  0x3cdf00bd;       (* arm_LDR Q29 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e5918d8;       (* arm_UZP1 Q24 Q6 Q25 16 *)
  0x4cdf7470;       (* arm_LDR Q16 X3 (Postimmediate_Offset (word 16)) *)
  0x4e54599e;       (* arm_UZP2 Q30 Q12 Q20 16 *)
  0x4e54198c;       (* arm_UZP1 Q12 Q12 Q20 16 *)
  0x4cdf74d4;       (* arm_LDR Q20 X6 (Postimmediate_Offset (word 16)) *)
  0x4e5958d2;       (* arm_UZP2 Q18 Q6 Q25 16 *)
  0x4e5d19d6;       (* arm_UZP1 Q22 Q14 Q29 16 *)
  0x4e6cc308;       (* arm_SMULL2_VEC Q8 Q24 Q12 16 *)
  0x4e4a18e4;       (* arm_UZP1 Q4 Q7 Q10 16 *)
  0x0e6cc30f;       (* arm_SMULL_VEC Q15 Q24 Q12 16 *)
  0x0e70824f;       (* arm_SMLAL_VEC Q15 Q18 Q16 16 *)
  0x3dc0042d;       (* arm_LDR Q13 X1 (Immediate_Offset (word 16)) *)
  0x0e7ec319;       (* arm_SMULL_VEC Q25 Q24 Q30 16 *)
  0x4e5d59db;       (* arm_UZP2 Q27 Q14 Q29 16 *)
  0x4e7ec30b;       (* arm_SMULL2_VEC Q11 Q24 Q30 16 *)
  0x4e4a58e1;       (* arm_UZP2 Q1 Q7 Q10 16 *)
  0x4e708248;       (* arm_SMLAL2_VEC Q8 Q18 Q16 16 *)
  0x4e6c824b;       (* arm_SMLAL2_VEC Q11 Q18 Q12 16 *)
  0x3cc20427;       (* arm_LDR Q7 X1 (Postimmediate_Offset (word 32)) *)
  0x4e768088;       (* arm_SMLAL2_VEC Q8 Q4 Q22 16 *)
  0x3cc2044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 32)) *)
  0x0e76808f;       (* arm_SMLAL_VEC Q15 Q4 Q22 16 *)
  0x3cdf0058;       (* arm_LDR Q24 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e748028;       (* arm_SMLAL2_VEC Q8 Q1 Q20 16 *)
  0x3dc00489;       (* arm_LDR Q9 X4 (Immediate_Offset (word 16)) *)
  0x4e7b808b;       (* arm_SMLAL2_VEC Q11 Q4 Q27 16 *)
  0x4e4d18e5;       (* arm_UZP1 Q5 Q7 Q13 16 *)
  0x0e74802f;       (* arm_SMLAL_VEC Q15 Q1 Q20 16 *)
  0x3cc204b5;       (* arm_LDR Q21 X5 (Postimmediate_Offset (word 32)) *)
  0x0e6c8259;       (* arm_SMLAL_VEC Q25 Q18 Q12 16 *)
  0x4e4d58f4;       (* arm_UZP2 Q20 Q7 Q13 16 *)
  0x0e7b8099;       (* arm_SMLAL_VEC Q25 Q4 Q27 16 *)
  0x4cdf747f;       (* arm_LDR Q31 X3 (Postimmediate_Offset (word 16)) *)
  0x0e768039;       (* arm_SMLAL_VEC Q25 Q1 Q22 16 *)
  0x4e5819dc;       (* arm_UZP1 Q28 Q14 Q24 16 *)
  0x4e76802b;       (* arm_SMLAL2_VEC Q11 Q1 Q22 16 *)
  0x4e4819ec;       (* arm_UZP1 Q12 Q15 Q8 16 *)
  0x3cc20486;       (* arm_LDR Q6 X4 (Postimmediate_Offset (word 32)) *)
  0x0e7cc0ba;       (* arm_SMULL_VEC Q26 Q5 Q28 16 *)
  0x4e629d92;       (* arm_MUL_VEC Q18 Q12 Q2 16 128 *)
  0x3cdf00b1;       (* arm_LDR Q17 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e4b1b21;       (* arm_UZP1 Q1 Q25 Q11 16 *)
  0x4e7cc0b7;       (* arm_SMULL2_VEC Q23 Q5 Q28 16 *)
  0x4e7f8297;       (* arm_SMLAL2_VEC Q23 Q20 Q31 16 *)
  0x4e629c2a;       (* arm_MUL_VEC Q10 Q1 Q2 16 128 *)
  0x4e511abe;       (* arm_UZP1 Q30 Q21 Q17 16 *)
  0x4e4918d0;       (* arm_UZP1 Q16 Q6 Q9 16 *)
  0x0e60824f;       (* arm_SMLAL_VEC Q15 Q18 Q0 16 *)
  0x4cdf74c3;       (* arm_LDR Q3 X6 (Postimmediate_Offset (word 16)) *)
  0x4e7e8217;       (* arm_SMLAL2_VEC Q23 Q16 Q30 16 *)
  0x4e608248;       (* arm_SMLAL2_VEC Q8 Q18 Q0 16 *)
  0x0e608159;       (* arm_SMLAL_VEC Q25 Q10 Q0 16 *)
  0x4e4958cc;       (* arm_UZP2 Q12 Q6 Q9 16 *)
  0x0e7f829a;       (* arm_SMLAL_VEC Q26 Q20 Q31 16 *)
  0x4e60814b;       (* arm_SMLAL2_VEC Q11 Q10 Q0 16 *)
  0x4e638197;       (* arm_SMLAL2_VEC Q23 Q12 Q3 16 *)
  0x4e4859ed;       (* arm_UZP2 Q13 Q15 Q8 16 *)
  0x4e5859dd;       (* arm_UZP2 Q29 Q14 Q24 16 *)
  0x0e7e821a;       (* arm_SMLAL_VEC Q26 Q16 Q30 16 *)
  0x4e515ab1;       (* arm_UZP2 Q17 Q21 Q17 16 *)
  0x0e63819a;       (* arm_SMLAL_VEC Q26 Q12 Q3 16 *)
  0x4e4b5b33;       (* arm_UZP2 Q19 Q25 Q11 16 *)
  0x0e7dc0b2;       (* arm_SMULL_VEC Q18 Q5 Q29 16 *)
  0x0e7c8292;       (* arm_SMLAL_VEC Q18 Q20 Q28 16 *)
  0x0e718212;       (* arm_SMLAL_VEC Q18 Q16 Q17 16 *)
  0x4e5379aa;       (* arm_ZIP2 Q10 Q13 Q19 16 128 *)
  0x4e571b43;       (* arm_UZP1 Q3 Q26 Q23 16 *)
  0x0e7e8192;       (* arm_SMLAL_VEC Q18 Q12 Q30 16 *)
  0x4e7dc0a8;       (* arm_SMULL2_VEC Q8 Q5 Q29 16 *)
  0x3d80040a;       (* arm_STR Q10 X0 (Immediate_Offset (word 16)) *)
  0x4e5339b9;       (* arm_ZIP1 Q25 Q13 Q19 16 128 *)
  0x4e629c6f;       (* arm_MUL_VEC Q15 Q3 Q2 16 128 *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x3dc00436;       (* arm_LDR Q22 X1 (Immediate_Offset (word 16)) *)
  0x3cc2042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc2044e;       (* arm_LDR Q14 X2 (Postimmediate_Offset (word 32)) *)
  0x4e7c8288;       (* arm_SMLAL2_VEC Q8 Q20 Q28 16 *)
  0x3cdf0044;       (* arm_LDR Q4 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e718208;       (* arm_SMLAL2_VEC Q8 Q16 Q17 16 *)
  0x3dc00498;       (* arm_LDR Q24 X4 (Immediate_Offset (word 16)) *)
  0x4e7e8188;       (* arm_SMLAL2_VEC Q8 Q12 Q30 16 *)
  0x4e561973;       (* arm_UZP1 Q19 Q11 Q22 16 *)
  0x3cc20487;       (* arm_LDR Q7 X4 (Postimmediate_Offset (word 32)) *)
  0x3cc204ad;       (* arm_LDR Q13 X5 (Postimmediate_Offset (word 32)) *)
  0x3cdf00b1;       (* arm_LDR Q17 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e565974;       (* arm_UZP2 Q20 Q11 Q22 16 *)
  0x0e6081fa;       (* arm_SMLAL_VEC Q26 Q15 Q0 16 *)
  0x4e6081f7;       (* arm_SMLAL2_VEC Q23 Q15 Q0 16 *)
  0x4e481a45;       (* arm_UZP1 Q5 Q18 Q8 16 *)
  0x4cdf747b;       (* arm_LDR Q27 X3 (Postimmediate_Offset (word 16)) *)
  0x4e4419dc;       (* arm_UZP1 Q28 Q14 Q4 16 *)
  0x4e629cab;       (* arm_MUL_VEC Q11 Q5 Q2 16 128 *)
  0x4e5119be;       (* arm_UZP1 Q30 Q13 Q17 16 *)
  0x4e5818f0;       (* arm_UZP1 Q16 Q7 Q24 16 *)
  0x4cdf74cf;       (* arm_LDR Q15 X6 (Postimmediate_Offset (word 16)) *)
  0x4e575b56;       (* arm_UZP2 Q22 Q26 Q23 16 *)
  0x4e7cc277;       (* arm_SMULL2_VEC Q23 Q19 Q28 16 *)
  0x4e7b8297;       (* arm_SMLAL2_VEC Q23 Q20 Q27 16 *)
  0x4e5159b1;       (* arm_UZP2 Q17 Q13 Q17 16 *)
  0x4e5858ec;       (* arm_UZP2 Q12 Q7 Q24 16 *)
  0x4e7e8217;       (* arm_SMLAL2_VEC Q23 Q16 Q30 16 *)
  0x4e4459df;       (* arm_UZP2 Q31 Q14 Q4 16 *)
  0x0e608172;       (* arm_SMLAL_VEC Q18 Q11 Q0 16 *)
  0x0e7cc27a;       (* arm_SMULL_VEC Q26 Q19 Q28 16 *)
  0x0e7b829a;       (* arm_SMLAL_VEC Q26 Q20 Q27 16 *)
  0x4e608168;       (* arm_SMLAL2_VEC Q8 Q11 Q0 16 *)
  0x4e6f8197;       (* arm_SMLAL2_VEC Q23 Q12 Q15 16 *)
  0x0e7e821a;       (* arm_SMLAL_VEC Q26 Q16 Q30 16 *)
  0x0e6f819a;       (* arm_SMLAL_VEC Q26 Q12 Q15 16 *)
  0x3c820419;       (* arm_STR Q25 X0 (Postimmediate_Offset (word 32)) *)
  0x4e485a49;       (* arm_UZP2 Q9 Q18 Q8 16 *)
  0x0e7fc272;       (* arm_SMULL_VEC Q18 Q19 Q31 16 *)
  0x0e7c8292;       (* arm_SMLAL_VEC Q18 Q20 Q28 16 *)
  0x0e718212;       (* arm_SMLAL_VEC Q18 Q16 Q17 16 *)
  0x4e497ac3;       (* arm_ZIP2 Q3 Q22 Q9 16 128 *)
  0x4e571b5d;       (* arm_UZP1 Q29 Q26 Q23 16 *)
  0x0e7e8192;       (* arm_SMLAL_VEC Q18 Q12 Q30 16 *)
  0x4e7fc268;       (* arm_SMULL2_VEC Q8 Q19 Q31 16 *)
  0x3d800403;       (* arm_STR Q3 X0 (Immediate_Offset (word 16)) *)
  0x4e493ad9;       (* arm_ZIP1 Q25 Q22 Q9 16 128 *)
  0x4e629faf;       (* arm_MUL_VEC Q15 Q29 Q2 16 128 *)
  0xf10005ad;       (* arm_SUBS X13 X13 (rvalue (word 1)) *)
  0xb5fff9ed;       (* arm_CBNZ X13 (word 2096956) *)
  0x3c820419;       (* arm_STR Q25 X0 (Postimmediate_Offset (word 32)) *)
  0x4e7c8288;       (* arm_SMLAL2_VEC Q8 Q20 Q28 16 *)
  0x4e718208;       (* arm_SMLAL2_VEC Q8 Q16 Q17 16 *)
  0x4e7e8188;       (* arm_SMLAL2_VEC Q8 Q12 Q30 16 *)
  0x4e6081f7;       (* arm_SMLAL2_VEC Q23 Q15 Q0 16 *)
  0x0e6081fa;       (* arm_SMLAL_VEC Q26 Q15 Q0 16 *)
  0x4e481a4c;       (* arm_UZP1 Q12 Q18 Q8 16 *)
  0x4e575b4f;       (* arm_UZP2 Q15 Q26 Q23 16 *)
  0x4e629d8c;       (* arm_MUL_VEC Q12 Q12 Q2 16 128 *)
  0x0e608192;       (* arm_SMLAL_VEC Q18 Q12 Q0 16 *)
  0x4e608188;       (* arm_SMLAL2_VEC Q8 Q12 Q0 16 *)
  0x4e485a5e;       (* arm_UZP2 Q30 Q18 Q8 16 *)
  0x4e5e39ec;       (* arm_ZIP1 Q12 Q15 Q30 16 128 *)
  0x4e5e79f3;       (* arm_ZIP2 Q19 Q15 Q30 16 128 *)
  0x3c82040c;       (* arm_STR Q12 X0 (Postimmediate_Offset (word 32)) *)
  0x3c9f0013;       (* arm_STR Q19 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

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
            read PC s = word (pc + 20)  /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (2 * i)))) s = x0 i)       /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (2 * i)))) s = y0 i)       /\
            (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (2 * i)))) s = y0t i)      /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcA  (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256 ==> read(memory :> bytes16(word_add srcB  (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128 ==> read(memory :> bytes16(word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read PC s = word (pc + 640) /\
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
     MAP_EVERY (fun n -> ARM_STEPS_TAC poly_basemul_acc_montgomery_cached_k2_EXEC [n] THEN
                (SIMD_SIMPLIFY_TAC [montred])) (1--805) THEN

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
     (REWRITE_RULE[fst poly_basemul_acc_montgomery_cached_k2_EXEC] (CONV_RULE TWEAK_CONV poly_basemul_acc_montgomery_cached_k2_SPEC))
      `[D8; D9; D10; D11; D12; D13; D14; D15]` 64  THEN
   WORD_ARITH_TAC)
;;
