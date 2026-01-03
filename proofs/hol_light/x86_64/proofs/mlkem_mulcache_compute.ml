(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
needs "x86_64/proofs/mlkem_zetas.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_mulcache_compute.o";; *)

let mlkem_mulcache_compute_mc = define_assert_from_elf "mlkem_mulcache_compute_mc" "x86_64/mlkem/mlkem_mulcache_compute.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xfd; 0x6f; 0x56; 0x20;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x5e; 0x60;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,992))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0x60; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1120))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0x3f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x47; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1024))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1152))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x47; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1056))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0xa0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1184))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x40; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1088))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0xc0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1216))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm8) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_mulcache_compute_tmc = define_trimmed "mlkem_mulcache_compute_tmc" mlkem_mulcache_compute_mc;;
let MLKEM_MULCACHE_COMPUTE_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_mulcache_compute_tmc;;

let avx2_mulcache = define
 `avx2_mulcache f k =
   let r = k DIV 64 in
   let q = k MOD 64 in
   let s = r * 128 + 32 * (q DIV 16) + (q MOD 16) + 16 in
   let t = 64 * r + 2 * (q DIV 32) + 4 * (q MOD 16) in
   (f s * (&17 pow (2 * bitreverse7 t + 1))) rem &3329`;;

let MLKEM_MULCACHE_COMPUTE_CORRECT = prove(
 `!r a zetas (zetas_list:int16 list) x pc.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, 323) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mlkem_mulcache_compute_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [r; a; zetas] s /\
              wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
              (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = word(pc + 323) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [events] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10] ,,
           MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,

  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `zetas:int64`; `zetas_list:int16 list`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN

  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  REWRITE_TAC [SOME_FLAGS; fst MLKEM_MULCACHE_COMPUTE_TMC_EXEC] THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN

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

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_MULCACHE_COMPUTE_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[ntt_montmul_alt])
        (1--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Reverse restructuring *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  (* Split quantified post-condition into separate cases *)
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN

  (* Forget all assumptions *)
  POP_ASSUM_LIST (K ALL_TAC) THEN

  (* Split into one congruence goals per index. *)
  (* Split into pairs of congruence and absolute value goals *)
  REPEAT(W(fun (asl,w) ->
  if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  REWRITE_TAC[avx2_mulcache; avx2_ntt_order] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN

  (* Instantiate general congruence and bounds rule for Montgomery multiplication
   * so it matches the current goal, and add as new assumption. *)
  W (MP_TAC o CONGBOUND_RULE o rand o rand o rator o rator o lhand o snd) THEN
  ASM_REWRITE_TAC [o_THM] THEN

  MATCH_MP_TAC MONO_AND THEN (CONJ_TAC THENL [
    (* Correctness *)
    REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 3329 65536`] THEN
    REWRITE_TAC [GSYM INT_REM_EQ] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC ((GEN_REWRITE_CONV DEPTH_CONV [BITREVERSE7_CLAUSES])
              THENC (REPEATC (CHANGED_CONV (ONCE_DEPTH_CONV NUM_RED_CONV)))) THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC [REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC

    ;

    (* Bounds *)
    REWRITE_TAC [INT_ABS_BOUNDS] THEN
    MATCH_MP_TAC(INT_ARITH
      `l':int <= l /\ u <= u'
       ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
    CONV_TAC INT_REDUCE_CONV])
);;

let MLKEM_MULCACHE_COMPUTE_NOIBT_SUBROUTINE_CORRECT  = prove(
 `!r a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, LENGTH mlkem_mulcache_compute_tmc) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248) /\
    nonoverlapping (r, 256) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_mulcache_compute_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [r; a; zetas] s /\
               wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
               (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_mulcache_compute_tmc (CONV_RULE TWEAK_CONV MLKEM_MULCACHE_COMPUTE_CORRECT));;

let MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT = prove(
 `!r a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, LENGTH mlkem_mulcache_compute_mc) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248) /\
    nonoverlapping (r, 256) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_mulcache_compute_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [r; a; zetas] s /\
               wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
               (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
  (CONV_RULE TWEAK_CONV MLKEM_MULCACHE_COMPUTE_NOIBT_SUBROUTINE_CORRECT)));;
