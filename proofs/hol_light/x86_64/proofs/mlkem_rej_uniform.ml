(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling for ML-KEM, filtering packed numbers < 3329.   *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;
needs "x86_64/proofs/mlkem_rej_uniform_table.ml";;

(**** print_literal_from_elf "x86_64/mlkem/mlkem_rej_uniform.o";;
 ****)

let mlkem_rej_uniform_mc = define_assert_from_elf
  "mlkem_rej_uniform_mc" "x86_64/mlkem/mlkem_rej_uniform.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x81; 0xec; 0x10; 0x02; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 528)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x0f; 0x84; 0xdd; 0x00; 0x00; 0x00;
                           (* JE (Imm32 (word 221)) *)
  0x48; 0xb8; 0x01; 0x0d; 0x01; 0x0d; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% rax) (Imm64 (word 937044495634074881)) *)
  0x66; 0x48; 0x0f; 0x6e; 0xc0;
                           (* MOVQ (%_% xmm0) (% rax) *)
  0x66; 0x48; 0x0f; 0x3a; 0x22; 0xc0; 0x01;
                           (* PINSRQ (%_% xmm0) (% rax) (Imm8 (word 1)) *)
  0x48; 0xb8; 0xff; 0x0f; 0xff; 0x0f; 0xff; 0x0f; 0xff; 0x0f;
                           (* MOV (% rax) (Imm64 (word 1152657617789587455)) *)
  0x66; 0x48; 0x0f; 0x6e; 0xe8;
                           (* MOVQ (%_% xmm5) (% rax) *)
  0x66; 0x48; 0x0f; 0x3a; 0x22; 0xe8; 0x01;
                           (* PINSRQ (%_% xmm5) (% rax) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x00; 0x01; 0x01; 0x02; 0x03; 0x04; 0x04; 0x05;
                           (* MOV (% rax) (Imm64 (word 361418281061515520)) *)
  0x66; 0x48; 0x0f; 0x6e; 0xe0;
                           (* MOVQ (%_% xmm4) (% rax) *)
  0x48; 0xb8; 0x06; 0x07; 0x07; 0x08; 0x09; 0x0a; 0x0a; 0x0b;
                           (* MOV (% rax) (Imm64 (word 795459318089975558)) *)
  0x66; 0x48; 0x0f; 0x3a; 0x22; 0xe0; 0x01;
                           (* PINSRQ (%_% xmm4) (% rax) (Imm8 (word 1)) *)
  0x48; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 0)) *)
  0x49; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Imm32 (word 0)) *)
  0x49; 0xc7; 0xc1; 0x55; 0x55; 0x00; 0x00;
                           (* MOV (% r9) (Imm32 (word 21845)) *)
  0xf3; 0x42; 0x0f; 0x6f; 0x14; 0x06;
                           (* MOVDQU (%_% xmm2) (Memop Word128 (%%% (rsi,0,r8))) *)
  0x66; 0x0f; 0x38; 0x00; 0xd4;
                           (* PSHUFB (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xda;  (* MOVDQA (%_% xmm3) (%_% xmm2) *)
  0x66; 0x0f; 0x71; 0xd3; 0x04;
                           (* PSRLW (%_% xmm3) (Imm8 (word 4)) *)
  0x66; 0x0f; 0x3a; 0x0e; 0xd3; 0xaa;
                           (* PBLENDW (%_% xmm2) (%_% xmm3) (Imm8 (word 170)) *)
  0x66; 0x0f; 0xdb; 0xd5;  (* PAND (%_% xmm2) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0x65; 0xca;  (* PCMPGTW (%_% xmm1) (%_% xmm2) *)
  0x66; 0x44; 0x0f; 0xd7; 0xd9;
                           (* PMOVMSKB (% r11d) (%_% xmm1) *)
  0xc4; 0x42; 0xa2; 0xf5; 0xd9;
                           (* PEXT (% r11) (% r11) (% r9) *)
  0x4d; 0x89; 0xda;        (* MOV (% r10) (% r11) *)
  0x49; 0xc1; 0xe2; 0x04;  (* SHL (% r10) (Imm8 (word 4)) *)
  0xf3; 0x42; 0x0f; 0x6f; 0x1c; 0x11;
                           (* MOVDQU (%_% xmm3) (Memop Word128 (%%% (rcx,0,r10))) *)
  0x66; 0x0f; 0x38; 0x00; 0xd3;
                           (* PSHUFB (%_% xmm2) (%_% xmm3) *)
  0xf3; 0x0f; 0x7f; 0x14; 0x44;
                           (* MOVDQU (Memop Word128 (%%% (rsp,1,rax))) (%_% xmm2) *)
  0xf3; 0x4d; 0x0f; 0xb8; 0xdb;
                           (* POPCNT (% r11) (% r11) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% rax) (Imm32 (word 256)) *)
  0x73; 0x09;              (* JAE (Imm8 (word 9)) *)
  0x49; 0x83; 0xc0; 0x0c;  (* ADD (% r8) (Imm8 (word 12)) *)
  0x4c; 0x39; 0xc2;        (* CMP (% rdx) (% r8) *)
  0x77; 0xa0;              (* JA (Imm8 (word 160)) *)
  0x48; 0xc7; 0xc1; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rcx) (Imm32 (word 256)) *)
  0x48; 0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% rax) (Imm32 (word 256)) *)
  0x48; 0x0f; 0x47; 0xc1;  (* CMOVA (% rax) (% rcx) *)
  0x48; 0x89; 0xe6;        (* MOV (% rsi) (% rsp) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0xd1; 0xe1;        (* SHL (% rcx) (Imm8 (word 1)) *)
  0xf3; 0xa4;              (* MOVSB true (% rdi) (% rsi) (% rcx) *)
  0x48; 0x81; 0xc4; 0x10; 0x02; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 528)) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mlkem_rej_uniform_tmc =
  define_trimmed "mlkem_rej_uniform_tmc" mlkem_rej_uniform_mc;;

let MLKEM_REJ_UNIFORM_EXEC = X86_MK_CORE_EXEC_RULE mlkem_rej_uniform_tmc;;

(* ------------------------------------------------------------------------- *)
(* An abbreviation used within the proof, though expanded in the spec.       *)
(* ------------------------------------------------------------------------- *)

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x. val x < 3329) (MAP (word_zx:12 word->int16) l)`;;

let REJ_SAMPLE_EMPTY = prove
 (`REJ_SAMPLE [] = []`,
  REWRITE_TAC[REJ_SAMPLE; FILTER; MAP]);;

let REJ_SAMPLE_APPEND = prove
 (`!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`,
  REWRITE_TAC[REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for mapping XMM assumptions into YMM ones.                        *)
(* ------------------------------------------------------------------------- *)

let XMM_EXISTSTOP = prove
 (`!c s:S. read (c :> zerotop_128) s = l
           ==> ?h. read c s = (word_join:int128->int128->int256) h l`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `word_subword (read c (s:S):int256) (128,128):int128` THEN
  REWRITE_TAC[READ_ZEROTOP_128] THEN CONV_TAC WORD_BLAST);;

let XMM_EXISTSTOP_RULE =
  REWRITE_RULE (map GSYM
   [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
    XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15]) o
  C ISPEC XMM_EXISTSTOP;;

let XMM_EXISTSTOP_TAC top y =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (XMM_EXISTSTOP_RULE y)) THEN
  DISCH_THEN(X_CHOOSE_TAC(mk_var(top,`:int128`)));;

(* ------------------------------------------------------------------------- *)
(* Now the actual proof.                                                     *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;

let lemma1a = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 12
         ==> word_join (word_subword q (8*i+8,8):byte)
                       (word_subword q (8*i,8):byte):int16 =
             word_subword (q:int128) (8*i,16)`,
  CONV_TAC WORD_BLAST);;

let lemma1b = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 12
         ==> word_ushr
              (word_join (word_subword q (8*i+8,8):byte)
                         (word_subword q (8*i,8):byte)) 4 =
     (word_zx:12 word->int16) (word_subword (q:int128) (8*i+4,12))`,
  CONV_TAC WORD_BLAST);;

let lemma2 = WORD_BLAST
 `(!h l m. word_and ((word_join:int64->int64->int128) h l) m =
           word_join (word_and h (word_subword m (64,64)))
                     (word_and l (word_subword m (0,64)))) /\
  (!h l m. word_and ((word_join:int32->int32->int64) h l) m =
           word_join (word_and h (word_subword m (32,32)))
                     (word_and l (word_subword m (0,32)))) /\
  (!h l m. word_and ((word_join:int16->int16->int32) h l) m =
           word_join (word_and h (word_subword m (16,16)))
                     (word_and l (word_subword m (0,16))))`;;

let lemma3 = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 12
         ==> word_and (word_subword (q:int128) (12*i,16)) (word 4095) =
             (word_zx:12 word->int16) (word_subword (q:int128) (12*i,12))`,
  CONV_TAC WORD_BLAST);;

let MLKEM_REJ_UNIFORM_CORRECT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (stackpointer,528))
          [(word pc,0xf7); (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,0xf7); (stackpointer,528)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_tmc) /\
                read RIP s = word(pc + 0x7) /\
                read RSP s = stackpointer /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist)
           (\s. read RIP s = word(pc + 0xef) /\
                let inlist' = MAP (word_zx:12 word->16 word) inlist in
                let outlist =
                  SUB_LIST (0,256) (FILTER (\x. val x < 3329) inlist') in
                let outlen = LENGTH outlist in
                C_RETURN s = word outlen /\
                wordlist_from_memory(res,outlen) s = outlist)
           (MAYCHANGE [RIP; RDI; RSI; RAX; RCX; RDX; R8; R9; R10; R11] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(stackpointer,528)])`,
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              SOME_FLAGS; ALL; C_RETURN; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Modify the precondition style a little bit ***)

  MP_TAC(ISPECL
   [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
   (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL
   [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
    `buflen:num`; `inlist:(12 word)list`]
   (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_12] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  (*** Handle the special case of buflen = 0, which is an early exit ***)

  ASM_CASES_TAC `buflen = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    X86_SIM_TAC MLKEM_REJ_UNIFORM_EXEC (1--3) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `8 * 0 = 12 * l ==> l = 0`)) THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MAP; FILTER; SUB_LIST_CLAUSES; LENGTH] THEN
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES];
    ALL_TAC] THEN

  SUBGOAL_THEN `12 <= buflen` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** Pick a number characterizing the number of times round the loop ***)

  SUBGOAL_THEN
   `?i. buflen < 12 * (i + 1) \/
        256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * i) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN STRIP_TAC THEN

  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_SAMPLE_EMPTY; LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** Set up the main loop invariant, UP2 because of double test ***)

  ENSURES_WHILE_UP2_TAC `N:num` `pc + 0x73` `pc + 0xd3`
   `\i s. read RSP s = stackpointer /\
          ~read DF s /\
          read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
          read(memory :> bytes(table,4096)) s =
          num_of_wordlist mlkem_rej_uniform_table /\
          read XMM0 s = word 17285419996640026625003037585112632577 /\
          read XMM4 s = word 14673634461853297750225786205640917248 /\
          read XMM5 s = word 21262780079976241823186373959458164735 /\
          read R9 s = word 0x5555 /\
          let outlist = REJ_SAMPLE(SUB_LIST(0,8 * i) inlist) in
          let outlen = LENGTH outlist in
          read RDI s = res /\
          read RSI s = buf /\
          read RDX s = word buflen /\
          read RCX s = table /\
          (i < N ==> read R8 s = word(12 * i)) /\
          read RAX s = word outlen /\
          read (memory :> bytes (stackpointer,2*outlen)) s =
          num_of_wordlist outlist` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY;
                LENGTH; READ_MEMORY_BYTES_TRIVIAL; num_of_wordlist];

    (*** Main invariant preservation proof for the loop ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[NOT_LT] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `cur:int64 = word_add buf (word (12 * i))` THEN
    ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,8 * i) inlist)` THEN
    ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    ASM_REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN

    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top0" `YMM0` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    ABBREV_TAC `q0 = read (memory :> bytes128 cur) s0` THEN

    (*** Simulate up to the computation of table index ***)

    ASSUME_TAC(WORD_RULE
     `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [n] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV))) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV))
    (1--11) THEN

    (*** Simplify and rationalize some resulting expressions ***)

    RULE_ASSUM_TAC(REWRITE_RULE[lemma1a; lemma1b; WORD_BLAST
     `word_subword x (0,16):int16 = x`]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
     [MESON[] `word_subword (if p then x else y) q =
               if p then word_subword x q else word_subword y q`]) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [MESON[] `bit 7 (if p then x else y) =
               if p then bit 7 x else bit 7 y`]) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAUT `(if p then T else F) <=> p`]) THEN

    (*** Perform the table lookup ****)

    REABBREV_TAC `idx = read R10 s11` THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC [12] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_shl x 4:int64 = word(16 * val x)`]) THEN
    ABBREV_TAC
     `tab =
      read (memory :> bytes128(word_add table (word(16 * val(idx:int64)))))
           s12` THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (13--14) THEN

    (*** Further simplify ***)

    RULE_ASSUM_TAC(REWRITE_RULE[lemma2]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV))) THEN
    RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lemma3]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BITBLAST_RULE
     `word_and ((word_zx:12 word->int16) x) (word 4095) = word_zx x`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BITBLAST_RULE
     `word_igt (word 3329:int16) (word_zx(x:12 word)) <=>
      val(word_zx x:int16) < 3329`]) THEN

    (*** Abbreviate the next digits as 16-bit words ***)

    ABBREV_TAC
     `(x:num->int16) j =
      word_zx(word_subword (q0:int128) (12 * j,12):12 word)` THEN
    FIRST_ASSUM(fun th ->
      MP_TAC(end_itlist CONJ (map (C SPEC th o mk_small_numeral) (0--7)))) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    (**** Later in the proof, we actually want this equivalent ***)

    SUBGOAL_THEN
     `!j. j < 8
          ==> (word_zx:12 word->int16)
              (EL j (SUB_LIST(8 * i,8) inlist)) = x j`
    ASSUME_TAC THENL
     [UNDISCH_THEN
       `read (memory :> bytes (buf,buflen)) s14 =
        num_of_wordlist(inlist:(12 word)list)`
       (MP_TAC o AP_TERM
         `\x. x DIV 2 EXP (8 * 12 * i) MOD 2 EXP (8 * 12)`) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
      REWRITE_TAC[READ_BYTES_MOD] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC[ARITH_RULE `8 * 12 = 12 * 8 * 1`] THEN
      REWRITE_TAC[ARITH_RULE `8 * 12 * x = 12 * 8 * x`] THEN
      REWRITE_TAC[GSYM DIMINDEX_12; GSYM NUM_OF_WORDLIST_SUB_LIST] THEN
      REWRITE_TAC[DIMINDEX_12] THEN
      SUBGOAL_THEN
       `MIN (buflen - 12 * i) 12 = MIN (dimindex(:128) DIV 8) 12`
      SUBST1_TAC THENL
       [REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC(ARITH_RULE
         `12 * (i + 1) <= b ==> MIN (b - 12 * i) 12 = 12`) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
        REWRITE_TAC[GSYM VAL_READ_WBYTES] THEN
        ASM_REWRITE_TAC[GSYM BYTES128_WBYTES; GSYM READ_COMPONENT_COMPOSE] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      ASM_REWRITE_TAC[word_zx; VAL_WORD_SUBWORD] THEN
      REWRITE_TAC[MULT_CLAUSES; DIMINDEX_12; ARITH_RULE `MIN n n = n`] THEN
      SUBGOAL_THEN
       `(val(q0:int128) DIV 2 EXP (12 * j)) MOD 2 EXP 12 =
        ((val q0 MOD 2 EXP 96) DIV 2 EXP (12 * j)) MOD 2 EXP 12`
       (fun th -> ASM_REWRITE_TAC[th])
      THENL
       [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `j < 8 ==> MIN 96 (12 * j + 12) = 12 * j + 12`];
        REWRITE_TAC[GSYM DIMINDEX_12; NUM_OF_WORDLIST_EL]] THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN

    (*** The table-based selection, brute forced by case analysis ***)

    SUBGOAL_THEN
     `read YMM2 s14 =
      (word_join:int128->int128->int256)
      (word_subword (ymm2_init:int256) (128,128))
      (word(num_of_wordlist
         (FILTER (\x. val x < 3329)
                 [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7])))`
    MP_TAC THENL
     [UNDISCH_TAC
       `read(memory :> bytes(table,4096)) s14 =
        num_of_wordlist mlkem_rej_uniform_table` THEN
      REPLICATE_TAC 4
       (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
             [GSYM NUM_OF_PAIR_WORDLIST]) THEN
      REWRITE_TAC[mlkem_rej_uniform_table; pair_wordlist] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
      REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["tab"; "idx"] THEN
      REWRITE_TAC[bitval] THEN
      MAP_EVERY ASM_CASES_TAC
       [`val(x 0:int16) < 3329`; `val(x 1:int16) < 3329`;
        `val(x 2:int16) < 3329`; `val(x 3:int16) < 3329`;
        `val(x 4:int16) < 3329`; `val(x 5:int16) < 3329`;
        `val(x 6:int16) < 3329`; `val(x 7:int16) < 3329`] THEN
      ASM_REWRITE_TAC[FILTER] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_CONDENSE_CONV)) THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REPLICATE_TAC 3 (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
      REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
      REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;
      DISCARD_MATCHING_ASSUMPTIONS [`read YMM2 s = x`] THEN STRIP_TAC] THEN

    (*** The writeback and popcount ***)

    VAL_INT64_TAC `curlen:num` THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (15--16) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV))) THEN

    (*** The counting part, similarly brute-forced, though it's easier ***)

    SUBGOAL_THEN
     `read R11 s16 = word(LENGTH (FILTER (\x. val x < 3329)
                       [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7]))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
      REPEAT(ONCE_REWRITE_TAC[FILTER] THEN REWRITE_TAC[] THEN
             COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      DISCARD_STATE_TAC "s16" THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_CONDENSE_CONV)) THEN
      REWRITE_TAC[LENGTH; FILTER] THEN CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      DISCARD_MATCHING_ASSUMPTIONS [`read R11 s = x`] THEN STRIP_TAC] THEN

    (*** Handle the overlapping writebacks, first some initialization ***)

    MAP_EVERY ABBREV_TAC
     [`lis = FILTER (\x. val x < 3329)
                    [x 0:int16; x 1; x 2; x 3; x 4; x 5; x 6; x 7]`;
      `len = LENGTH(lis:int16 list)`] THEN

    SUBGOAL_THEN `len <= 8` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["len"; "lis"] THEN
      REPEAT CONJ_TAC THEN
      W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN

    ABBREV_TAC `curlist':int16 list = APPEND curlist lis` THEN
    ABBREV_TAC `curlen':num = curlen + len` THEN

    SUBGOAL_THEN
     `curlen' < 264 /\
      read (memory :> bytes (stackpointer,2*curlen')) s16 =
      num_of_wordlist(curlist':int16 list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["curlen'"; "curlist'"] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`curlen < 256`; `len <= 8`] THEN ARITH_TAC;
        REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o
        snd) THEN
      ASM_REWRITE_TAC[DIMINDEX_16; ARITH_RULE `8 * 2 * l = 16 * l`] THEN
      DISCH_THEN SUBST1_TAC THEN

      UNDISCH_THEN
       `read (memory :> bytes128 (word_add stackpointer (word (2 * curlen))))
             s16 =
        word (num_of_wordlist(lis:int16 list))`
       (MP_TAC o AP_TERM `val:int128->num`) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES; VAL_READ_WBYTES;
                  DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
      SUBGOAL_THEN `2 * len = MIN 16 (2 * len)` SUBST1_TAC THENL
       [UNDISCH_TAC `len <= 8` THEN ARITH_TAC;
        REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
      REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
      MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
      ASM_REWRITE_TAC[DIMINDEX_16] THEN
      UNDISCH_TAC `len <= 8` THEN ARITH_TAC;
      ALL_TAC] THEN

    SUBGOAL_THEN `LENGTH(curlist':int16 list) = curlen'` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["curlist'"; "curlen'"] THEN
      REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (*** Finish all the interesting parts before the next case split ***)

    SUBGOAL_THEN `REJ_SAMPLE (SUB_LIST(8 * i,8) inlist) = lis` ASSUME_TAC THENL
     [EXPAND_TAC "lis" THEN REWRITE_TAC[REJ_SAMPLE] THEN AP_TERM_TAC THEN
      REWRITE_TAC[LIST_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
      REWRITE_TAC[LENGTH_MAP] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN MATCH_MP_TAC(ARITH_RULE
         `8 * (i + 1) <= l ==> MIN 8 (l - 8 * i) = 8`) THEN
        SIMPLE_ARITH_TAC;
        ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `REJ_SAMPLE (SUB_LIST (0,8 * (i + 1)) inlist) = curlist'`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
      ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; ADD_CLAUSES];
      ALL_TAC] THEN

    (*** Now the case split over the ending loop count ***)

    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i + 1 < N`)) THEN
      ASM_REWRITE_TAC[NOT_LT; ARITH_RULE `(i + 1) + 1 = i + 2`] THEN
      STRIP_TAC THEN VAL_INT64_TAC `curlen':num` THEN
      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (17--19) THEN
      POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD; GSYM NOT_LT] THEN DISCH_TAC THEN
      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (20--22) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(TAUT `p ==> (if p then x else y) = x`) THEN
        ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; NOT_LT; DE_MORGAN_THM] THEN
        REWRITE_TAC[WORD_RULE
         `word_add (word(12 * i)) (word 12) = word(12 * (i + 1))`] THEN
        ASM_SIMP_TAC[VAL_WORD_LE] THEN
        MAP_EVERY VAL_INT64_TAC [`buflen:num`; `12 * (i + 1)`] THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
        UNDISCH_TAC `12 * (i + 2) <= buflen` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
      REPLICATE_TAC 3 (CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE;

      X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (17--19) THEN
      POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD; GSYM NOT_LT] THEN
      VAL_INT64_TAC `curlen':num` THEN ASM_REWRITE_TAC[NOT_LT] THEN
      COND_CASES_TAC THEN DISCH_TAC THENL
       [ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
        REPLICATE_TAC 3 (CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        ASM_REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE;
        X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (20--22) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(TAUT `p ==> (if ~p then x else y) = y`) THEN
          ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; NOT_LT; DE_MORGAN_THM] THEN
          REWRITE_TAC[WORD_RULE
           `word_add (word(12 * i)) (word 12) = word(12 * (i + 1))`] THEN
          MAP_EVERY VAL_INT64_TAC [`buflen:num`; `12 * (i + 1)`] THEN
          ASM_REWRITE_TAC[GSYM VAL_EQ; GSYM LE_LT] THEN
          FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
           [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
            DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
            REWRITE_TAC[LE_MULT_LCANCEL; LT_MULT_LCANCEL; ARITH_EQ] THEN
            SIMPLE_ARITH_TAC;
            MATCH_MP_TAC(ARITH_RULE
             `l < 256 ==> 256 <= l ==> b <= 12 * i'`)] THEN
          DISCARD_STATE_TAC "s22" THEN
          UNDISCH_TAC `~(256 <= curlen')` THEN REWRITE_TAC[NOT_LE] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LET_TRANS) THEN
          SUBST1_TAC(SYM(ASSUME `LENGTH(curlist':int16 list) = curlen'`)) THEN
          EXPAND_TAC "curlist'" THEN UNDISCH_TAC `~(i + 1 < N)` THEN
          REWRITE_TAC[NOT_LT] THEN GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
          DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; SUB_LIST_SPLIT] THEN
          REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD];
          ASM_REWRITE_TAC[XMM0; XMM4; XMM5; READ_ZEROTOP_128] THEN
          REPLICATE_TAC 3 (CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          ASM_REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE]]];

    (*** The copying to the output and final reasoning ***)

    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    MAP_EVERY ABBREV_TAC
     [`outlist = REJ_SAMPLE (SUB_LIST (0,8 * N) inlist)`;
      `outlen = LENGTH(outlist:int16 list)`] THEN
    SUBGOAL_THEN `outlen < 264` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
      MATCH_MP_TAC(ARITH_RULE
       `l' <= l + 8 ==> ~(b < x) /\ l < 256 ==> l' < 264`) THEN
      MP_TAC(ISPECL [`inlist:(12 word)list`; `8 * (N - 1)`; `8`; `0`]
          SUB_LIST_SPLIT) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 8 * (N - 1) + 8 = 8 * N`] THEN
      MAP_EVERY EXPAND_TAC ["outlen"; "outlist"] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
      REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
      REWRITE_TAC[REJ_SAMPLE] THEN
      W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
      REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
      MAP_EVERY VAL_INT64_TAC [`outlen:num`; `MIN 256 outlen`]] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (1--3) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `word(MIN 256 outlen):int64` o MATCH_MP
     (MESON[] `read RAX s = x ==> !x'. x = x' ==> read RAX s = x'`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
      ONCE_REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV THEN
      ARITH_TAC;
      DISCH_TAC] THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_EXEC (4--6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_shl (word n) 1 = word(2 * n)`]) THEN
    VAL_INT64_TAC `2 * MIN 256 outlen` THEN
    X86_VSTEPS_TAC MLKEM_REJ_UNIFORM_EXEC [7] THEN
    FIRST_X_ASSUM(MP_TAC o check
      (can (term_match [] `z = read c (write c y s)`) o concl)) THEN
    SIMP_TAC[READ_WRITE_X86_STRINGCOPY; ARITH_RULE
        `2 * MIN 256 l < 2 EXP 64`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) X86_STRINGCOPY_NONOVERLAPPING o
      rand o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ARITH_TAC; NONOVERLAPPING_TAC];
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[GSYM REJ_SAMPLE] THEN
    MP_TAC(ISPECL
     [`res:int64`; `LENGTH(SUB_LIST (0,256) (REJ_SAMPLE inlist))`;
      `2 * LENGTH(SUB_LIST (0,256) (REJ_SAMPLE inlist))`;
      `SUB_LIST (0,256) (REJ_SAMPLE inlist)`]
     (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`; DIMINDEX_16] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `read (memory :> bytes (stackpointer,2 * MIN 256 outlen)) s6 =
      num_of_wordlist (SUB_LIST (0,256) outlist:int16 list)`
    SUBST_ALL_TAC THENL
     [DISCARD_STATE_TAC "s7" THEN
      REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; DIMINDEX_16] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[ARITH_RULE `2 * MIN 256 l = MIN (2 * l) 512`] THEN
      REWRITE_TAC[ARITH_RULE `16 * 256 = 8 * 512`] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `MIN a b = MIN b a`] THEN
      REWRITE_TAC[GSYM READ_BYTES_MOD] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC[ARITH_RULE `512 = 8 * 64`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [SUBGOAL_THEN `SUB_LIST (0,8 * N) (inlist:(12 word)list) = inlist`
      SUBST_ALL_TAC THENL
       [MATCH_MP_TAC SUB_LIST_REFL THEN FIRST_X_ASSUM(MATCH_MP_TAC o
        MATCH_MP
         (ARITH_RULE `8 * b = 12 * l ==> b <= 12 * N ==> l <= 8 * N`)) THEN
        UNDISCH_TAC `buflen < 12 * (N + 1)` THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
        SIMP_TAC[LEFT_IMP_EXISTS_THM; LE_MULT_LCANCEL; LT_MULT_LCANCEL] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0]];
      ASM_REWRITE_TAC[GSYM NOT_LE; LENGTH_SUB_LIST; SUB_0] THEN
      ASM_SIMP_TAC[ARITH_RULE `256 <= n ==> MIN 256 n = 256`] THEN
      MATCH_MP_TAC(MESON[]
       `y = x /\ (y = x ==> P) ==> word x = word y /\ P`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
        TRANS_TAC LE_TRANS `outlen:num` THEN ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME `LENGTH(outlist:int16 list) = outlen`)) THEN
        EXPAND_TAC "outlist" THEN
        MP_TAC(ISPECL [`inlist:(12 word)list`; `8 * N`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th ->
          GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
        REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN
       `SUB_LIST (0,256) (REJ_SAMPLE inlist) = SUB_LIST (0,256) outlist`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`inlist:(12 word)list`; `8 * N`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
        ASM_SIMP_TAC[REJ_SAMPLE_APPEND; SUB_LIST_APPEND_LEFT];
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `256 <= l ==> 2 * 256 = 2 * MIN 256 l`)) THEN
      FIRST_ASSUM ACCEPT_TAC]]);;

let MLKEM_REJ_UNIFORM_NOIBT_SUBROUTINE_CORRECT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer returnaddress.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_sub stackpointer (word 528),528))
          [(word pc,LENGTH mlkem_rej_uniform_tmc);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,LENGTH mlkem_rej_uniform_tmc);
           (word_sub stackpointer (word 528),536)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                let inlist' = MAP (word_zx:12 word->16 word) inlist in
                let outlist =
                  SUB_LIST (0,256) (FILTER (\x. val x < 3329) inlist') in
                let outlen = LENGTH outlist in
                C_RETURN s = word outlen /\
                wordlist_from_memory(res,outlen) s = outlist)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,512);
                      memory :> bytes(word_sub stackpointer (word 528),528)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_STACK_TAC mlkem_rej_uniform_tmc
    (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_CORRECT) `[]` 528);;

let MLKEM_REJ_UNIFORM_SUBROUTINE_CORRECT = prove
 (`!res buf buflen table (inlist:(12 word)list) pc stackpointer returnaddress.
      12 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_sub stackpointer (word 528),528))
          [(word pc,LENGTH mlkem_rej_uniform_mc);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (res,512))
          [(word pc,LENGTH mlkem_rej_uniform_mc);
           (word_sub stackpointer (word 528),536)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res;buf;buflen;table] s /\
                (read DF s <=> false) /\
                wordlist_from_memory(table,4096) s = mlkem_rej_uniform_table /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                let inlist' = MAP (word_zx:12 word->16 word) inlist in
                let outlist =
                  SUB_LIST (0,256) (FILTER (\x. val x < 3329) inlist') in
                let outlen = LENGTH outlist in
                C_RETURN s = word outlen /\
                wordlist_from_memory(res,outlen) s = outlist)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,512);
                      memory :> bytes(word_sub stackpointer (word 528),528)])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_NOIBT_SUBROUTINE_CORRECT)));;
