;
; Copyright(c) The mlkem - native project authors
; Copyright(c) The mldsa - native project authors
; SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
;
;  References
;  ==========
;
;  - [REF_AVX2]
;    CRYSTALS-Dilithium optimized AVX2 implementation
;    Bai, Ducas, Kiltz, Lepoint, Lyubashevsky, Schwabe, Seiler, Stehlé
;    https://github.com/pq-crystals/dilithium/tree/master/avx2
;
; This file is derived from the public domain
; AVX2 Dilithium implementation @[REF_AVX2].
;
; MASM (Microsoft Assembler) version for MS Windows
; provided by Ingo A. Kubbilun <ingo.kubbilun@gmail.com>
; Oct. 2026
;
; This honors the Microsoft AMD64 ABI instead of
; Sys V AMD64 ABI (e.g. Linux/GNU Compiler Collection)
;
; pseudo assembly instructions (prologue, FRAME/UNWIND)
; added with help from Github Copilot, assembly checking
; performed by Github Copilot, too.
;

                          .CODE

                           ALIGN 16

; yaml
; Name: rej_uniform_avx2_asm
; Description: x86_64 AVX2 rejection sampling
; Signature: uint64_t mlk_rej_uniform_avx2_asm(int16_t *r, const uint8_t *buf, uint64_t buflen, const uint8_t *table)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 512
;     permissions: write-only
;     c_parameter: int16_t *r
;     description: Output buffer (256 x int16_t)
;   rdx:
;     type: buffer
;     size_bytes: rdx
;     permissions: read-only
;     c_parameter: const uint8_t *buf
;     description: Input buffer
;   r8:
;     type: scalar
;     c_parameter: uint64_t buflen
;     description: Length of input buffer (must be multiple of 12)
;     test_with: 504  # MLKEM_GEN_MATRIX_NBLOCKS * MLK_XOF_RATE
;   r9:
;     type: buffer
;     size_bytes: 4096
;     permissions: read-only
;     c_parameter: const uint8_t *table
;     description: Lookup table
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_rej_uniform_avx2_asm
ENDIF

FUNC_NAME PROC FRAME


                                                      ; Only volatile registers are used (rax, rcx, rdx, r8-r11,
                                                      ; xmm0-xmm5), so nothing needs to be saved/restored and the
                                                      ; arguments stay where the MS ABI puts them:
                                                      ;   rcx = r, rdx = buf (advanced), r8 = buf end, r9 = table
         sub       rsp,0210h                          ; 512 bytes scratch + 16 bytes store overhang
         .allocstack 0210h
         .endprolog

         xor       eax,eax                            ; count = 0
         test      r8,r8                              ;
         je        Lmlk_rej_uniform_asm_end           ;
         add       r8,rdx                             ; r8 = end of input (replaces offset register)
         mov       rax,0d010d010d010d01h              ;
         movq      xmm0,rax                           ;
         pinsrq    xmm0,rax,01h                       ;
         mov       rax,0fff0fff0fff0fffh              ;
         movq      xmm5,rax                           ;
         pinsrq    xmm5,rax,01h                       ;
         mov       rax,0504040302010100h              ;
         movq      xmm4,rax                           ;
         mov       rax,0b0a0a0908070706h              ;
         pinsrq    xmm4,rax,01h                       ;
         xor       eax,eax                            ;
         mov       r10d,05555h                        ; pext mask

         ALIGN     16

Lmlk_rej_uniform_asm_loop_start:

         movq      xmm2,qword ptr [rdx]               ;
         pinsrd    xmm2,dword ptr [rdx+08h],02h       ;
         pshufb    xmm2,xmm4                          ;
         movdqa    xmm3,xmm2                          ;
         psrlw     xmm3,04h                           ;
         pblendw   xmm2,xmm3,0aah                     ;
         pand      xmm2,xmm5                          ;
         movdqa    xmm1,xmm0                          ;
         pcmpgtw   xmm1,xmm2                          ;
         pmovmskb  r11d,xmm1                          ;
         pext      r11,r11,r10                        ;
         shl       r11,04h                            ; table index * 16
         movdqu    xmm3,xmmword ptr [r9+r11*1]        ;
         pshufb    xmm2,xmm3                          ;
         movdqu    xmmword ptr [rsp+rax*2],xmm2       ;
         popcnt    r11,r11                            ; shifting does not change the popcount
         add       rax,r11                            ;
         cmp       rax,0100h                          ;
         jae       Lmlk_rej_uniform_asm_final_copy    ;
         add       rdx,0ch                            ;
         cmp       r8,rdx                             ;
         ja        Lmlk_rej_uniform_asm_loop_start    ;

         ALIGN     16

Lmlk_rej_uniform_asm_final_copy:

         mov       r10d,0100h                         ;
         cmp       rax,r10                            ;
         cmova     rax,r10                            ; clamp count to 256
         lea       r8,[rax*2]                         ; r8 = bytes to copy
         xor       edx,edx                            ; rdx = byte offset

Lmlk_rej_uniform_asm_copy16:                          ; Claude says: no 'ALIGN 16' here because it does not save much
                                                      ; Claude optimized 'rep movsb' away favoring movdqu instead
         lea       r9,[rdx+10h]                       ;
         cmp       r9,r8                              ;
         ja        Lmlk_rej_uniform_asm_copy_tail     ;
         movdqu    xmm0,xmmword ptr [rsp+rdx]         ;
         movdqu    xmmword ptr [rcx+rdx],xmm0         ;
         mov       rdx,r9                             ;
         jmp       Lmlk_rej_uniform_asm_copy16        ;

         ALIGN     16

Lmlk_rej_uniform_asm_copy_tail:

         cmp       rdx,r8                             ;
         jae       Lmlk_rej_uniform_asm_end           ;
         movzx     r9d,word ptr [rsp+rdx]             ;
         mov       word ptr [rcx+rdx],r9w             ;
         add       rdx,02h                            ;
         jmp       Lmlk_rej_uniform_asm_copy_tail     ;

         ALIGN     16

Lmlk_rej_uniform_asm_end:
         add       rsp,0210h                          ;
         ret                                          ;

FUNC_NAME ENDP

         END
