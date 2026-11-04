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
; Name: tomont_avx2_asm
; Description: x86_64 AVX2 Montgomery conversion
; Signature: void mlk_tomont_avx2_asm(int16_t *r)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 512
;     permissions: read/write
;     c_parameter: int16_t *r
;     description: Input/output polynomial (256 x int16_t)
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_tomont_avx2_asm
ENDIF

FUNC_NAME PROC FRAME


  sub           rsp,0A8h                       ; 0A8h and not 0A0h for alignment purposes
  .allocstack   0A8h

  vmovdqa       xmmword ptr [rsp+000h],xmm6    ; save xmm6 on stack
  .savexmm128   xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7    ; save xmm7 on stack
  .savexmm128   xmm7,010h
  vmovdqa       xmmword ptr [rsp+020h],xmm8    ; save xmm8 on stack
  .savexmm128   xmm8,020h
  vmovdqa       xmmword ptr [rsp+030h],xmm9    ; save xmm9 on stack
  .savexmm128   xmm9,030h
  vmovdqa       xmmword ptr [rsp+040h],xmm10   ; save xmm10 on stack
  .savexmm128   xmm10,040h
  vmovdqa       xmmword ptr [rsp+050h],xmm11   ; save xmm11 on stack
  .savexmm128   xmm11,050h
  vmovdqa       xmmword ptr [rsp+060h],xmm12   ; save xmm12 on stack
  .savexmm128   xmm12,060h
  vmovdqa       xmmword ptr [rsp+070h],xmm13   ; save xmm13 on stack
  .savexmm128   xmm13,070h
  vmovdqa       xmmword ptr [rsp+080h],xmm14   ; save xmm14 on stack
  .savexmm128   xmm14,080h
  vmovdqa       xmmword ptr [rsp+090h],xmm15   ; save xmm15 on stack
  .savexmm128   xmm15,090h
  .endprolog

  mov           eax,0d010d01h                  ;
  vmovd         xmm0,eax                       ;
  vpbroadcastd  ymm0,xmm0                      ;
  mov           eax,050495049h                 ;
  vmovd         xmm1,eax                       ;
  vpbroadcastd  ymm1,xmm1                      ;
  mov           eax,05490549h                  ;
  vmovd         xmm2,eax                       ;
  vpbroadcastd  ymm2,xmm2                      ;
  vmovdqa       ymm3,ymmword ptr [rcx]         ;
  vmovdqa       ymm4,ymmword ptr [rcx+020h]    ;
  vmovdqa       ymm5,ymmword ptr [rcx+040h]    ;
  vmovdqa       ymm6,ymmword ptr [rcx+060h]    ;
  vmovdqa       ymm7,ymmword ptr [rcx+080h]    ;
  vmovdqa       ymm8,ymmword ptr [rcx+0a0h]    ;
  vmovdqa       ymm9,ymmword ptr [rcx+0c0h]    ;
  vmovdqa       ymm10,ymmword ptr [rcx+0e0h]   ;
  vpmullw       ymm11,ymm3,ymm1                ;
  vpmulhw       ymm3,ymm3,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm0               ;
  vpsubw        ymm3,ymm3,ymm11                ;
  vpmullw       ymm12,ymm4,ymm1                ;
  vpmulhw       ymm4,ymm4,ymm2                 ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpsubw        ymm4,ymm4,ymm12                ;
  vpmullw       ymm13,ymm5,ymm1                ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpsubw        ymm5,ymm5,ymm13                ;
  vpmullw       ymm14,ymm6,ymm1                ;
  vpmulhw       ymm6,ymm6,ymm2                 ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpsubw        ymm6,ymm6,ymm14                ;
  vpmullw       ymm15,ymm7,ymm1                ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpsubw        ymm7,ymm7,ymm15                ;
  vpmullw       ymm11,ymm8,ymm1                ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm0               ;
  vpsubw        ymm8,ymm8,ymm11                ;
  vpmullw       ymm12,ymm9,ymm1                ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpsubw        ymm9,ymm9,ymm12                ;
  vpmullw       ymm13,ymm10,ymm1               ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpsubw        ymm10,ymm10,ymm13              ;
  vmovdqa       ymmword ptr [rcx],ymm3         ;
  vmovdqa       ymmword ptr [rcx+020h],ymm4    ;
  vmovdqa       ymmword ptr [rcx+040h],ymm5    ;
  vmovdqa       ymmword ptr [rcx+060h],ymm6    ;
  vmovdqa       ymmword ptr [rcx+080h],ymm7    ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm8    ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm9    ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm10   ;
  vmovdqa       ymm3,ymmword ptr [rcx+0100h]   ;
  vmovdqa       ymm4,ymmword ptr [rcx+0120h]   ;
  vmovdqa       ymm5,ymmword ptr [rcx+0140h]   ;
  vmovdqa       ymm6,ymmword ptr [rcx+0160h]   ;
  vmovdqa       ymm7,ymmword ptr [rcx+0180h]   ;
  vmovdqa       ymm8,ymmword ptr [rcx+01a0h]   ;
  vmovdqa       ymm9,ymmword ptr [rcx+01c0h]   ;
  vmovdqa       ymm10,ymmword ptr [rcx+01e0h]  ;
  vpmullw       ymm11,ymm3,ymm1                ;
  vpmulhw       ymm3,ymm3,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm0               ;
  vpsubw        ymm3,ymm3,ymm11                ;
  vpmullw       ymm12,ymm4,ymm1                ;
  vpmulhw       ymm4,ymm4,ymm2                 ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpsubw        ymm4,ymm4,ymm12                ;
  vpmullw       ymm13,ymm5,ymm1                ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpsubw        ymm5,ymm5,ymm13                ;
  vpmullw       ymm14,ymm6,ymm1                ;
  vpmulhw       ymm6,ymm6,ymm2                 ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpsubw        ymm6,ymm6,ymm14                ;
  vpmullw       ymm15,ymm7,ymm1                ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpsubw        ymm7,ymm7,ymm15                ;
  vpmullw       ymm11,ymm8,ymm1                ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm0               ;
  vpsubw        ymm8,ymm8,ymm11                ;
  vpmullw       ymm12,ymm9,ymm1                ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpsubw        ymm9,ymm9,ymm12                ;
  vpmullw       ymm13,ymm10,ymm1               ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpsubw        ymm10,ymm10,ymm13              ;
  vmovdqa       ymmword ptr [rcx+0100h],ymm3   ;
  vmovdqa       ymmword ptr [rcx+0120h],ymm4   ;
  vmovdqa       ymmword ptr [rcx+0140h],ymm5   ;
  vmovdqa       ymmword ptr [rcx+0160h],ymm6   ;
  vmovdqa       ymmword ptr [rcx+0180h],ymm7   ;
  vmovdqa       ymmword ptr [rcx+01a0h],ymm8   ;
  vmovdqa       ymmword ptr [rcx+01c0h],ymm9   ;
  vmovdqa       ymmword ptr [rcx+01e0h],ymm10  ;

  vzeroupper                                   ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]    ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]    ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]    ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]    ; restore xmm9 from stack
  vmovdqa       xmm10,xmmword ptr [rsp+040h]   ; restore xmm10 from stack
  vmovdqa       xmm11,xmmword ptr [rsp+050h]   ; restore xmm11 from stack
  vmovdqa       xmm12,xmmword ptr [rsp+060h]   ; restore xmm12 from stack
  vmovdqa       xmm13,xmmword ptr [rsp+070h]   ; restore xmm13 from stack
  vmovdqa       xmm14,xmmword ptr [rsp+080h]   ; restore xmm14 from stack
  vmovdqa       xmm15,xmmword ptr [rsp+090h]   ; restore xmm15 from stack

  add           rsp,0A8h                       ; 0A8h and not 0A0h for alignment purposes

  ret                                          ;

FUNC_NAME ENDP

  END
