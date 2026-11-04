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
; Name: invntt_avx2_asm
; Description: x86_64 AVX2 inverse NTT
; Signature: void mlk_invntt_avx2_asm(int16_t *r, const int16_t *qdata)
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
;   rdx:
;     type: buffer
;     size_bytes: 1248
;     permissions: read-only
;     c_parameter: const int16_t *qdata
;     description: Precomputed constants (624 x int16_t)
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_invntt_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,0A8h                             ; 0A8h and not 0A0h for alignment purposes
  .allocstack   0A8h

  vmovdqa       xmmword ptr [rsp+000h],xmm6          ; save xmm6 on stack
  .savexmm128    xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7          ; save xmm7 on stack
  .savexmm128    xmm7,010h
  vmovdqa       xmmword ptr [rsp+020h],xmm8          ; save xmm8 on stack
  .savexmm128    xmm8,020h
  vmovdqa       xmmword ptr [rsp+030h],xmm9          ; save xmm9 on stack
  .savexmm128    xmm9,030h
  vmovdqa       xmmword ptr [rsp+040h],xmm10         ; save xmm10 on stack
  .savexmm128    xmm10,040h
  vmovdqa       xmmword ptr [rsp+050h],xmm11         ; save xmm11 on stack
  .savexmm128    xmm11,050h
  vmovdqa       xmmword ptr [rsp+060h],xmm12         ; save xmm12 on stack
  .savexmm128    xmm12,060h
  vmovdqa       xmmword ptr [rsp+070h],xmm13         ; save xmm13 on stack
  .savexmm128    xmm13,070h
  vmovdqa       xmmword ptr [rsp+080h],xmm14         ; save xmm14 on stack
  .savexmm128    xmm14,080h
  vmovdqa       xmmword ptr [rsp+090h],xmm15         ; save xmm15 on stack
  .savexmm128    xmm15,090h
  .endprolog

  mov           eax,0d010d01h                        ;
  vmovd         xmm0,eax                             ;
  vpbroadcastd  ymm0,xmm0                            ;
  mov           eax,0d8a1d8a1h                       ;
  vmovd         xmm2,eax                             ;
  vpbroadcastd  ymm2,xmm2                            ;
  mov           eax,05a105a1h                        ;
  vmovd         xmm3,eax                             ;
  vpbroadcastd  ymm3,xmm3                            ;
  vmovdqa       ymm4,ymmword ptr [rcx]               ;
  vmovdqa       ymm6,ymmword ptr [rcx+040h]          ;
  vmovdqa       ymm5,ymmword ptr [rcx+020h]          ;
  vmovdqa       ymm7,ymmword ptr [rcx+060h]          ;
  vpmullw       ymm12,ymm4,ymm2                      ;
  vpmulhw       ymm4,ymm4,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm4,ymm4,ymm12                      ;
  vpmullw       ymm12,ymm6,ymm2                      ;
  vpmulhw       ymm6,ymm6,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm6,ymm6,ymm12                      ;
  vpmullw       ymm12,ymm5,ymm2                      ;
  vpmulhw       ymm5,ymm5,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm5,ymm5,ymm12                      ;
  vpmullw       ymm12,ymm7,ymm2                      ;
  vpmulhw       ymm7,ymm7,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm7,ymm7,ymm12                      ;
  vmovdqa       ymm8,ymmword ptr [rcx+080h]          ;
  vmovdqa       ymm10,ymmword ptr [rcx+0c0h]         ;
  vmovdqa       ymm9,ymmword ptr [rcx+0a0h]          ;
  vmovdqa       ymm11,ymmword ptr [rcx+0e0h]         ;
  vpmullw       ymm12,ymm8,ymm2                      ;
  vpmulhw       ymm8,ymm8,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm8,ymm8,ymm12                      ;
  vpmullw       ymm12,ymm10,ymm2                     ;
  vpmulhw       ymm10,ymm10,ymm3                     ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm10,ymm10,ymm12                    ;
  vpmullw       ymm12,ymm9,ymm2                      ;
  vpmulhw       ymm9,ymm9,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm9,ymm9,ymm12                      ;
  vpmullw       ymm12,ymm11,ymm2                     ;
  vpmulhw       ymm11,ymm11,ymm3                     ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm11,ymm11,ymm12                    ;
  vpermq        ymm15,ymmword ptr [rdx+03a0h],04eh   ;
  vpermq        ymm1,ymmword ptr [rdx+0360h],04eh    ;
  vpermq        ymm2,ymmword ptr [rdx+03c0h],04eh    ;
  vpermq        ymm3,ymmword ptr [rdx+0380h],04eh    ;
  vmovdqa       ymm12,ymmword ptr [rdx]              ;
  vpshufb       ymm15,ymm15,ymm12                    ;
  vpshufb       ymm1,ymm1,ymm12                      ;
  vpshufb       ymm2,ymm2,ymm12                      ;
  vpshufb       ymm3,ymm3,ymm12                      ;
  vpsubw        ymm12,ymm6,ymm4                      ;
  vpaddw        ymm4,ymm4,ymm6                       ;
  vpsubw        ymm13,ymm7,ymm5                      ;
  vpmullw       ymm6,ymm12,ymm15                     ;
  vpaddw        ymm5,ymm5,ymm7                       ;
  vpsubw        ymm14,ymm10,ymm8                     ;
  vpmullw       ymm7,ymm13,ymm15                     ;
  vpaddw        ymm8,ymm8,ymm10                      ;
  vpsubw        ymm15,ymm11,ymm9                     ;
  vpmullw       ymm10,ymm14,ymm1                     ;
  vpaddw        ymm9,ymm9,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm1                     ;
  vpmulhw       ymm12,ymm12,ymm2                     ;
  vpmulhw       ymm13,ymm13,ymm2                     ;
  vpmulhw       ymm14,ymm14,ymm3                     ;
  vpmulhw       ymm15,ymm15,ymm3                     ;
  vpmulhw       ymm6,ymm6,ymm0                       ;
  vpmulhw       ymm7,ymm7,ymm0                       ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm6,ymm12,ymm6                      ;
  vpsubw        ymm7,ymm13,ymm7                      ;
  vpsubw        ymm10,ymm14,ymm10                    ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpermq        ymm2,ymmword ptr [rdx+0320h],04eh    ;
  vpermq        ymm3,ymmword ptr [rdx+0340h],04eh    ;
  vmovdqa       ymm1,ymmword ptr [rdx]               ;
  vpshufb       ymm2,ymm2,ymm1                       ;
  vpshufb       ymm3,ymm3,ymm1                       ;
  vpsubw        ymm12,ymm8,ymm4                      ;
  vpaddw        ymm4,ymm4,ymm8                       ;
  vpsubw        ymm13,ymm9,ymm5                      ;
  vpmullw       ymm8,ymm12,ymm2                      ;
  vpaddw        ymm5,ymm5,ymm9                       ;
  vpsubw        ymm14,ymm10,ymm6                     ;
  vpmullw       ymm9,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm10                      ;
  vpsubw        ymm15,ymm11,ymm7                     ;
  vpmullw       ymm10,ymm14,ymm2                     ;
  vpaddw        ymm7,ymm7,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm3                     ;
  vpmulhw       ymm13,ymm13,ymm3                     ;
  vpmulhw       ymm14,ymm14,ymm3                     ;
  vpmulhw       ymm15,ymm15,ymm3                     ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm9,ymm9,ymm0                       ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm8,ymm12,ymm8                      ;
  vpsubw        ymm9,ymm13,ymm9                      ;
  vpsubw        ymm10,ymm14,ymm10                    ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpslld        ymm3,ymm5,010h                       ;
  vpblendw      ymm3,ymm4,ymm3,0aah                  ;
  vpsrld        ymm4,ymm4,010h                       ;
  vpblendw      ymm5,ymm4,ymm5,0aah                  ;
  vpslld        ymm4,ymm7,010h                       ;
  vpblendw      ymm4,ymm6,ymm4,0aah                  ;
  vpsrld        ymm6,ymm6,010h                       ;
  vpblendw      ymm7,ymm6,ymm7,0aah                  ;
  vpslld        ymm6,ymm9,010h                       ;
  vpblendw      ymm6,ymm8,ymm6,0aah                  ;
  vpsrld        ymm8,ymm8,010h                       ;
  vpblendw      ymm9,ymm8,ymm9,0aah                  ;
  vpslld        ymm8,ymm11,010h                      ;
  vpblendw      ymm8,ymm10,ymm8,0aah                 ;
  vpsrld        ymm10,ymm10,010h                     ;
  vpblendw      ymm11,ymm10,ymm11,0aah               ;
  vmovdqa       ymm12,ymmword ptr [rdx+020h]         ;
  vpermd        ymm2,ymm12,ymmword ptr [rdx+02e0h]   ;
  vpermd        ymm10,ymm12,ymmword ptr [rdx+0300h]  ;
  vpsubw        ymm12,ymm5,ymm3                      ;
  vpaddw        ymm3,ymm3,ymm5                       ;
  vpsubw        ymm13,ymm7,ymm4                      ;
  vpmullw       ymm5,ymm12,ymm2                      ;
  vpaddw        ymm4,ymm4,ymm7                       ;
  vpsubw        ymm14,ymm9,ymm6                      ;
  vpmullw       ymm7,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm9                       ;
  vpsubw        ymm15,ymm11,ymm8                     ;
  vpmullw       ymm9,ymm14,ymm2                      ;
  vpaddw        ymm8,ymm8,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm10                    ;
  vpmulhw       ymm13,ymm13,ymm10                    ;
  vpmulhw       ymm14,ymm14,ymm10                    ;
  vpmulhw       ymm15,ymm15,ymm10                    ;
  vpmulhw       ymm5,ymm5,ymm0                       ;
  vpmulhw       ymm7,ymm7,ymm0                       ;
  vpmulhw       ymm9,ymm9,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm5,ymm12,ymm5                      ;
  vpsubw        ymm7,ymm13,ymm7                      ;
  vpsubw        ymm9,ymm14,ymm9                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  mov           eax,04ebf4ebfh                       ;
  vmovd         xmm1,eax                             ;
  vpbroadcastd  ymm1,xmm1                            ;
  vpmulhw       ymm12,ymm3,ymm1                      ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm3,ymm3,ymm12                      ;
  vmovsldup     ymm10,ymm4                           ;
  vpblendd      ymm10,ymm3,ymm10,0aah                ;
  vpsrlq        ymm3,ymm3,020h                       ;
  vpblendd      ymm4,ymm3,ymm4,0aah                  ;
  vmovsldup     ymm3,ymm8                            ;
  vpblendd      ymm3,ymm6,ymm3,0aah                  ;
  vpsrlq        ymm6,ymm6,020h                       ;
  vpblendd      ymm8,ymm6,ymm8,0aah                  ;
  vmovsldup     ymm6,ymm7                            ;
  vpblendd      ymm6,ymm5,ymm6,0aah                  ;
  vpsrlq        ymm5,ymm5,020h                       ;
  vpblendd      ymm7,ymm5,ymm7,0aah                  ;
  vmovsldup     ymm5,ymm11                           ;
  vpblendd      ymm5,ymm9,ymm5,0aah                  ;
  vpsrlq        ymm9,ymm9,020h                       ;
  vpblendd      ymm11,ymm9,ymm11,0aah                ;
  vpermq        ymm2,ymmword ptr [rdx+02a0h],01bh    ;
  vpermq        ymm9,ymmword ptr [rdx+02c0h],01bh    ;
  vpsubw        ymm12,ymm4,ymm10                     ;
  vpaddw        ymm10,ymm10,ymm4                     ;
  vpsubw        ymm13,ymm8,ymm3                      ;
  vpmullw       ymm4,ymm12,ymm2                      ;
  vpaddw        ymm3,ymm3,ymm8                       ;
  vpsubw        ymm14,ymm7,ymm6                      ;
  vpmullw       ymm8,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm7                       ;
  vpsubw        ymm15,ymm11,ymm5                     ;
  vpmullw       ymm7,ymm14,ymm2                      ;
  vpaddw        ymm5,ymm5,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm9                     ;
  vpmulhw       ymm13,ymm13,ymm9                     ;
  vpmulhw       ymm14,ymm14,ymm9                     ;
  vpmulhw       ymm15,ymm15,ymm9                     ;
  vpmulhw       ymm4,ymm4,ymm0                       ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm7,ymm7,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm4,ymm12,ymm4                      ;
  vpsubw        ymm8,ymm13,ymm8                      ;
  vpsubw        ymm7,ymm14,ymm7                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpmulhw       ymm12,ymm10,ymm1                     ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm10,ymm10,ymm12                    ;
  vpunpcklqdq   ymm9,ymm10,ymm3                      ;
  vpunpckhqdq   ymm3,ymm10,ymm3                      ;
  vpunpcklqdq   ymm10,ymm6,ymm5                      ;
  vpunpckhqdq   ymm5,ymm6,ymm5                       ;
  vpunpcklqdq   ymm6,ymm4,ymm8                       ;
  vpunpckhqdq   ymm8,ymm4,ymm8                       ;
  vpunpcklqdq   ymm4,ymm7,ymm11                      ;
  vpunpckhqdq   ymm11,ymm7,ymm11                     ;
  vpermq        ymm2,ymmword ptr [rdx+0260h],04eh    ;
  vpermq        ymm7,ymmword ptr [rdx+0280h],04eh    ;
  vpsubw        ymm12,ymm3,ymm9                      ;
  vpaddw        ymm9,ymm9,ymm3                       ;
  vpsubw        ymm13,ymm5,ymm10                     ;
  vpmullw       ymm3,ymm12,ymm2                      ;
  vpaddw        ymm10,ymm10,ymm5                     ;
  vpsubw        ymm14,ymm8,ymm6                      ;
  vpmullw       ymm5,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm8                       ;
  vpsubw        ymm15,ymm11,ymm4                     ;
  vpmullw       ymm8,ymm14,ymm2                      ;
  vpaddw        ymm4,ymm4,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm7                     ;
  vpmulhw       ymm13,ymm13,ymm7                     ;
  vpmulhw       ymm14,ymm14,ymm7                     ;
  vpmulhw       ymm15,ymm15,ymm7                     ;
  vpmulhw       ymm3,ymm3,ymm0                       ;
  vpmulhw       ymm5,ymm5,ymm0                       ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm3,ymm12,ymm3                      ;
  vpsubw        ymm5,ymm13,ymm5                      ;
  vpsubw        ymm8,ymm14,ymm8                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpmulhw       ymm12,ymm9,ymm1                      ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm9,ymm9,ymm12                      ;
  vperm2i128    ymm7,ymm9,ymm10,020h                 ;
  vperm2i128    ymm10,ymm9,ymm10,031h                ;
  vperm2i128    ymm9,ymm6,ymm4,020h                  ;
  vperm2i128    ymm4,ymm6,ymm4,031h                  ;
  vperm2i128    ymm6,ymm3,ymm5,020h                  ;
  vperm2i128    ymm5,ymm3,ymm5,031h                  ;
  vperm2i128    ymm3,ymm8,ymm11,020h                 ;
  vperm2i128    ymm11,ymm8,ymm11,031h                ;
  vmovdqa       ymm2,ymmword ptr [rdx+0220h]         ;
  vmovdqa       ymm8,ymmword ptr [rdx+0240h]         ;
  vpsubw        ymm12,ymm10,ymm7                     ;
  vpaddw        ymm7,ymm7,ymm10                      ;
  vpsubw        ymm13,ymm4,ymm9                      ;
  vpmullw       ymm10,ymm12,ymm2                     ;
  vpaddw        ymm9,ymm9,ymm4                       ;
  vpsubw        ymm14,ymm5,ymm6                      ;
  vpmullw       ymm4,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm5                       ;
  vpsubw        ymm15,ymm11,ymm3                     ;
  vpmullw       ymm5,ymm14,ymm2                      ;
  vpaddw        ymm3,ymm3,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm8                     ;
  vpmulhw       ymm13,ymm13,ymm8                     ;
  vpmulhw       ymm14,ymm14,ymm8                     ;
  vpmulhw       ymm15,ymm15,ymm8                     ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm4,ymm4,ymm0                       ;
  vpmulhw       ymm5,ymm5,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm10,ymm12,ymm10                    ;
  vpsubw        ymm4,ymm13,ymm4                      ;
  vpsubw        ymm5,ymm14,ymm5                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpmulhw       ymm12,ymm7,ymm1                      ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm7,ymm7,ymm12                      ;
  vmovdqa       ymmword ptr [rcx],ymm7               ;
  vmovdqa       ymmword ptr [rcx+020h],ymm9          ;
  vmovdqa       ymmword ptr [rcx+040h],ymm6          ;
  vmovdqa       ymmword ptr [rcx+060h],ymm3          ;
  vmovdqa       ymmword ptr [rcx+080h],ymm10         ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm4          ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm5          ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm11         ;
  mov           eax,0d8a1d8a1h                       ;
  vmovd         xmm2,eax                             ;
  vpbroadcastd  ymm2,xmm2                            ;
  mov           eax,05a105a1h                        ;
  vmovd         xmm3,eax                             ;
  vpbroadcastd  ymm3,xmm3                            ;
  vmovdqa       ymm4,ymmword ptr [rcx+0100h]         ;
  vmovdqa       ymm6,ymmword ptr [rcx+0140h]         ;
  vmovdqa       ymm5,ymmword ptr [rcx+0120h]         ;
  vmovdqa       ymm7,ymmword ptr [rcx+0160h]         ;
  vpmullw       ymm12,ymm4,ymm2                      ;
  vpmulhw       ymm4,ymm4,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm4,ymm4,ymm12                      ;
  vpmullw       ymm12,ymm6,ymm2                      ;
  vpmulhw       ymm6,ymm6,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm6,ymm6,ymm12                      ;
  vpmullw       ymm12,ymm5,ymm2                      ;
  vpmulhw       ymm5,ymm5,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm5,ymm5,ymm12                      ;
  vpmullw       ymm12,ymm7,ymm2                      ;
  vpmulhw       ymm7,ymm7,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm7,ymm7,ymm12                      ;
  vmovdqa       ymm8,ymmword ptr [rcx+0180h]         ;
  vmovdqa       ymm10,ymmword ptr [rcx+01c0h]        ;
  vmovdqa       ymm9,ymmword ptr [rcx+01a0h]         ;
  vmovdqa       ymm11,ymmword ptr [rcx+01e0h]        ;
  vpmullw       ymm12,ymm8,ymm2                      ;
  vpmulhw       ymm8,ymm8,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm8,ymm8,ymm12                      ;
  vpmullw       ymm12,ymm10,ymm2                     ;
  vpmulhw       ymm10,ymm10,ymm3                     ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm10,ymm10,ymm12                    ;
  vpmullw       ymm12,ymm9,ymm2                      ;
  vpmulhw       ymm9,ymm9,ymm3                       ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm9,ymm9,ymm12                      ;
  vpmullw       ymm12,ymm11,ymm2                     ;
  vpmulhw       ymm11,ymm11,ymm3                     ;
  vpmulhw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm11,ymm11,ymm12                    ;
  vpermq        ymm15,ymmword ptr [rdx+01e0h],04eh   ;
  vpermq        ymm1,ymmword ptr [rdx+01a0h],04eh    ;
  vpermq        ymm2,ymmword ptr [rdx+0200h],04eh    ;
  vpermq        ymm3,ymmword ptr [rdx+01c0h],04eh    ;
  vmovdqa       ymm12,ymmword ptr [rdx]              ;
  vpshufb       ymm15,ymm15,ymm12                    ;
  vpshufb       ymm1,ymm1,ymm12                      ;
  vpshufb       ymm2,ymm2,ymm12                      ;
  vpshufb       ymm3,ymm3,ymm12                      ;
  vpsubw        ymm12,ymm6,ymm4                      ;
  vpaddw        ymm4,ymm4,ymm6                       ;
  vpsubw        ymm13,ymm7,ymm5                      ;
  vpmullw       ymm6,ymm12,ymm15                     ;
  vpaddw        ymm5,ymm5,ymm7                       ;
  vpsubw        ymm14,ymm10,ymm8                     ;
  vpmullw       ymm7,ymm13,ymm15                     ;
  vpaddw        ymm8,ymm8,ymm10                      ;
  vpsubw        ymm15,ymm11,ymm9                     ;
  vpmullw       ymm10,ymm14,ymm1                     ;
  vpaddw        ymm9,ymm9,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm1                     ;
  vpmulhw       ymm12,ymm12,ymm2                     ;
  vpmulhw       ymm13,ymm13,ymm2                     ;
  vpmulhw       ymm14,ymm14,ymm3                     ;
  vpmulhw       ymm15,ymm15,ymm3                     ;
  vpmulhw       ymm6,ymm6,ymm0                       ;
  vpmulhw       ymm7,ymm7,ymm0                       ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm6,ymm12,ymm6                      ;
  vpsubw        ymm7,ymm13,ymm7                      ;
  vpsubw        ymm10,ymm14,ymm10                    ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpermq        ymm2,ymmword ptr [rdx+0160h],04eh    ;
  vpermq        ymm3,ymmword ptr [rdx+0180h],04eh    ;
  vmovdqa       ymm1,ymmword ptr [rdx]               ;
  vpshufb       ymm2,ymm2,ymm1                       ;
  vpshufb       ymm3,ymm3,ymm1                       ;
  vpsubw        ymm12,ymm8,ymm4                      ;
  vpaddw        ymm4,ymm4,ymm8                       ;
  vpsubw        ymm13,ymm9,ymm5                      ;
  vpmullw       ymm8,ymm12,ymm2                      ;
  vpaddw        ymm5,ymm5,ymm9                       ;
  vpsubw        ymm14,ymm10,ymm6                     ;
  vpmullw       ymm9,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm10                      ;
  vpsubw        ymm15,ymm11,ymm7                     ;
  vpmullw       ymm10,ymm14,ymm2                     ;
  vpaddw        ymm7,ymm7,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm3                     ;
  vpmulhw       ymm13,ymm13,ymm3                     ;
  vpmulhw       ymm14,ymm14,ymm3                     ;
  vpmulhw       ymm15,ymm15,ymm3                     ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm9,ymm9,ymm0                       ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm8,ymm12,ymm8                      ;
  vpsubw        ymm9,ymm13,ymm9                      ;
  vpsubw        ymm10,ymm14,ymm10                    ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpslld        ymm3,ymm5,010h                       ;
  vpblendw      ymm3,ymm4,ymm3,0aah                  ;
  vpsrld        ymm4,ymm4,010h                       ;
  vpblendw      ymm5,ymm4,ymm5,0aah                  ;
  vpslld        ymm4,ymm7,010h                       ;
  vpblendw      ymm4,ymm6,ymm4,0aah                  ;
  vpsrld        ymm6,ymm6,010h                       ;
  vpblendw      ymm7,ymm6,ymm7,0aah                  ;
  vpslld        ymm6,ymm9,010h                       ;
  vpblendw      ymm6,ymm8,ymm6,0aah                  ;
  vpsrld        ymm8,ymm8,010h                       ;
  vpblendw      ymm9,ymm8,ymm9,0aah                  ;
  vpslld        ymm8,ymm11,010h                      ;
  vpblendw      ymm8,ymm10,ymm8,0aah                 ;
  vpsrld        ymm10,ymm10,010h                     ;
  vpblendw      ymm11,ymm10,ymm11,0aah               ;
  vmovdqa       ymm12,ymmword ptr [rdx+020h]         ;
  vpermd        ymm2,ymm12,ymmword ptr [rdx+0120h]   ;
  vpermd        ymm10,ymm12,ymmword ptr [rdx+0140h]  ;
  vpsubw        ymm12,ymm5,ymm3                      ;
  vpaddw        ymm3,ymm3,ymm5                       ;
  vpsubw        ymm13,ymm7,ymm4                      ;
  vpmullw       ymm5,ymm12,ymm2                      ;
  vpaddw        ymm4,ymm4,ymm7                       ;
  vpsubw        ymm14,ymm9,ymm6                      ;
  vpmullw       ymm7,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm9                       ;
  vpsubw        ymm15,ymm11,ymm8                     ;
  vpmullw       ymm9,ymm14,ymm2                      ;
  vpaddw        ymm8,ymm8,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm10                    ;
  vpmulhw       ymm13,ymm13,ymm10                    ;
  vpmulhw       ymm14,ymm14,ymm10                    ;
  vpmulhw       ymm15,ymm15,ymm10                    ;
  vpmulhw       ymm5,ymm5,ymm0                       ;
  vpmulhw       ymm7,ymm7,ymm0                       ;
  vpmulhw       ymm9,ymm9,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm5,ymm12,ymm5                      ;
  vpsubw        ymm7,ymm13,ymm7                      ;
  vpsubw        ymm9,ymm14,ymm9                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  mov           eax,04ebf4ebfh                       ;
  vmovd         xmm1,eax                             ;
  vpbroadcastd  ymm1,xmm1                            ;
  vpmulhw       ymm12,ymm3,ymm1                      ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm3,ymm3,ymm12                      ;
  vmovsldup     ymm10,ymm4                           ;
  vpblendd      ymm10,ymm3,ymm10,0aah                ;
  vpsrlq        ymm3,ymm3,020h                       ;
  vpblendd      ymm4,ymm3,ymm4,0aah                  ;
  vmovsldup     ymm3,ymm8                            ;
  vpblendd      ymm3,ymm6,ymm3,0aah                  ;
  vpsrlq        ymm6,ymm6,020h                       ;
  vpblendd      ymm8,ymm6,ymm8,0aah                  ;
  vmovsldup     ymm6,ymm7                            ;
  vpblendd      ymm6,ymm5,ymm6,0aah                  ;
  vpsrlq        ymm5,ymm5,020h                       ;
  vpblendd      ymm7,ymm5,ymm7,0aah                  ;
  vmovsldup     ymm5,ymm11                           ;
  vpblendd      ymm5,ymm9,ymm5,0aah                  ;
  vpsrlq        ymm9,ymm9,020h                       ;
  vpblendd      ymm11,ymm9,ymm11,0aah                ;
  vpermq        ymm2,ymmword ptr [rdx+0e0h],01bh     ;
  vpermq        ymm9,ymmword ptr [rdx+0100h],01bh    ;
  vpsubw        ymm12,ymm4,ymm10                     ;
  vpaddw        ymm10,ymm10,ymm4                     ;
  vpsubw        ymm13,ymm8,ymm3                      ;
  vpmullw       ymm4,ymm12,ymm2                      ;
  vpaddw        ymm3,ymm3,ymm8                       ;
  vpsubw        ymm14,ymm7,ymm6                      ;
  vpmullw       ymm8,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm7                       ;
  vpsubw        ymm15,ymm11,ymm5                     ;
  vpmullw       ymm7,ymm14,ymm2                      ;
  vpaddw        ymm5,ymm5,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm9                     ;
  vpmulhw       ymm13,ymm13,ymm9                     ;
  vpmulhw       ymm14,ymm14,ymm9                     ;
  vpmulhw       ymm15,ymm15,ymm9                     ;
  vpmulhw       ymm4,ymm4,ymm0                       ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm7,ymm7,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm4,ymm12,ymm4                      ;
  vpsubw        ymm8,ymm13,ymm8                      ;
  vpsubw        ymm7,ymm14,ymm7                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpmulhw       ymm12,ymm10,ymm1                     ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm10,ymm10,ymm12                    ;
  vpunpcklqdq   ymm9,ymm10,ymm3                      ;
  vpunpckhqdq   ymm3,ymm10,ymm3                      ;
  vpunpcklqdq   ymm10,ymm6,ymm5                      ;
  vpunpckhqdq   ymm5,ymm6,ymm5                       ;
  vpunpcklqdq   ymm6,ymm4,ymm8                       ;
  vpunpckhqdq   ymm8,ymm4,ymm8                       ;
  vpunpcklqdq   ymm4,ymm7,ymm11                      ;
  vpunpckhqdq   ymm11,ymm7,ymm11                     ;
  vpermq        ymm2,ymmword ptr [rdx+0a0h],04eh     ;
  vpermq        ymm7,ymmword ptr [rdx+0c0h],04eh     ;
  vpsubw        ymm12,ymm3,ymm9                      ;
  vpaddw        ymm9,ymm9,ymm3                       ;
  vpsubw        ymm13,ymm5,ymm10                     ;
  vpmullw       ymm3,ymm12,ymm2                      ;
  vpaddw        ymm10,ymm10,ymm5                     ;
  vpsubw        ymm14,ymm8,ymm6                      ;
  vpmullw       ymm5,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm8                       ;
  vpsubw        ymm15,ymm11,ymm4                     ;
  vpmullw       ymm8,ymm14,ymm2                      ;
  vpaddw        ymm4,ymm4,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm7                     ;
  vpmulhw       ymm13,ymm13,ymm7                     ;
  vpmulhw       ymm14,ymm14,ymm7                     ;
  vpmulhw       ymm15,ymm15,ymm7                     ;
  vpmulhw       ymm3,ymm3,ymm0                       ;
  vpmulhw       ymm5,ymm5,ymm0                       ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm3,ymm12,ymm3                      ;
  vpsubw        ymm5,ymm13,ymm5                      ;
  vpsubw        ymm8,ymm14,ymm8                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpmulhw       ymm12,ymm9,ymm1                      ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm9,ymm9,ymm12                      ;
  vperm2i128    ymm7,ymm9,ymm10,020h                 ;
  vperm2i128    ymm10,ymm9,ymm10,031h                ;
  vperm2i128    ymm9,ymm6,ymm4,020h                  ;
  vperm2i128    ymm4,ymm6,ymm4,031h                  ;
  vperm2i128    ymm6,ymm3,ymm5,020h                  ;
  vperm2i128    ymm5,ymm3,ymm5,031h                  ;
  vperm2i128    ymm3,ymm8,ymm11,020h                 ;
  vperm2i128    ymm11,ymm8,ymm11,031h                ;
  vmovdqa       ymm2,ymmword ptr [rdx+060h]          ;
  vmovdqa       ymm8,ymmword ptr [rdx+080h]          ;
  vpsubw        ymm12,ymm10,ymm7                     ;
  vpaddw        ymm7,ymm7,ymm10                      ;
  vpsubw        ymm13,ymm4,ymm9                      ;
  vpmullw       ymm10,ymm12,ymm2                     ;
  vpaddw        ymm9,ymm9,ymm4                       ;
  vpsubw        ymm14,ymm5,ymm6                      ;
  vpmullw       ymm4,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm5                       ;
  vpsubw        ymm15,ymm11,ymm3                     ;
  vpmullw       ymm5,ymm14,ymm2                      ;
  vpaddw        ymm3,ymm3,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm8                     ;
  vpmulhw       ymm13,ymm13,ymm8                     ;
  vpmulhw       ymm14,ymm14,ymm8                     ;
  vpmulhw       ymm15,ymm15,ymm8                     ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm4,ymm4,ymm0                       ;
  vpmulhw       ymm5,ymm5,ymm0                       ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm10,ymm12,ymm10                    ;
  vpsubw        ymm4,ymm13,ymm4                      ;
  vpsubw        ymm5,ymm14,ymm5                      ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vpmulhw       ymm12,ymm7,ymm1                      ;
  vpsraw        ymm12,ymm12,0ah                      ;
  vpmullw       ymm12,ymm12,ymm0                     ;
  vpsubw        ymm7,ymm7,ymm12                      ;
  vmovdqa       ymmword ptr [rcx+0100h],ymm7         ;
  vmovdqa       ymmword ptr [rcx+0120h],ymm9         ;
  vmovdqa       ymmword ptr [rcx+0140h],ymm6         ;
  vmovdqa       ymmword ptr [rcx+0160h],ymm3         ;
  vmovdqa       ymmword ptr [rcx+0180h],ymm10        ;
  vmovdqa       ymmword ptr [rcx+01a0h],ymm4         ;
  vmovdqa       ymmword ptr [rcx+01c0h],ymm5         ;
  vmovdqa       ymmword ptr [rcx+01e0h],ymm11        ;
  vmovdqa       ymm4,ymmword ptr [rcx]               ;
  vmovdqa       ymm8,ymmword ptr [rcx+0100h]         ;
  vmovdqa       ymm5,ymmword ptr [rcx+020h]          ;
  vmovdqa       ymm9,ymmword ptr [rcx+0120h]         ;
  vpbroadcastq  ymm2,qword ptr [rdx+040h]            ;
  vmovdqa       ymm6,ymmword ptr [rcx+040h]          ;
  vmovdqa       ymm10,ymmword ptr [rcx+0140h]        ;
  vmovdqa       ymm7,ymmword ptr [rcx+060h]          ;
  vmovdqa       ymm11,ymmword ptr [rcx+0160h]        ;
  vpbroadcastq  ymm3,qword ptr [rdx+048h]            ;
  vpsubw        ymm12,ymm8,ymm4                      ;
  vpaddw        ymm4,ymm4,ymm8                       ;
  vpsubw        ymm13,ymm9,ymm5                      ;
  vpmullw       ymm8,ymm12,ymm2                      ;
  vpaddw        ymm5,ymm5,ymm9                       ;
  vpsubw        ymm14,ymm10,ymm6                     ;
  vpmullw       ymm9,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm10                      ;
  vpsubw        ymm15,ymm11,ymm7                     ;
  vpmullw       ymm10,ymm14,ymm2                     ;
  vpaddw        ymm7,ymm7,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm3                     ;
  vpmulhw       ymm13,ymm13,ymm3                     ;
  vpmulhw       ymm14,ymm14,ymm3                     ;
  vpmulhw       ymm15,ymm15,ymm3                     ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm9,ymm9,ymm0                       ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm8,ymm12,ymm8                      ;
  vpsubw        ymm9,ymm13,ymm9                      ;
  vpsubw        ymm10,ymm14,ymm10                    ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vmovdqa       ymmword ptr [rcx],ymm4               ;
  vmovdqa       ymmword ptr [rcx+020h],ymm5          ;
  vmovdqa       ymmword ptr [rcx+040h],ymm6          ;
  vmovdqa       ymmword ptr [rcx+060h],ymm7          ;
  vmovdqa       ymmword ptr [rcx+0100h],ymm8         ;
  vmovdqa       ymmword ptr [rcx+0120h],ymm9         ;
  vmovdqa       ymmword ptr [rcx+0140h],ymm10        ;
  vmovdqa       ymmword ptr [rcx+0160h],ymm11        ;
  vmovdqa       ymm4,ymmword ptr [rcx+080h]          ;
  vmovdqa       ymm8,ymmword ptr [rcx+0180h]         ;
  vmovdqa       ymm5,ymmword ptr [rcx+0a0h]          ;
  vmovdqa       ymm9,ymmword ptr [rcx+01a0h]         ;
  vpbroadcastq  ymm2,qword ptr [rdx+040h]            ;
  vmovdqa       ymm6,ymmword ptr [rcx+0c0h]          ;
  vmovdqa       ymm10,ymmword ptr [rcx+01c0h]        ;
  vmovdqa       ymm7,ymmword ptr [rcx+0e0h]          ;
  vmovdqa       ymm11,ymmword ptr [rcx+01e0h]        ;
  vpbroadcastq  ymm3,qword ptr [rdx+048h]            ;
  vpsubw        ymm12,ymm8,ymm4                      ;
  vpaddw        ymm4,ymm4,ymm8                       ;
  vpsubw        ymm13,ymm9,ymm5                      ;
  vpmullw       ymm8,ymm12,ymm2                      ;
  vpaddw        ymm5,ymm5,ymm9                       ;
  vpsubw        ymm14,ymm10,ymm6                     ;
  vpmullw       ymm9,ymm13,ymm2                      ;
  vpaddw        ymm6,ymm6,ymm10                      ;
  vpsubw        ymm15,ymm11,ymm7                     ;
  vpmullw       ymm10,ymm14,ymm2                     ;
  vpaddw        ymm7,ymm7,ymm11                      ;
  vpmullw       ymm11,ymm15,ymm2                     ;
  vpmulhw       ymm12,ymm12,ymm3                     ;
  vpmulhw       ymm13,ymm13,ymm3                     ;
  vpmulhw       ymm14,ymm14,ymm3                     ;
  vpmulhw       ymm15,ymm15,ymm3                     ;
  vpmulhw       ymm8,ymm8,ymm0                       ;
  vpmulhw       ymm9,ymm9,ymm0                       ;
  vpmulhw       ymm10,ymm10,ymm0                     ;
  vpmulhw       ymm11,ymm11,ymm0                     ;
  vpsubw        ymm8,ymm12,ymm8                      ;
  vpsubw        ymm9,ymm13,ymm9                      ;
  vpsubw        ymm10,ymm14,ymm10                    ;
  vpsubw        ymm11,ymm15,ymm11                    ;
  vmovdqa       ymmword ptr [rcx+080h],ymm4          ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm5          ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm6          ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm7          ;
  vmovdqa       ymmword ptr [rcx+0180h],ymm8         ;
  vmovdqa       ymmword ptr [rcx+01a0h],ymm9         ;
  vmovdqa       ymmword ptr [rcx+01c0h],ymm10        ;
  vmovdqa       ymmword ptr [rcx+01e0h],ymm11        ;

  vzeroupper                                         ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]          ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]          ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]          ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]          ; restore xmm9 from stack
  vmovdqa       xmm10,xmmword ptr [rsp+040h]         ; restore xmm10 from stack
  vmovdqa       xmm11,xmmword ptr [rsp+050h]         ; restore xmm11 from stack
  vmovdqa       xmm12,xmmword ptr [rsp+060h]         ; restore xmm12 from stack
  vmovdqa       xmm13,xmmword ptr [rsp+070h]         ; restore xmm13 from stack
  vmovdqa       xmm14,xmmword ptr [rsp+080h]         ; restore xmm14 from stack
  vmovdqa       xmm15,xmmword ptr [rsp+090h]         ; restore xmm15 from stack

  add           rsp,0A8h                             ; 0A8h and not 0A0h for alignment purposes

  ret                                                ;

FUNC_NAME ENDP

          END
