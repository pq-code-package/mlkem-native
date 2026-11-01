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
; Name: poly_compress_d10_avx2_asm
; Description: x86_64 AVX2 polynomial compression (d=10)
; Signature: void mlk_poly_compress_d10_avx2_asm(uint8_t *r, const int16_t *a, const uint8_t *data)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 320
;     permissions: write-only
;     c_parameter: uint8_t *r
;     description: Output compressed polynomial
;   rdx:
;     type: buffer
;     size_bytes: 512
;     permissions: read-only
;     c_parameter: const int16_t *a
;     description: Input polynomial (256 x int16_t)
;   r8:
;     type: buffer
;     size_bytes: 32
;     permissions: read-only
;     c_parameter: const uint8_t *data
;     description: Precomputed compression constants
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_poly_compress_d10_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,058h                      ; 058h and not 050h for alignment purposes
  .allocstack   058h

  vmovdqa       xmmword ptr [rsp+000h],xmm6   ; save xmm6 on stack
  .savexmm128    xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7   ; save xmm7 on stack
  .savexmm128    xmm7,010h
  vmovdqa       xmmword ptr [rsp+020h],xmm8   ; save xmm8 on stack
  .savexmm128    xmm8,020h
  vmovdqa       xmmword ptr [rsp+030h],xmm9   ; save xmm9 on stack
  .savexmm128    xmm9,030h
  vmovdqa       xmmword ptr [rsp+040h],xmm10  ; save xmm10 on stack
  .savexmm128    xmm10,040h
  .endprolog

  mov           eax,04ebf4ebfh                ;
  vmovd         xmm0,eax                      ;
  vpbroadcastd  ymm0,xmm0                     ;
  vpsllw        ymm1,ymm0,03h                 ;
  mov           eax,0f000fh                   ;
  vmovd         xmm2,eax                      ;
  vpbroadcastd  ymm2,xmm2                     ;
  mov           eax,010001000h                ;
  vmovd         xmm3,eax                      ;
  vpbroadcastd  ymm3,xmm3                     ;
  mov           eax,03ff03ffh                 ;
  vmovd         xmm4,eax                      ;
  vpbroadcastd  ymm4,xmm4                     ;
  mov           rax,0400000104000001h         ;
  vmovq         xmm5,rax                      ;
  vpbroadcastq  ymm5,xmm5                     ;
  mov           eax,0ch                       ;
  vmovq         xmm6,rax                      ;
  vpbroadcastq  ymm6,xmm6                     ;
  vmovdqa       ymm7,ymmword ptr [r8]         ;
  vmovdqa       ymm8,ymmword ptr [rdx]        ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx],xmm8        ;
  vmovd         dword ptr [rcx+010h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+020h]   ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+014h],xmm8   ;
  vmovd         dword ptr [rcx+024h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+040h]   ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+028h],xmm8   ;
  vmovd         dword ptr [rcx+038h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+060h]   ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+03ch],xmm8   ;
  vmovd         dword ptr [rcx+04ch],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+080h]   ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+050h],xmm8   ;
  vmovd         dword ptr [rcx+060h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0a0h]   ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+064h],xmm8   ;
  vmovd         dword ptr [rcx+074h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0c0h]   ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+078h],xmm8   ;
  vmovd         dword ptr [rcx+088h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0e0h]   ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+08ch],xmm8   ;
  vmovd         dword ptr [rcx+09ch],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0100h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+0a0h],xmm8   ;
  vmovd         dword ptr [rcx+0b0h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0120h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+0b4h],xmm8   ;
  vmovd         dword ptr [rcx+0c4h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0140h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+0c8h],xmm8   ;
  vmovd         dword ptr [rcx+0d8h],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0160h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+0dch],xmm8   ;
  vmovd         dword ptr [rcx+0ech],xmm9     ;
  vmovdqa       ymm8,ymmword ptr [rdx+0180h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+0f0h],xmm8   ;
  vmovd         dword ptr [rcx+0100h],xmm9    ;
  vmovdqa       ymm8,ymmword ptr [rdx+01a0h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+0104h],xmm8  ;
  vmovd         dword ptr [rcx+0114h],xmm9    ;
  vmovdqa       ymm8,ymmword ptr [rdx+01c0h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+0118h],xmm8  ;
  vmovd         dword ptr [rcx+0128h],xmm9    ;
  vmovdqa       ymm8,ymmword ptr [rdx+01e0h]  ;
  vpmullw       ymm9,ymm8,ymm1                ;
  vpaddw        ymm10,ymm8,ymm2               ;
  vpsllw        ymm8,ymm8,03h                 ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpsubw        ymm10,ymm9,ymm10              ;
  vpandn        ymm9,ymm9,ymm10               ;
  vpsrlw        ymm9,ymm9,0fh                 ;
  vpsubw        ymm8,ymm8,ymm9                ;
  vpmulhrsw     ymm8,ymm8,ymm3                ;
  vpand         ymm8,ymm8,ymm4                ;
  vpmaddwd      ymm8,ymm8,ymm5                ;
  vpsllvd       ymm8,ymm8,ymm6                ;
  vpsrlq        ymm8,ymm8,0ch                 ;
  vpshufb       ymm8,ymm8,ymm7                ;
  vextracti128  xmm9,ymm8,01h                 ;
  vpblendw      xmm8,xmm8,xmm9,0e0h           ;
  vmovdqu       xmmword ptr [rcx+012ch],xmm8  ;
  vmovd         dword ptr [rcx+013ch],xmm9    ;

  vzeroupper                                  ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]   ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]   ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]   ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]   ; restore xmm9 from stack
  vmovdqa       xmm10,xmmword ptr [rsp+040h]  ; restore xmm10 from stack

  add           rsp,058h                      ; 058h and not 050h for alignment purposes

  ret                                         ;

FUNC_NAME ENDP

  END
