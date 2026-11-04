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
; Name: poly_compress_d11_avx2_asm
; Description: x86_64 AVX2 polynomial compression (d=11)
; Signature: void mlk_poly_compress_d11_avx2_asm(uint8_t *r, const int16_t *a, const uint8_t *data)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 352
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
;     size_bytes: 64
;     permissions: read-only
;     c_parameter: const uint8_t *data
;     description: Precomputed compression constants
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_poly_compress_d11_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,068h                        ; 068h and not 060h for alignment purposes
  .allocstack   068h

  vmovdqa       xmmword ptr [rsp+000h],xmm6     ; save xmm6 on stack
  .savexmm128    xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7     ; save xmm7 on stack
  .savexmm128    xmm7,010h
  vmovdqa       xmmword ptr [rsp+020h],xmm8     ; save xmm8 on stack
  .savexmm128    xmm8,020h
  vmovdqa       xmmword ptr [rsp+030h],xmm9     ; save xmm9 on stack
  .savexmm128    xmm9,030h
  vmovdqa       xmmword ptr [rsp+040h],xmm10    ; save xmm10 on stack
  .savexmm128    xmm10,040h
  vmovdqa       xmmword ptr [rsp+050h],xmm11    ; save xmm11 on stack
  .savexmm128    xmm11,050h
  .endprolog

  mov           eax,04ebf4ebfh                  ;
  vmovd         xmm0,eax                        ;
  vpbroadcastd  ymm0,xmm0                       ;
  vpsllw        ymm1,ymm0,03h                   ;
  mov           eax,0240024h                    ;
  vmovd         xmm2,eax                        ;
  vpbroadcastd  ymm2,xmm2                       ;
  mov           eax,020002000h                  ;
  vmovd         xmm3,eax                        ;
  vpbroadcastd  ymm3,xmm3                       ;
  mov           eax,07ff07ffh                   ;
  vmovd         xmm4,eax                        ;
  vpbroadcastd  ymm4,xmm4                       ;
  mov           rax,0800000108000001h           ;
  vmovq         xmm5,rax                        ;
  vpbroadcastq  ymm5,xmm5                       ;
  mov           eax,0ah                         ;
  vmovq         xmm6,rax                        ;
  vpbroadcastq  ymm6,xmm6                       ;
  vmovdqa       ymm7,ymmword ptr [r8]           ;
  vmovdqa       ymm8,ymmword ptr [r8+020h]      ;
  vmovdqa       ymm9,ymmword ptr [rdx]          ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx],xmm9          ;
  vmovd         dword ptr [rcx+010h],xmm10      ;
  vpextrw       word ptr [rcx+014h],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+020h]     ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+016h],xmm9     ;
  vmovd         dword ptr [rcx+026h],xmm10      ;
  vpextrw       word ptr [rcx+02ah],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+040h]     ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+02ch],xmm9     ;
  vmovd         dword ptr [rcx+03ch],xmm10      ;
  vpextrw       word ptr [rcx+040h],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+060h]     ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+042h],xmm9     ;
  vmovd         dword ptr [rcx+052h],xmm10      ;
  vpextrw       word ptr [rcx+056h],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+080h]     ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+058h],xmm9     ;
  vmovd         dword ptr [rcx+068h],xmm10      ;
  vpextrw       word ptr [rcx+06ch],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0a0h]     ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+06eh],xmm9     ;
  vmovd         dword ptr [rcx+07eh],xmm10      ;
  vpextrw       word ptr [rcx+082h],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0c0h]     ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+084h],xmm9     ;
  vmovd         dword ptr [rcx+094h],xmm10      ;
  vpextrw       word ptr [rcx+098h],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0e0h]     ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+09ah],xmm9     ;
  vmovd         dword ptr [rcx+0aah],xmm10      ;
  vpextrw       word ptr [rcx+0aeh],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0100h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+0b0h],xmm9     ;
  vmovd         dword ptr [rcx+0c0h],xmm10      ;
  vpextrw       word ptr [rcx+0c4h],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0120h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+0c6h],xmm9     ;
  vmovd         dword ptr [rcx+0d6h],xmm10      ;
  vpextrw       word ptr [rcx+0dah],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0140h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+0dch],xmm9     ;
  vmovd         dword ptr [rcx+0ech],xmm10      ;
  vpextrw       word ptr [rcx+0f0h],xmm10,02h   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0160h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+0f2h],xmm9     ;
  vmovd         dword ptr [rcx+0102h],xmm10     ;
  vpextrw       word ptr [rcx+0106h],xmm10,02h  ;
  vmovdqa       ymm9,ymmword ptr [rdx+0180h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+0108h],xmm9    ;
  vmovd         dword ptr [rcx+0118h],xmm10     ;
  vpextrw       word ptr [rcx+011ch],xmm10,02h  ;
  vmovdqa       ymm9,ymmword ptr [rdx+01a0h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+011eh],xmm9    ;
  vmovd         dword ptr [rcx+012eh],xmm10     ;
  vpextrw       word ptr [rcx+0132h],xmm10,02h  ;
  vmovdqa       ymm9,ymmword ptr [rdx+01c0h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+0134h],xmm9    ;
  vmovd         dword ptr [rcx+0144h],xmm10     ;
  vpextrw       word ptr [rcx+0148h],xmm10,02h  ;
  vmovdqa       ymm9,ymmword ptr [rdx+01e0h]    ;
  vpmullw       ymm10,ymm9,ymm1                 ;
  vpaddw        ymm11,ymm9,ymm2                 ;
  vpsllw        ymm9,ymm9,03h                   ;
  vpmulhw       ymm9,ymm9,ymm0                  ;
  vpsubw        ymm11,ymm10,ymm11               ;
  vpandn        ymm10,ymm10,ymm11               ;
  vpsrlw        ymm10,ymm10,0fh                 ;
  vpsubw        ymm9,ymm9,ymm10                 ;
  vpmulhrsw     ymm9,ymm9,ymm3                  ;
  vpand         ymm9,ymm9,ymm4                  ;
  vpmaddwd      ymm9,ymm9,ymm5                  ;
  vpsllvd       ymm9,ymm9,ymm6                  ;
  vpsrldq       ymm10,ymm9,08h                  ;
  vpsrlvq       ymm9,ymm9,ymm7                  ;
  vpsllq        ymm10,ymm10,022h                ;
  vpaddq        ymm9,ymm9,ymm10                 ;
  vpshufb       ymm9,ymm9,ymm8                  ;
  vextracti128  xmm10,ymm9,01h                  ;
  vpblendvb     xmm9,xmm9,xmm10,xmm8            ;
  vmovdqu       xmmword ptr [rcx+014ah],xmm9    ;
  vmovd         dword ptr [rcx+015ah],xmm10     ;
  vpextrw       word ptr [rcx+015eh],xmm10,02h  ;

  vzeroupper                                    ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]     ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]     ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]     ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]     ; restore xmm9 from stack
  vmovdqa       xmm10,xmmword ptr [rsp+040h]    ; restore xmm10 from stack
  vmovdqa       xmm11,xmmword ptr [rsp+050h]    ; restore xmm11 from stack

  add           rsp,068h                        ; 068h and not 060h for alignment purposes

  ret                                           ;

FUNC_NAME ENDP

  END
