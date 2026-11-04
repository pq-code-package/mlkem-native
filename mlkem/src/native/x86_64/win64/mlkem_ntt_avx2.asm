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
; Name: ntt_avx2_asm
; Description: x86_64 AVX2 forward NTT
; Signature: void mlk_ntt_avx2_asm(int16_t *r, const int16_t *qdata)
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
FUNC_NAME EQU mlkem_ntt_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,0A8h                       ; 0A8h and not 0A0h for alignment purposes
  .allocstack   0A8h

  vmovdqa       xmmword ptr [rsp+000h],xmm6    ; save xmm6 on stack
  .savexmm128    xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7    ; save xmm7 on stack
  .savexmm128    xmm7,010h
  vmovdqa       xmmword ptr [rsp+020h],xmm8    ; save xmm8 on stack
  .savexmm128    xmm8,020h
  vmovdqa       xmmword ptr [rsp+030h],xmm9    ; save xmm9 on stack
  .savexmm128    xmm9,030h
  vmovdqa       xmmword ptr [rsp+040h],xmm10   ; save xmm10 on stack
  .savexmm128    xmm10,040h
  vmovdqa       xmmword ptr [rsp+050h],xmm11   ; save xmm11 on stack
  .savexmm128    xmm11,050h
  vmovdqa       xmmword ptr [rsp+060h],xmm12   ; save xmm12 on stack
  .savexmm128    xmm12,060h
  vmovdqa       xmmword ptr [rsp+070h],xmm13   ; save xmm13 on stack
  .savexmm128    xmm13,070h
  vmovdqa       xmmword ptr [rsp+080h],xmm14   ; save xmm14 on stack
  .savexmm128    xmm14,080h
  vmovdqa       xmmword ptr [rsp+090h],xmm15   ; save xmm15 on stack
  .savexmm128    xmm15,090h
  .endprolog

  mov           eax,0d010d01h                  ;
  vmovd         xmm0,eax                       ;
  vpbroadcastd  ymm0,xmm0                      ;
  vpbroadcastq  ymm15,qword ptr [rdx+040h]     ;
  vmovdqa       ymm8,ymmword ptr [rcx+0100h]   ;
  vmovdqa       ymm9,ymmword ptr [rcx+0120h]   ;
  vmovdqa       ymm10,ymmword ptr [rcx+0140h]  ;
  vmovdqa       ymm11,ymmword ptr [rcx+0160h]  ;
  vpbroadcastq  ymm2,qword ptr [rdx+048h]      ;
  vpmullw       ymm12,ymm8,ymm15               ;
  vpmullw       ymm13,ymm9,ymm15               ;
  vpmullw       ymm14,ymm10,ymm15              ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vmovdqa       ymm4,ymmword ptr [rcx]         ;
  vmovdqa       ymm5,ymmword ptr [rcx+020h]    ;
  vmovdqa       ymm6,ymmword ptr [rcx+040h]    ;
  vmovdqa       ymm7,ymmword ptr [rcx+060h]    ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm3,ymm4,ymm8                 ;
  vpsubw        ymm8,ymm4,ymm8                 ;
  vpaddw        ymm4,ymm5,ymm9                 ;
  vpsubw        ymm9,ymm5,ymm9                 ;
  vpaddw        ymm5,ymm6,ymm10                ;
  vpsubw        ymm10,ymm6,ymm10               ;
  vpaddw        ymm6,ymm7,ymm11                ;
  vpsubw        ymm11,ymm7,ymm11               ;
  vpsubw        ymm3,ymm3,ymm12                ;
  vpaddw        ymm8,ymm8,ymm12                ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm9,ymm9,ymm13                ;
  vpsubw        ymm5,ymm5,ymm14                ;
  vpaddw        ymm10,ymm10,ymm14              ;
  vpsubw        ymm6,ymm6,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovdqa       ymmword ptr [rcx],ymm3         ;
  vmovdqa       ymmword ptr [rcx+020h],ymm4    ;
  vmovdqa       ymmword ptr [rcx+040h],ymm5    ;
  vmovdqa       ymmword ptr [rcx+060h],ymm6    ;
  vmovdqa       ymmword ptr [rcx+0100h],ymm8   ;
  vmovdqa       ymmword ptr [rcx+0120h],ymm9   ;
  vmovdqa       ymmword ptr [rcx+0140h],ymm10  ;
  vmovdqa       ymmword ptr [rcx+0160h],ymm11  ;
  vpbroadcastq  ymm15,qword ptr [rdx+040h]     ;
  vmovdqa       ymm8,ymmword ptr [rcx+0180h]   ;
  vmovdqa       ymm9,ymmword ptr [rcx+01a0h]   ;
  vmovdqa       ymm10,ymmword ptr [rcx+01c0h]  ;
  vmovdqa       ymm11,ymmword ptr [rcx+01e0h]  ;
  vpbroadcastq  ymm2,qword ptr [rdx+048h]      ;
  vpmullw       ymm12,ymm8,ymm15               ;
  vpmullw       ymm13,ymm9,ymm15               ;
  vpmullw       ymm14,ymm10,ymm15              ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vmovdqa       ymm4,ymmword ptr [rcx+080h]    ;
  vmovdqa       ymm5,ymmword ptr [rcx+0a0h]    ;
  vmovdqa       ymm6,ymmword ptr [rcx+0c0h]    ;
  vmovdqa       ymm7,ymmword ptr [rcx+0e0h]    ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm3,ymm4,ymm8                 ;
  vpsubw        ymm8,ymm4,ymm8                 ;
  vpaddw        ymm4,ymm5,ymm9                 ;
  vpsubw        ymm9,ymm5,ymm9                 ;
  vpaddw        ymm5,ymm6,ymm10                ;
  vpsubw        ymm10,ymm6,ymm10               ;
  vpaddw        ymm6,ymm7,ymm11                ;
  vpsubw        ymm11,ymm7,ymm11               ;
  vpsubw        ymm3,ymm3,ymm12                ;
  vpaddw        ymm8,ymm8,ymm12                ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm9,ymm9,ymm13                ;
  vpsubw        ymm5,ymm5,ymm14                ;
  vpaddw        ymm10,ymm10,ymm14              ;
  vpsubw        ymm6,ymm6,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovdqa       ymmword ptr [rcx+080h],ymm3    ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm4    ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm5    ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm6    ;
  vmovdqa       ymmword ptr [rcx+0180h],ymm8   ;
  vmovdqa       ymmword ptr [rcx+01a0h],ymm9   ;
  vmovdqa       ymmword ptr [rcx+01c0h],ymm10  ;
  vmovdqa       ymmword ptr [rcx+01e0h],ymm11  ;
  vmovdqa       ymm15,ymmword ptr [rdx+060h]   ;
  vmovdqa       ymm8,ymmword ptr [rcx+080h]    ;
  vmovdqa       ymm9,ymmword ptr [rcx+0a0h]    ;
  vmovdqa       ymm10,ymmword ptr [rcx+0c0h]   ;
  vmovdqa       ymm11,ymmword ptr [rcx+0e0h]   ;
  vmovdqa       ymm2,ymmword ptr [rdx+080h]    ;
  vpmullw       ymm12,ymm8,ymm15               ;
  vpmullw       ymm13,ymm9,ymm15               ;
  vpmullw       ymm14,ymm10,ymm15              ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vmovdqa       ymm4,ymmword ptr [rcx]         ;
  vmovdqa       ymm5,ymmword ptr [rcx+020h]    ;
  vmovdqa       ymm6,ymmword ptr [rcx+040h]    ;
  vmovdqa       ymm7,ymmword ptr [rcx+060h]    ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm3,ymm4,ymm8                 ;
  vpsubw        ymm8,ymm4,ymm8                 ;
  vpaddw        ymm4,ymm5,ymm9                 ;
  vpsubw        ymm9,ymm5,ymm9                 ;
  vpaddw        ymm5,ymm6,ymm10                ;
  vpsubw        ymm10,ymm6,ymm10               ;
  vpaddw        ymm6,ymm7,ymm11                ;
  vpsubw        ymm11,ymm7,ymm11               ;
  vpsubw        ymm3,ymm3,ymm12                ;
  vpaddw        ymm8,ymm8,ymm12                ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm9,ymm9,ymm13                ;
  vpsubw        ymm5,ymm5,ymm14                ;
  vpaddw        ymm10,ymm10,ymm14              ;
  vpsubw        ymm6,ymm6,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vperm2i128    ymm7,ymm5,ymm10,020h           ;
  vperm2i128    ymm10,ymm5,ymm10,031h          ;
  vperm2i128    ymm5,ymm6,ymm11,020h           ;
  vperm2i128    ymm11,ymm6,ymm11,031h          ;
  vmovdqa       ymm15,ymmword ptr [rdx+0a0h]   ;
  vmovdqa       ymm2,ymmword ptr [rdx+0c0h]    ;
  vpmullw       ymm12,ymm7,ymm15               ;
  vpmullw       ymm13,ymm10,ymm15              ;
  vpmullw       ymm14,ymm5,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vperm2i128    ymm6,ymm3,ymm8,020h            ;
  vperm2i128    ymm8,ymm3,ymm8,031h            ;
  vperm2i128    ymm3,ymm4,ymm9,020h            ;
  vperm2i128    ymm9,ymm4,ymm9,031h            ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm4,ymm6,ymm7                 ;
  vpsubw        ymm7,ymm6,ymm7                 ;
  vpaddw        ymm6,ymm8,ymm10                ;
  vpsubw        ymm10,ymm8,ymm10               ;
  vpaddw        ymm8,ymm3,ymm5                 ;
  vpsubw        ymm5,ymm3,ymm5                 ;
  vpaddw        ymm3,ymm9,ymm11                ;
  vpsubw        ymm11,ymm9,ymm11               ;
  vpsubw        ymm4,ymm4,ymm12                ;
  vpaddw        ymm7,ymm7,ymm12                ;
  vpsubw        ymm6,ymm6,ymm13                ;
  vpaddw        ymm10,ymm10,ymm13              ;
  vpsubw        ymm8,ymm8,ymm14                ;
  vpaddw        ymm5,ymm5,ymm14                ;
  vpsubw        ymm3,ymm3,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vpunpcklqdq   ymm9,ymm8,ymm5                 ;
  vpunpckhqdq   ymm5,ymm8,ymm5                 ;
  vpunpcklqdq   ymm8,ymm3,ymm11                ;
  vpunpckhqdq   ymm11,ymm3,ymm11               ;
  vmovdqa       ymm15,ymmword ptr [rdx+0e0h]   ;
  vmovdqa       ymm2,ymmword ptr [rdx+0100h]   ;
  vpmullw       ymm12,ymm9,ymm15               ;
  vpmullw       ymm13,ymm5,ymm15               ;
  vpmullw       ymm14,ymm8,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vpunpcklqdq   ymm3,ymm4,ymm7                 ;
  vpunpckhqdq   ymm7,ymm4,ymm7                 ;
  vpunpcklqdq   ymm4,ymm6,ymm10                ;
  vpunpckhqdq   ymm10,ymm6,ymm10               ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm6,ymm3,ymm9                 ;
  vpsubw        ymm9,ymm3,ymm9                 ;
  vpaddw        ymm3,ymm7,ymm5                 ;
  vpsubw        ymm5,ymm7,ymm5                 ;
  vpaddw        ymm7,ymm4,ymm8                 ;
  vpsubw        ymm8,ymm4,ymm8                 ;
  vpaddw        ymm4,ymm10,ymm11               ;
  vpsubw        ymm11,ymm10,ymm11              ;
  vpsubw        ymm6,ymm6,ymm12                ;
  vpaddw        ymm9,ymm9,ymm12                ;
  vpsubw        ymm3,ymm3,ymm13                ;
  vpaddw        ymm5,ymm5,ymm13                ;
  vpsubw        ymm7,ymm7,ymm14                ;
  vpaddw        ymm8,ymm8,ymm14                ;
  vpsubw        ymm4,ymm4,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovsldup     ymm10,ymm8                     ;
  vpblendd      ymm10,ymm7,ymm10,0aah          ;
  vpsrlq        ymm7,ymm7,020h                 ;
  vpblendd      ymm8,ymm7,ymm8,0aah            ;
  vmovsldup     ymm7,ymm11                     ;
  vpblendd      ymm7,ymm4,ymm7,0aah            ;
  vpsrlq        ymm4,ymm4,020h                 ;
  vpblendd      ymm11,ymm4,ymm11,0aah          ;
  vmovdqa       ymm15,ymmword ptr [rdx+0120h]  ;
  vmovdqa       ymm2,ymmword ptr [rdx+0140h]   ;
  vpmullw       ymm12,ymm10,ymm15              ;
  vpmullw       ymm13,ymm8,ymm15               ;
  vpmullw       ymm14,ymm7,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vmovsldup     ymm4,ymm9                      ;
  vpblendd      ymm4,ymm6,ymm4,0aah            ;
  vpsrlq        ymm6,ymm6,020h                 ;
  vpblendd      ymm9,ymm6,ymm9,0aah            ;
  vmovsldup     ymm6,ymm5                      ;
  vpblendd      ymm6,ymm3,ymm6,0aah            ;
  vpsrlq        ymm3,ymm3,020h                 ;
  vpblendd      ymm5,ymm3,ymm5,0aah            ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm3,ymm4,ymm10                ;
  vpsubw        ymm10,ymm4,ymm10               ;
  vpaddw        ymm4,ymm9,ymm8                 ;
  vpsubw        ymm8,ymm9,ymm8                 ;
  vpaddw        ymm9,ymm6,ymm7                 ;
  vpsubw        ymm7,ymm6,ymm7                 ;
  vpaddw        ymm6,ymm5,ymm11                ;
  vpsubw        ymm11,ymm5,ymm11               ;
  vpsubw        ymm3,ymm3,ymm12                ;
  vpaddw        ymm10,ymm10,ymm12              ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm8,ymm8,ymm13                ;
  vpsubw        ymm9,ymm9,ymm14                ;
  vpaddw        ymm7,ymm7,ymm14                ;
  vpsubw        ymm6,ymm6,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vpslld        ymm5,ymm7,010h                 ;
  vpblendw      ymm5,ymm9,ymm5,0aah            ;
  vpsrld        ymm9,ymm9,010h                 ;
  vpblendw      ymm7,ymm9,ymm7,0aah            ;
  vpslld        ymm9,ymm11,010h                ;
  vpblendw      ymm9,ymm6,ymm9,0aah            ;
  vpsrld        ymm6,ymm6,010h                 ;
  vpblendw      ymm11,ymm6,ymm11,0aah          ;
  vmovdqa       ymm15,ymmword ptr [rdx+0160h]  ;
  vmovdqa       ymm2,ymmword ptr [rdx+0180h]   ;
  vpmullw       ymm12,ymm5,ymm15               ;
  vpmullw       ymm13,ymm7,ymm15               ;
  vpmullw       ymm14,ymm9,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vpslld        ymm6,ymm10,010h                ;
  vpblendw      ymm6,ymm3,ymm6,0aah            ;
  vpsrld        ymm3,ymm3,010h                 ;
  vpblendw      ymm10,ymm3,ymm10,0aah          ;
  vpslld        ymm3,ymm8,010h                 ;
  vpblendw      ymm3,ymm4,ymm3,0aah            ;
  vpsrld        ymm4,ymm4,010h                 ;
  vpblendw      ymm8,ymm4,ymm8,0aah            ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm4,ymm6,ymm5                 ;
  vpsubw        ymm5,ymm6,ymm5                 ;
  vpaddw        ymm6,ymm10,ymm7                ;
  vpsubw        ymm7,ymm10,ymm7                ;
  vpaddw        ymm10,ymm3,ymm9                ;
  vpsubw        ymm9,ymm3,ymm9                 ;
  vpaddw        ymm3,ymm8,ymm11                ;
  vpsubw        ymm11,ymm8,ymm11               ;
  vpsubw        ymm4,ymm4,ymm12                ;
  vpaddw        ymm5,ymm5,ymm12                ;
  vpsubw        ymm6,ymm6,ymm13                ;
  vpaddw        ymm7,ymm7,ymm13                ;
  vpsubw        ymm10,ymm10,ymm14              ;
  vpaddw        ymm9,ymm9,ymm14                ;
  vpsubw        ymm3,ymm3,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovdqa       ymm14,ymmword ptr [rdx+01a0h]  ;
  vmovdqa       ymm15,ymmword ptr [rdx+01e0h]  ;
  vmovdqa       ymm8,ymmword ptr [rdx+01c0h]   ;
  vmovdqa       ymm2,ymmword ptr [rdx+0200h]   ;
  vpmullw       ymm12,ymm10,ymm14              ;
  vpmullw       ymm13,ymm3,ymm14               ;
  vpmullw       ymm14,ymm9,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm10,ymm10,ymm8               ;
  vpmulhw       ymm3,ymm3,ymm8                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm8,ymm4,ymm10                ;
  vpsubw        ymm10,ymm4,ymm10               ;
  vpaddw        ymm4,ymm6,ymm3                 ;
  vpsubw        ymm3,ymm6,ymm3                 ;
  vpaddw        ymm6,ymm5,ymm9                 ;
  vpsubw        ymm9,ymm5,ymm9                 ;
  vpaddw        ymm5,ymm7,ymm11                ;
  vpsubw        ymm11,ymm7,ymm11               ;
  vpsubw        ymm8,ymm8,ymm12                ;
  vpaddw        ymm10,ymm10,ymm12              ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm3,ymm3,ymm13                ;
  vpsubw        ymm6,ymm6,ymm14                ;
  vpaddw        ymm9,ymm9,ymm14                ;
  vpsubw        ymm5,ymm5,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovdqa       ymmword ptr [rcx],ymm8         ;
  vmovdqa       ymmword ptr [rcx+020h],ymm4    ;
  vmovdqa       ymmword ptr [rcx+040h],ymm10   ;
  vmovdqa       ymmword ptr [rcx+060h],ymm3    ;
  vmovdqa       ymmword ptr [rcx+080h],ymm6    ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm5    ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm9    ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm11   ;
  vmovdqa       ymm15,ymmword ptr [rdx+0220h]  ;
  vmovdqa       ymm8,ymmword ptr [rcx+0180h]   ;
  vmovdqa       ymm9,ymmword ptr [rcx+01a0h]   ;
  vmovdqa       ymm10,ymmword ptr [rcx+01c0h]  ;
  vmovdqa       ymm11,ymmword ptr [rcx+01e0h]  ;
  vmovdqa       ymm2,ymmword ptr [rdx+0240h]   ;
  vpmullw       ymm12,ymm8,ymm15               ;
  vpmullw       ymm13,ymm9,ymm15               ;
  vpmullw       ymm14,ymm10,ymm15              ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vmovdqa       ymm4,ymmword ptr [rcx+0100h]   ;
  vmovdqa       ymm5,ymmword ptr [rcx+0120h]   ;
  vmovdqa       ymm6,ymmword ptr [rcx+0140h]   ;
  vmovdqa       ymm7,ymmword ptr [rcx+0160h]   ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm3,ymm4,ymm8                 ;
  vpsubw        ymm8,ymm4,ymm8                 ;
  vpaddw        ymm4,ymm5,ymm9                 ;
  vpsubw        ymm9,ymm5,ymm9                 ;
  vpaddw        ymm5,ymm6,ymm10                ;
  vpsubw        ymm10,ymm6,ymm10               ;
  vpaddw        ymm6,ymm7,ymm11                ;
  vpsubw        ymm11,ymm7,ymm11               ;
  vpsubw        ymm3,ymm3,ymm12                ;
  vpaddw        ymm8,ymm8,ymm12                ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm9,ymm9,ymm13                ;
  vpsubw        ymm5,ymm5,ymm14                ;
  vpaddw        ymm10,ymm10,ymm14              ;
  vpsubw        ymm6,ymm6,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vperm2i128    ymm7,ymm5,ymm10,020h           ;
  vperm2i128    ymm10,ymm5,ymm10,031h          ;
  vperm2i128    ymm5,ymm6,ymm11,020h           ;
  vperm2i128    ymm11,ymm6,ymm11,031h          ;
  vmovdqa       ymm15,ymmword ptr [rdx+0260h]  ;
  vmovdqa       ymm2,ymmword ptr [rdx+0280h]   ;
  vpmullw       ymm12,ymm7,ymm15               ;
  vpmullw       ymm13,ymm10,ymm15              ;
  vpmullw       ymm14,ymm5,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vperm2i128    ymm6,ymm3,ymm8,020h            ;
  vperm2i128    ymm8,ymm3,ymm8,031h            ;
  vperm2i128    ymm3,ymm4,ymm9,020h            ;
  vperm2i128    ymm9,ymm4,ymm9,031h            ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm4,ymm6,ymm7                 ;
  vpsubw        ymm7,ymm6,ymm7                 ;
  vpaddw        ymm6,ymm8,ymm10                ;
  vpsubw        ymm10,ymm8,ymm10               ;
  vpaddw        ymm8,ymm3,ymm5                 ;
  vpsubw        ymm5,ymm3,ymm5                 ;
  vpaddw        ymm3,ymm9,ymm11                ;
  vpsubw        ymm11,ymm9,ymm11               ;
  vpsubw        ymm4,ymm4,ymm12                ;
  vpaddw        ymm7,ymm7,ymm12                ;
  vpsubw        ymm6,ymm6,ymm13                ;
  vpaddw        ymm10,ymm10,ymm13              ;
  vpsubw        ymm8,ymm8,ymm14                ;
  vpaddw        ymm5,ymm5,ymm14                ;
  vpsubw        ymm3,ymm3,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vpunpcklqdq   ymm9,ymm8,ymm5                 ;
  vpunpckhqdq   ymm5,ymm8,ymm5                 ;
  vpunpcklqdq   ymm8,ymm3,ymm11                ;
  vpunpckhqdq   ymm11,ymm3,ymm11               ;
  vmovdqa       ymm15,ymmword ptr [rdx+02a0h]  ;
  vmovdqa       ymm2,ymmword ptr [rdx+02c0h]   ;
  vpmullw       ymm12,ymm9,ymm15               ;
  vpmullw       ymm13,ymm5,ymm15               ;
  vpmullw       ymm14,ymm8,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vpunpcklqdq   ymm3,ymm4,ymm7                 ;
  vpunpckhqdq   ymm7,ymm4,ymm7                 ;
  vpunpcklqdq   ymm4,ymm6,ymm10                ;
  vpunpckhqdq   ymm10,ymm6,ymm10               ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm6,ymm3,ymm9                 ;
  vpsubw        ymm9,ymm3,ymm9                 ;
  vpaddw        ymm3,ymm7,ymm5                 ;
  vpsubw        ymm5,ymm7,ymm5                 ;
  vpaddw        ymm7,ymm4,ymm8                 ;
  vpsubw        ymm8,ymm4,ymm8                 ;
  vpaddw        ymm4,ymm10,ymm11               ;
  vpsubw        ymm11,ymm10,ymm11              ;
  vpsubw        ymm6,ymm6,ymm12                ;
  vpaddw        ymm9,ymm9,ymm12                ;
  vpsubw        ymm3,ymm3,ymm13                ;
  vpaddw        ymm5,ymm5,ymm13                ;
  vpsubw        ymm7,ymm7,ymm14                ;
  vpaddw        ymm8,ymm8,ymm14                ;
  vpsubw        ymm4,ymm4,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovsldup     ymm10,ymm8                     ;
  vpblendd      ymm10,ymm7,ymm10,0aah          ;
  vpsrlq        ymm7,ymm7,020h                 ;
  vpblendd      ymm8,ymm7,ymm8,0aah            ;
  vmovsldup     ymm7,ymm11                     ;
  vpblendd      ymm7,ymm4,ymm7,0aah            ;
  vpsrlq        ymm4,ymm4,020h                 ;
  vpblendd      ymm11,ymm4,ymm11,0aah          ;
  vmovdqa       ymm15,ymmword ptr [rdx+02e0h]  ;
  vmovdqa       ymm2,ymmword ptr [rdx+0300h]   ;
  vpmullw       ymm12,ymm10,ymm15              ;
  vpmullw       ymm13,ymm8,ymm15               ;
  vpmullw       ymm14,ymm7,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm10,ymm10,ymm2               ;
  vpmulhw       ymm8,ymm8,ymm2                 ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vmovsldup     ymm4,ymm9                      ;
  vpblendd      ymm4,ymm6,ymm4,0aah            ;
  vpsrlq        ymm6,ymm6,020h                 ;
  vpblendd      ymm9,ymm6,ymm9,0aah            ;
  vmovsldup     ymm6,ymm5                      ;
  vpblendd      ymm6,ymm3,ymm6,0aah            ;
  vpsrlq        ymm3,ymm3,020h                 ;
  vpblendd      ymm5,ymm3,ymm5,0aah            ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm3,ymm4,ymm10                ;
  vpsubw        ymm10,ymm4,ymm10               ;
  vpaddw        ymm4,ymm9,ymm8                 ;
  vpsubw        ymm8,ymm9,ymm8                 ;
  vpaddw        ymm9,ymm6,ymm7                 ;
  vpsubw        ymm7,ymm6,ymm7                 ;
  vpaddw        ymm6,ymm5,ymm11                ;
  vpsubw        ymm11,ymm5,ymm11               ;
  vpsubw        ymm3,ymm3,ymm12                ;
  vpaddw        ymm10,ymm10,ymm12              ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm8,ymm8,ymm13                ;
  vpsubw        ymm9,ymm9,ymm14                ;
  vpaddw        ymm7,ymm7,ymm14                ;
  vpsubw        ymm6,ymm6,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vpslld        ymm5,ymm7,010h                 ;
  vpblendw      ymm5,ymm9,ymm5,0aah            ;
  vpsrld        ymm9,ymm9,010h                 ;
  vpblendw      ymm7,ymm9,ymm7,0aah            ;
  vpslld        ymm9,ymm11,010h                ;
  vpblendw      ymm9,ymm6,ymm9,0aah            ;
  vpsrld        ymm6,ymm6,010h                 ;
  vpblendw      ymm11,ymm6,ymm11,0aah          ;
  vmovdqa       ymm15,ymmword ptr [rdx+0320h]  ;
  vmovdqa       ymm2,ymmword ptr [rdx+0340h]   ;
  vpmullw       ymm12,ymm5,ymm15               ;
  vpmullw       ymm13,ymm7,ymm15               ;
  vpmullw       ymm14,ymm9,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm5,ymm5,ymm2                 ;
  vpmulhw       ymm7,ymm7,ymm2                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vpslld        ymm6,ymm10,010h                ;
  vpblendw      ymm6,ymm3,ymm6,0aah            ;
  vpsrld        ymm3,ymm3,010h                 ;
  vpblendw      ymm10,ymm3,ymm10,0aah          ;
  vpslld        ymm3,ymm8,010h                 ;
  vpblendw      ymm3,ymm4,ymm3,0aah            ;
  vpsrld        ymm4,ymm4,010h                 ;
  vpblendw      ymm8,ymm4,ymm8,0aah            ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm4,ymm6,ymm5                 ;
  vpsubw        ymm5,ymm6,ymm5                 ;
  vpaddw        ymm6,ymm10,ymm7                ;
  vpsubw        ymm7,ymm10,ymm7                ;
  vpaddw        ymm10,ymm3,ymm9                ;
  vpsubw        ymm9,ymm3,ymm9                 ;
  vpaddw        ymm3,ymm8,ymm11                ;
  vpsubw        ymm11,ymm8,ymm11               ;
  vpsubw        ymm4,ymm4,ymm12                ;
  vpaddw        ymm5,ymm5,ymm12                ;
  vpsubw        ymm6,ymm6,ymm13                ;
  vpaddw        ymm7,ymm7,ymm13                ;
  vpsubw        ymm10,ymm10,ymm14              ;
  vpaddw        ymm9,ymm9,ymm14                ;
  vpsubw        ymm3,ymm3,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovdqa       ymm14,ymmword ptr [rdx+0360h]  ;
  vmovdqa       ymm15,ymmword ptr [rdx+03a0h]  ;
  vmovdqa       ymm8,ymmword ptr [rdx+0380h]   ;
  vmovdqa       ymm2,ymmword ptr [rdx+03c0h]   ;
  vpmullw       ymm12,ymm10,ymm14              ;
  vpmullw       ymm13,ymm3,ymm14               ;
  vpmullw       ymm14,ymm9,ymm15               ;
  vpmullw       ymm15,ymm11,ymm15              ;
  vpmulhw       ymm10,ymm10,ymm8               ;
  vpmulhw       ymm3,ymm3,ymm8                 ;
  vpmulhw       ymm9,ymm9,ymm2                 ;
  vpmulhw       ymm11,ymm11,ymm2               ;
  vpmulhw       ymm12,ymm12,ymm0               ;
  vpmulhw       ymm13,ymm13,ymm0               ;
  vpmulhw       ymm14,ymm14,ymm0               ;
  vpmulhw       ymm15,ymm15,ymm0               ;
  vpaddw        ymm8,ymm4,ymm10                ;
  vpsubw        ymm10,ymm4,ymm10               ;
  vpaddw        ymm4,ymm6,ymm3                 ;
  vpsubw        ymm3,ymm6,ymm3                 ;
  vpaddw        ymm6,ymm5,ymm9                 ;
  vpsubw        ymm9,ymm5,ymm9                 ;
  vpaddw        ymm5,ymm7,ymm11                ;
  vpsubw        ymm11,ymm7,ymm11               ;
  vpsubw        ymm8,ymm8,ymm12                ;
  vpaddw        ymm10,ymm10,ymm12              ;
  vpsubw        ymm4,ymm4,ymm13                ;
  vpaddw        ymm3,ymm3,ymm13                ;
  vpsubw        ymm6,ymm6,ymm14                ;
  vpaddw        ymm9,ymm9,ymm14                ;
  vpsubw        ymm5,ymm5,ymm15                ;
  vpaddw        ymm11,ymm11,ymm15              ;
  vmovdqa       ymmword ptr [rcx+0100h],ymm8   ;
  vmovdqa       ymmword ptr [rcx+0120h],ymm4   ;
  vmovdqa       ymmword ptr [rcx+0140h],ymm10  ;
  vmovdqa       ymmword ptr [rcx+0160h],ymm3   ;
  vmovdqa       ymmword ptr [rcx+0180h],ymm6   ;
  vmovdqa       ymmword ptr [rcx+01a0h],ymm5   ;
  vmovdqa       ymmword ptr [rcx+01c0h],ymm9   ;
  vmovdqa       ymmword ptr [rcx+01e0h],ymm11  ;

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
