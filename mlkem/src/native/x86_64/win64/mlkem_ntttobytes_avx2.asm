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
; Name: ntttobytes_avx2_asm
; Description: x86_64 AVX2 polynomial serialization in NTT domain
; Signature: void mlk_ntttobytes_avx2_asm(uint8_t *r, const int16_t *a)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 384
;     permissions: write-only
;     c_parameter: uint8_t *r
;     description: Output byte array (MLKEM_POLYBYTES = 384)
;   rdx:
;     type: buffer
;     size_bytes: 512
;     permissions: read-only
;     c_parameter: const int16_t *a
;     description: Input polynomial (256 x int16_t)
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_ntttobytes_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,078h                       ; 078h and not 070h for alignment purposes
  .allocstack   078h

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
  .endprolog

  mov           eax,0d010d01h                  ;
  vmovd         xmm0,eax                       ;
  vpbroadcastd  ymm0,xmm0                      ;
  vmovdqa       ymm5,ymmword ptr [rdx]         ;
  vmovdqa       ymm6,ymmword ptr [rdx+020h]    ;
  vmovdqa       ymm7,ymmword ptr [rdx+040h]    ;
  vmovdqa       ymm8,ymmword ptr [rdx+060h]    ;
  vmovdqa       ymm9,ymmword ptr [rdx+080h]    ;
  vmovdqa       ymm10,ymmword ptr [rdx+0a0h]   ;
  vmovdqa       ymm11,ymmword ptr [rdx+0c0h]   ;
  vmovdqa       ymm12,ymmword ptr [rdx+0e0h]   ;
  vpsllw        ymm4,ymm6,0ch                  ;
  vpor          ymm4,ymm5,ymm4                 ;
  vpsrlw        ymm5,ymm6,04h                  ;
  vpsllw        ymm6,ymm7,08h                  ;
  vpor          ymm5,ymm6,ymm5                 ;
  vpsrlw        ymm6,ymm7,08h                  ;
  vpsllw        ymm7,ymm8,04h                  ;
  vpor          ymm6,ymm7,ymm6                 ;
  vpsllw        ymm7,ymm10,0ch                 ;
  vpor          ymm7,ymm9,ymm7                 ;
  vpsrlw        ymm8,ymm10,04h                 ;
  vpsllw        ymm9,ymm11,08h                 ;
  vpor          ymm8,ymm9,ymm8                 ;
  vpsrlw        ymm9,ymm11,08h                 ;
  vpsllw        ymm10,ymm12,04h                ;
  vpor          ymm9,ymm10,ymm9                ;
  vpslld        ymm3,ymm5,010h                 ;
  vpblendw      ymm3,ymm4,ymm3,0aah            ;
  vpsrld        ymm4,ymm4,010h                 ;
  vpblendw      ymm5,ymm4,ymm5,0aah            ;
  vpslld        ymm4,ymm7,010h                 ;
  vpblendw      ymm4,ymm6,ymm4,0aah            ;
  vpsrld        ymm6,ymm6,010h                 ;
  vpblendw      ymm7,ymm6,ymm7,0aah            ;
  vpslld        ymm6,ymm9,010h                 ;
  vpblendw      ymm6,ymm8,ymm6,0aah            ;
  vpsrld        ymm8,ymm8,010h                 ;
  vpblendw      ymm9,ymm8,ymm9,0aah            ;
  vmovsldup     ymm8,ymm4                      ;
  vpblendd      ymm8,ymm3,ymm8,0aah            ;
  vpsrlq        ymm3,ymm3,020h                 ;
  vpblendd      ymm4,ymm3,ymm4,0aah            ;
  vmovsldup     ymm3,ymm5                      ;
  vpblendd      ymm3,ymm6,ymm3,0aah            ;
  vpsrlq        ymm6,ymm6,020h                 ;
  vpblendd      ymm5,ymm6,ymm5,0aah            ;
  vmovsldup     ymm6,ymm9                      ;
  vpblendd      ymm6,ymm7,ymm6,0aah            ;
  vpsrlq        ymm7,ymm7,020h                 ;
  vpblendd      ymm9,ymm7,ymm9,0aah            ;
  vpunpcklqdq   ymm7,ymm8,ymm3                 ;
  vpunpckhqdq   ymm3,ymm8,ymm3                 ;
  vpunpcklqdq   ymm8,ymm6,ymm4                 ;
  vpunpckhqdq   ymm4,ymm6,ymm4                 ;
  vpunpcklqdq   ymm6,ymm5,ymm9                 ;
  vpunpckhqdq   ymm9,ymm5,ymm9                 ;
  vperm2i128    ymm5,ymm7,ymm8,020h            ;
  vperm2i128    ymm8,ymm7,ymm8,031h            ;
  vperm2i128    ymm7,ymm6,ymm3,020h            ;
  vperm2i128    ymm3,ymm6,ymm3,031h            ;
  vperm2i128    ymm6,ymm4,ymm9,020h            ;
  vperm2i128    ymm9,ymm4,ymm9,031h            ;
  vmovdqu       ymmword ptr [rcx],ymm5         ;
  vmovdqu       ymmword ptr [rcx+020h],ymm7    ;
  vmovdqu       ymmword ptr [rcx+040h],ymm6    ;
  vmovdqu       ymmword ptr [rcx+060h],ymm8    ;
  vmovdqu       ymmword ptr [rcx+080h],ymm3    ;
  vmovdqu       ymmword ptr [rcx+0a0h],ymm9    ;
  vmovdqa       ymm5,ymmword ptr [rdx+0100h]   ;
  vmovdqa       ymm6,ymmword ptr [rdx+0120h]   ;
  vmovdqa       ymm7,ymmword ptr [rdx+0140h]   ;
  vmovdqa       ymm8,ymmword ptr [rdx+0160h]   ;
  vmovdqa       ymm9,ymmword ptr [rdx+0180h]   ;
  vmovdqa       ymm10,ymmword ptr [rdx+01a0h]  ;
  vmovdqa       ymm11,ymmword ptr [rdx+01c0h]  ;
  vmovdqa       ymm12,ymmword ptr [rdx+01e0h]  ;
  vpsllw        ymm4,ymm6,0ch                  ;
  vpor          ymm4,ymm5,ymm4                 ;
  vpsrlw        ymm5,ymm6,04h                  ;
  vpsllw        ymm6,ymm7,08h                  ;
  vpor          ymm5,ymm6,ymm5                 ;
  vpsrlw        ymm6,ymm7,08h                  ;
  vpsllw        ymm7,ymm8,04h                  ;
  vpor          ymm6,ymm7,ymm6                 ;
  vpsllw        ymm7,ymm10,0ch                 ;
  vpor          ymm7,ymm9,ymm7                 ;
  vpsrlw        ymm8,ymm10,04h                 ;
  vpsllw        ymm9,ymm11,08h                 ;
  vpor          ymm8,ymm9,ymm8                 ;
  vpsrlw        ymm9,ymm11,08h                 ;
  vpsllw        ymm10,ymm12,04h                ;
  vpor          ymm9,ymm10,ymm9                ;
  vpslld        ymm3,ymm5,010h                 ;
  vpblendw      ymm3,ymm4,ymm3,0aah            ;
  vpsrld        ymm4,ymm4,010h                 ;
  vpblendw      ymm5,ymm4,ymm5,0aah            ;
  vpslld        ymm4,ymm7,010h                 ;
  vpblendw      ymm4,ymm6,ymm4,0aah            ;
  vpsrld        ymm6,ymm6,010h                 ;
  vpblendw      ymm7,ymm6,ymm7,0aah            ;
  vpslld        ymm6,ymm9,010h                 ;
  vpblendw      ymm6,ymm8,ymm6,0aah            ;
  vpsrld        ymm8,ymm8,010h                 ;
  vpblendw      ymm9,ymm8,ymm9,0aah            ;
  vmovsldup     ymm8,ymm4                      ;
  vpblendd      ymm8,ymm3,ymm8,0aah            ;
  vpsrlq        ymm3,ymm3,020h                 ;
  vpblendd      ymm4,ymm3,ymm4,0aah            ;
  vmovsldup     ymm3,ymm5                      ;
  vpblendd      ymm3,ymm6,ymm3,0aah            ;
  vpsrlq        ymm6,ymm6,020h                 ;
  vpblendd      ymm5,ymm6,ymm5,0aah            ;
  vmovsldup     ymm6,ymm9                      ;
  vpblendd      ymm6,ymm7,ymm6,0aah            ;
  vpsrlq        ymm7,ymm7,020h                 ;
  vpblendd      ymm9,ymm7,ymm9,0aah            ;
  vpunpcklqdq   ymm7,ymm8,ymm3                 ;
  vpunpckhqdq   ymm3,ymm8,ymm3                 ;
  vpunpcklqdq   ymm8,ymm6,ymm4                 ;
  vpunpckhqdq   ymm4,ymm6,ymm4                 ;
  vpunpcklqdq   ymm6,ymm5,ymm9                 ;
  vpunpckhqdq   ymm9,ymm5,ymm9                 ;
  vperm2i128    ymm5,ymm7,ymm8,020h            ;
  vperm2i128    ymm8,ymm7,ymm8,031h            ;
  vperm2i128    ymm7,ymm6,ymm3,020h            ;
  vperm2i128    ymm3,ymm6,ymm3,031h            ;
  vperm2i128    ymm6,ymm4,ymm9,020h            ;
  vperm2i128    ymm9,ymm4,ymm9,031h            ;
  vmovdqu       ymmword ptr [rcx+0c0h],ymm5    ;
  vmovdqu       ymmword ptr [rcx+0e0h],ymm7    ;
  vmovdqu       ymmword ptr [rcx+0100h],ymm6   ;
  vmovdqu       ymmword ptr [rcx+0120h],ymm8   ;
  vmovdqu       ymmword ptr [rcx+0140h],ymm3   ;
  vmovdqu       ymmword ptr [rcx+0160h],ymm9   ;

  vzeroupper                                   ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]    ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]    ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]    ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]    ; restore xmm9 from stack
  vmovdqa       xmm10,xmmword ptr [rsp+040h]   ; restore xmm10 from stack
  vmovdqa       xmm11,xmmword ptr [rsp+050h]   ; restore xmm11 from stack
  vmovdqa       xmm12,xmmword ptr [rsp+060h]   ; restore xmm12 from stack

  add           rsp,078h                       ; 078h and not 070h for alignment purposes

  ret                                          ;

FUNC_NAME ENDP

  END
