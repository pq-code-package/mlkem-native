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
; Name: nttunpack_avx2_asm
; Description: x86_64 AVX2 NTT unpack from custom to bitreversed order
; Signature: void mlk_nttunpack_avx2_asm(int16_t *r)
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
FUNC_NAME EQU mlkem_nttunpack_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,068h                      ; 068h and not 060h for alignment purposes
  .allocstack   068h

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
  vmovdqa       xmmword ptr [rsp+050h],xmm11  ; save xmm11 on stack
  .savexmm128    xmm11,050h
  .endprolog

  vmovdqa      ymm4,ymmword ptr [rcx]         ;
  vmovdqa      ymm5,ymmword ptr [rcx+020h]    ;
  vmovdqa      ymm6,ymmword ptr [rcx+040h]    ;
  vmovdqa      ymm7,ymmword ptr [rcx+060h]    ;
  vmovdqa      ymm8,ymmword ptr [rcx+080h]    ;
  vmovdqa      ymm9,ymmword ptr [rcx+0a0h]    ;
  vmovdqa      ymm10,ymmword ptr [rcx+0c0h]   ;
  vmovdqa      ymm11,ymmword ptr [rcx+0e0h]   ;
  vperm2i128   ymm3,ymm4,ymm8,020h            ;
  vperm2i128   ymm8,ymm4,ymm8,031h            ;
  vperm2i128   ymm4,ymm5,ymm9,020h            ;
  vperm2i128   ymm9,ymm5,ymm9,031h            ;
  vperm2i128   ymm5,ymm6,ymm10,020h           ;
  vperm2i128   ymm10,ymm6,ymm10,031h          ;
  vperm2i128   ymm6,ymm7,ymm11,020h           ;
  vperm2i128   ymm11,ymm7,ymm11,031h          ;
  vpunpcklqdq  ymm7,ymm3,ymm5                 ;
  vpunpckhqdq  ymm5,ymm3,ymm5                 ;
  vpunpcklqdq  ymm3,ymm8,ymm10                ;
  vpunpckhqdq  ymm10,ymm8,ymm10               ;
  vpunpcklqdq  ymm8,ymm4,ymm6                 ;
  vpunpckhqdq  ymm6,ymm4,ymm6                 ;
  vpunpcklqdq  ymm4,ymm9,ymm11                ;
  vpunpckhqdq  ymm11,ymm9,ymm11               ;
  vmovsldup    ymm9,ymm8                      ;
  vpblendd     ymm9,ymm7,ymm9,0aah            ;
  vpsrlq       ymm7,ymm7,020h                 ;
  vpblendd     ymm8,ymm7,ymm8,0aah            ;
  vmovsldup    ymm7,ymm6                      ;
  vpblendd     ymm7,ymm5,ymm7,0aah            ;
  vpsrlq       ymm5,ymm5,020h                 ;
  vpblendd     ymm6,ymm5,ymm6,0aah            ;
  vmovsldup    ymm5,ymm4                      ;
  vpblendd     ymm5,ymm3,ymm5,0aah            ;
  vpsrlq       ymm3,ymm3,020h                 ;
  vpblendd     ymm4,ymm3,ymm4,0aah            ;
  vmovsldup    ymm3,ymm11                     ;
  vpblendd     ymm3,ymm10,ymm3,0aah           ;
  vpsrlq       ymm10,ymm10,020h               ;
  vpblendd     ymm11,ymm10,ymm11,0aah         ;
  vpslld       ymm10,ymm5,010h                ;
  vpblendw     ymm10,ymm9,ymm10,0aah          ;
  vpsrld       ymm9,ymm9,010h                 ;
  vpblendw     ymm5,ymm9,ymm5,0aah            ;
  vpslld       ymm9,ymm4,010h                 ;
  vpblendw     ymm9,ymm8,ymm9,0aah            ;
  vpsrld       ymm8,ymm8,010h                 ;
  vpblendw     ymm4,ymm8,ymm4,0aah            ;
  vpslld       ymm8,ymm3,010h                 ;
  vpblendw     ymm8,ymm7,ymm8,0aah            ;
  vpsrld       ymm7,ymm7,010h                 ;
  vpblendw     ymm3,ymm7,ymm3,0aah            ;
  vpslld       ymm7,ymm11,010h                ;
  vpblendw     ymm7,ymm6,ymm7,0aah            ;
  vpsrld       ymm6,ymm6,010h                 ;
  vpblendw     ymm11,ymm6,ymm11,0aah          ;
  vmovdqa      ymmword ptr [rcx],ymm10        ;
  vmovdqa      ymmword ptr [rcx+020h],ymm5    ;
  vmovdqa      ymmword ptr [rcx+040h],ymm9    ;
  vmovdqa      ymmword ptr [rcx+060h],ymm4    ;
  vmovdqa      ymmword ptr [rcx+080h],ymm8    ;
  vmovdqa      ymmword ptr [rcx+0a0h],ymm3    ;
  vmovdqa      ymmword ptr [rcx+0c0h],ymm7    ;
  vmovdqa      ymmword ptr [rcx+0e0h],ymm11   ;
  vmovdqa      ymm4,ymmword ptr [rcx+0100h]   ;
  vmovdqa      ymm5,ymmword ptr [rcx+0120h]   ;
  vmovdqa      ymm6,ymmword ptr [rcx+0140h]   ;
  vmovdqa      ymm7,ymmword ptr [rcx+0160h]   ;
  vmovdqa      ymm8,ymmword ptr [rcx+0180h]   ;
  vmovdqa      ymm9,ymmword ptr [rcx+01a0h]   ;
  vmovdqa      ymm10,ymmword ptr [rcx+01c0h]  ;
  vmovdqa      ymm11,ymmword ptr [rcx+01e0h]  ;
  vperm2i128   ymm3,ymm4,ymm8,020h            ;
  vperm2i128   ymm8,ymm4,ymm8,031h            ;
  vperm2i128   ymm4,ymm5,ymm9,020h            ;
  vperm2i128   ymm9,ymm5,ymm9,031h            ;
  vperm2i128   ymm5,ymm6,ymm10,020h           ;
  vperm2i128   ymm10,ymm6,ymm10,031h          ;
  vperm2i128   ymm6,ymm7,ymm11,020h           ;
  vperm2i128   ymm11,ymm7,ymm11,031h          ;
  vpunpcklqdq  ymm7,ymm3,ymm5                 ;
  vpunpckhqdq  ymm5,ymm3,ymm5                 ;
  vpunpcklqdq  ymm3,ymm8,ymm10                ;
  vpunpckhqdq  ymm10,ymm8,ymm10               ;
  vpunpcklqdq  ymm8,ymm4,ymm6                 ;
  vpunpckhqdq  ymm6,ymm4,ymm6                 ;
  vpunpcklqdq  ymm4,ymm9,ymm11                ;
  vpunpckhqdq  ymm11,ymm9,ymm11               ;
  vmovsldup    ymm9,ymm8                      ;
  vpblendd     ymm9,ymm7,ymm9,0aah            ;
  vpsrlq       ymm7,ymm7,020h                 ;
  vpblendd     ymm8,ymm7,ymm8,0aah            ;
  vmovsldup    ymm7,ymm6                      ;
  vpblendd     ymm7,ymm5,ymm7,0aah            ;
  vpsrlq       ymm5,ymm5,020h                 ;
  vpblendd     ymm6,ymm5,ymm6,0aah            ;
  vmovsldup    ymm5,ymm4                      ;
  vpblendd     ymm5,ymm3,ymm5,0aah            ;
  vpsrlq       ymm3,ymm3,020h                 ;
  vpblendd     ymm4,ymm3,ymm4,0aah            ;
  vmovsldup    ymm3,ymm11                     ;
  vpblendd     ymm3,ymm10,ymm3,0aah           ;
  vpsrlq       ymm10,ymm10,020h               ;
  vpblendd     ymm11,ymm10,ymm11,0aah         ;
  vpslld       ymm10,ymm5,010h                ;
  vpblendw     ymm10,ymm9,ymm10,0aah          ;
  vpsrld       ymm9,ymm9,010h                 ;
  vpblendw     ymm5,ymm9,ymm5,0aah            ;
  vpslld       ymm9,ymm4,010h                 ;
  vpblendw     ymm9,ymm8,ymm9,0aah            ;
  vpsrld       ymm8,ymm8,010h                 ;
  vpblendw     ymm4,ymm8,ymm4,0aah            ;
  vpslld       ymm8,ymm3,010h                 ;
  vpblendw     ymm8,ymm7,ymm8,0aah            ;
  vpsrld       ymm7,ymm7,010h                 ;
  vpblendw     ymm3,ymm7,ymm3,0aah            ;
  vpslld       ymm7,ymm11,010h                ;
  vpblendw     ymm7,ymm6,ymm7,0aah            ;
  vpsrld       ymm6,ymm6,010h                 ;
  vpblendw     ymm11,ymm6,ymm11,0aah          ;
  vmovdqa      ymmword ptr [rcx+0100h],ymm10  ;
  vmovdqa      ymmword ptr [rcx+0120h],ymm5   ;
  vmovdqa      ymmword ptr [rcx+0140h],ymm9   ;
  vmovdqa      ymmword ptr [rcx+0160h],ymm4   ;
  vmovdqa      ymmword ptr [rcx+0180h],ymm8   ;
  vmovdqa      ymmword ptr [rcx+01a0h],ymm3   ;
  vmovdqa      ymmword ptr [rcx+01c0h],ymm7   ;
  vmovdqa      ymmword ptr [rcx+01e0h],ymm11  ;

  vzeroupper                                  ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]   ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]   ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]   ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]   ; restore xmm9 from stack
  vmovdqa       xmm10,xmmword ptr [rsp+040h]  ; restore xmm10 from stack
  vmovdqa       xmm11,xmmword ptr [rsp+050h]  ; restore xmm11 from stack

  add           rsp,068h                      ; 068h and not 060h for alignment purposes

  ret                                         ;

FUNC_NAME ENDP

  END
