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
; Name: nttfrombytes_avx2_asm
; Description: x86_64 AVX2 polynomial deserialization in NTT domain
; Signature: void mlk_nttfrombytes_avx2_asm(int16_t *r, const uint8_t *a)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 512
;     permissions: write-only
;     c_parameter: int16_t *r
;     description: Output polynomial (256 x int16_t)
;   rdx:
;     type: buffer
;     size_bytes: 384
;     permissions: read-only
;     c_parameter: const uint8_t *a
;     description: Input byte array (MLKEM_POLYBYTES = 384)
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_nttfrombytes_avx2_asm
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

  mov           eax,0fff0fffh                  ;
  vmovd         xmm0,eax                       ;
  vpbroadcastd  ymm0,xmm0                      ;
  vmovdqu       ymm4,ymmword ptr [rdx]         ;
  vmovdqu       ymm5,ymmword ptr [rdx+020h]    ;
  vmovdqu       ymm6,ymmword ptr [rdx+040h]    ;
  vmovdqu       ymm7,ymmword ptr [rdx+060h]    ;
  vmovdqu       ymm8,ymmword ptr [rdx+080h]    ;
  vmovdqu       ymm9,ymmword ptr [rdx+0a0h]    ;
  vperm2i128    ymm3,ymm4,ymm7,020h            ;
  vperm2i128    ymm7,ymm4,ymm7,031h            ;
  vperm2i128    ymm4,ymm5,ymm8,020h            ;
  vperm2i128    ymm8,ymm5,ymm8,031h            ;
  vperm2i128    ymm5,ymm6,ymm9,020h            ;
  vperm2i128    ymm9,ymm6,ymm9,031h            ;
  vpunpcklqdq   ymm6,ymm3,ymm8                 ;
  vpunpckhqdq   ymm8,ymm3,ymm8                 ;
  vpunpcklqdq   ymm3,ymm7,ymm5                 ;
  vpunpckhqdq   ymm5,ymm7,ymm5                 ;
  vpunpcklqdq   ymm7,ymm4,ymm9                 ;
  vpunpckhqdq   ymm9,ymm4,ymm9                 ;
  vmovsldup     ymm4,ymm5                      ;
  vpblendd      ymm4,ymm6,ymm4,0aah            ;
  vpsrlq        ymm6,ymm6,020h                 ;
  vpblendd      ymm5,ymm6,ymm5,0aah            ;
  vmovsldup     ymm6,ymm7                      ;
  vpblendd      ymm6,ymm8,ymm6,0aah            ;
  vpsrlq        ymm8,ymm8,020h                 ;
  vpblendd      ymm7,ymm8,ymm7,0aah            ;
  vmovsldup     ymm8,ymm9                      ;
  vpblendd      ymm8,ymm3,ymm8,0aah            ;
  vpsrlq        ymm3,ymm3,020h                 ;
  vpblendd      ymm9,ymm3,ymm9,0aah            ;
  vpslld        ymm10,ymm7,010h                ;
  vpblendw      ymm10,ymm4,ymm10,0aah          ;
  vpsrld        ymm4,ymm4,010h                 ;
  vpblendw      ymm7,ymm4,ymm7,0aah            ;
  vpslld        ymm4,ymm8,010h                 ;
  vpblendw      ymm4,ymm5,ymm4,0aah            ;
  vpsrld        ymm5,ymm5,010h                 ;
  vpblendw      ymm8,ymm5,ymm8,0aah            ;
  vpslld        ymm5,ymm9,010h                 ;
  vpblendw      ymm5,ymm6,ymm5,0aah            ;
  vpsrld        ymm6,ymm6,010h                 ;
  vpblendw      ymm9,ymm6,ymm9,0aah            ;
  vpsrlw        ymm11,ymm10,0ch                ;
  vpsllw        ymm12,ymm7,04h                 ;
  vpor          ymm11,ymm12,ymm11              ;
  vpand         ymm10,ymm10,ymm0               ;
  vpand         ymm11,ymm11,ymm0               ;
  vpsrlw        ymm12,ymm7,08h                 ;
  vpsllw        ymm13,ymm4,08h                 ;
  vpor          ymm12,ymm13,ymm12              ;
  vpand         ymm12,ymm12,ymm0               ;
  vpsrlw        ymm13,ymm4,04h                 ;
  vpand         ymm13,ymm13,ymm0               ;
  vpsrlw        ymm14,ymm8,0ch                 ;
  vpsllw        ymm15,ymm5,04h                 ;
  vpor          ymm14,ymm15,ymm14              ;
  vpand         ymm8,ymm8,ymm0                 ;
  vpand         ymm14,ymm14,ymm0               ;
  vpsrlw        ymm15,ymm5,08h                 ;
  vpsllw        ymm1,ymm9,08h                  ;
  vpor          ymm15,ymm1,ymm15               ;
  vpand         ymm15,ymm15,ymm0               ;
  vpsrlw        ymm1,ymm9,04h                  ;
  vpand         ymm1,ymm1,ymm0                 ;
  vmovdqa       ymmword ptr [rcx],ymm10        ;
  vmovdqa       ymmword ptr [rcx+020h],ymm11   ;
  vmovdqa       ymmword ptr [rcx+040h],ymm12   ;
  vmovdqa       ymmword ptr [rcx+060h],ymm13   ;
  vmovdqa       ymmword ptr [rcx+080h],ymm8    ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm14   ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm15   ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm1    ;
  vmovdqu       ymm4,ymmword ptr [rdx+0c0h]    ;
  vmovdqu       ymm5,ymmword ptr [rdx+0e0h]    ;
  vmovdqu       ymm6,ymmword ptr [rdx+0100h]   ;
  vmovdqu       ymm7,ymmword ptr [rdx+0120h]   ;
  vmovdqu       ymm8,ymmword ptr [rdx+0140h]   ;
  vmovdqu       ymm9,ymmword ptr [rdx+0160h]   ;
  vperm2i128    ymm3,ymm4,ymm7,020h            ;
  vperm2i128    ymm7,ymm4,ymm7,031h            ;
  vperm2i128    ymm4,ymm5,ymm8,020h            ;
  vperm2i128    ymm8,ymm5,ymm8,031h            ;
  vperm2i128    ymm5,ymm6,ymm9,020h            ;
  vperm2i128    ymm9,ymm6,ymm9,031h            ;
  vpunpcklqdq   ymm6,ymm3,ymm8                 ;
  vpunpckhqdq   ymm8,ymm3,ymm8                 ;
  vpunpcklqdq   ymm3,ymm7,ymm5                 ;
  vpunpckhqdq   ymm5,ymm7,ymm5                 ;
  vpunpcklqdq   ymm7,ymm4,ymm9                 ;
  vpunpckhqdq   ymm9,ymm4,ymm9                 ;
  vmovsldup     ymm4,ymm5                      ;
  vpblendd      ymm4,ymm6,ymm4,0aah            ;
  vpsrlq        ymm6,ymm6,020h                 ;
  vpblendd      ymm5,ymm6,ymm5,0aah            ;
  vmovsldup     ymm6,ymm7                      ;
  vpblendd      ymm6,ymm8,ymm6,0aah            ;
  vpsrlq        ymm8,ymm8,020h                 ;
  vpblendd      ymm7,ymm8,ymm7,0aah            ;
  vmovsldup     ymm8,ymm9                      ;
  vpblendd      ymm8,ymm3,ymm8,0aah            ;
  vpsrlq        ymm3,ymm3,020h                 ;
  vpblendd      ymm9,ymm3,ymm9,0aah            ;
  vpslld        ymm10,ymm7,010h                ;
  vpblendw      ymm10,ymm4,ymm10,0aah          ;
  vpsrld        ymm4,ymm4,010h                 ;
  vpblendw      ymm7,ymm4,ymm7,0aah            ;
  vpslld        ymm4,ymm8,010h                 ;
  vpblendw      ymm4,ymm5,ymm4,0aah            ;
  vpsrld        ymm5,ymm5,010h                 ;
  vpblendw      ymm8,ymm5,ymm8,0aah            ;
  vpslld        ymm5,ymm9,010h                 ;
  vpblendw      ymm5,ymm6,ymm5,0aah            ;
  vpsrld        ymm6,ymm6,010h                 ;
  vpblendw      ymm9,ymm6,ymm9,0aah            ;
  vpsrlw        ymm11,ymm10,0ch                ;
  vpsllw        ymm12,ymm7,04h                 ;
  vpor          ymm11,ymm12,ymm11              ;
  vpand         ymm10,ymm10,ymm0               ;
  vpand         ymm11,ymm11,ymm0               ;
  vpsrlw        ymm12,ymm7,08h                 ;
  vpsllw        ymm13,ymm4,08h                 ;
  vpor          ymm12,ymm13,ymm12              ;
  vpand         ymm12,ymm12,ymm0               ;
  vpsrlw        ymm13,ymm4,04h                 ;
  vpand         ymm13,ymm13,ymm0               ;
  vpsrlw        ymm14,ymm8,0ch                 ;
  vpsllw        ymm15,ymm5,04h                 ;
  vpor          ymm14,ymm15,ymm14              ;
  vpand         ymm8,ymm8,ymm0                 ;
  vpand         ymm14,ymm14,ymm0               ;
  vpsrlw        ymm15,ymm5,08h                 ;
  vpsllw        ymm1,ymm9,08h                  ;
  vpor          ymm15,ymm1,ymm15               ;
  vpand         ymm15,ymm15,ymm0               ;
  vpsrlw        ymm1,ymm9,04h                  ;
  vpand         ymm1,ymm1,ymm0                 ;
  vmovdqa       ymmword ptr [rcx+0100h],ymm10  ;
  vmovdqa       ymmword ptr [rcx+0120h],ymm11  ;
  vmovdqa       ymmword ptr [rcx+0140h],ymm12  ;
  vmovdqa       ymmword ptr [rcx+0160h],ymm13  ;
  vmovdqa       ymmword ptr [rcx+0180h],ymm8   ;
  vmovdqa       ymmword ptr [rcx+01a0h],ymm14  ;
  vmovdqa       ymmword ptr [rcx+01c0h],ymm15  ;
  vmovdqa       ymmword ptr [rcx+01e0h],ymm1   ;

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
