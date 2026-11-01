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
; Name: reduce_avx2_asm
; Description: x86_64 AVX2 modular reduction
; Signature: void mlk_reduce_avx2_asm(int16_t *r)
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
FUNC_NAME EQU mlkem_reduce_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,058h                      ; 058h and not 050h for alignment purposes
  .allocstack   058h

  vmovdqa       xmmword ptr [rsp+000h],xmm6   ; save xmm6 on stack
  .savexmm128   xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7   ; save xmm7 on stack
  .savexmm128   xmm7,010h
  vmovdqa       xmmword ptr [rsp+020h],xmm8   ; save xmm8 on stack
  .savexmm128   xmm8,020h
  vmovdqa       xmmword ptr [rsp+030h],xmm9   ; save xmm9 on stack
  .savexmm128   xmm9,030h
  vmovdqa       xmmword ptr [rsp+040h],xmm12  ; save xmm12 on stack
  .savexmm128   xmm12,040h
  .endprolog

  mov           eax,0d010d01h                 ;
  vmovd         xmm0,eax                      ;
  vpbroadcastd  ymm0,xmm0                     ;
  mov           eax,04ebf4ebfh                ;
  vmovd         xmm1,eax                      ;
  vpbroadcastd  ymm1,xmm1                     ;
  vmovdqa       ymm2,ymmword ptr [rcx]        ;
  vmovdqa       ymm3,ymmword ptr [rcx+020h]   ;
  vmovdqa       ymm4,ymmword ptr [rcx+040h]   ;
  vmovdqa       ymm5,ymmword ptr [rcx+060h]   ;
  vmovdqa       ymm6,ymmword ptr [rcx+080h]   ;
  vmovdqa       ymm7,ymmword ptr [rcx+0a0h]   ;
  vmovdqa       ymm8,ymmword ptr [rcx+0c0h]   ;
  vmovdqa       ymm9,ymmword ptr [rcx+0e0h]   ;
  vpmulhw       ymm12,ymm2,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm2,ymm2,ymm12               ;
  vpmulhw       ymm12,ymm3,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm3,ymm3,ymm12               ;
  vpmulhw       ymm12,ymm4,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm4,ymm4,ymm12               ;
  vpmulhw       ymm12,ymm5,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm5,ymm5,ymm12               ;
  vpmulhw       ymm12,ymm6,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm6,ymm6,ymm12               ;
  vpmulhw       ymm12,ymm7,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm7,ymm7,ymm12               ;
  vpmulhw       ymm12,ymm8,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm8,ymm8,ymm12               ;
  vpmulhw       ymm12,ymm9,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm9,ymm9,ymm12               ;
  vpsubw        ymm2,ymm2,ymm0                ;
  vpsraw        ymm12,ymm2,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm2,ymm2,ymm12               ;
  vpsubw        ymm3,ymm3,ymm0                ;
  vpsraw        ymm12,ymm3,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm3,ymm3,ymm12               ;
  vpsubw        ymm4,ymm4,ymm0                ;
  vpsraw        ymm12,ymm4,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm4,ymm4,ymm12               ;
  vpsubw        ymm5,ymm5,ymm0                ;
  vpsraw        ymm12,ymm5,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm5,ymm5,ymm12               ;
  vpsubw        ymm6,ymm6,ymm0                ;
  vpsraw        ymm12,ymm6,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm6,ymm6,ymm12               ;
  vpsubw        ymm7,ymm7,ymm0                ;
  vpsraw        ymm12,ymm7,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm7,ymm7,ymm12               ;
  vpsubw        ymm8,ymm8,ymm0                ;
  vpsraw        ymm12,ymm8,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm8,ymm8,ymm12               ;
  vpsubw        ymm9,ymm9,ymm0                ;
  vpsraw        ymm12,ymm9,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm9,ymm9,ymm12               ;
  vmovdqa       ymmword ptr [rcx],ymm2        ;
  vmovdqa       ymmword ptr [rcx+020h],ymm3   ;
  vmovdqa       ymmword ptr [rcx+040h],ymm4   ;
  vmovdqa       ymmword ptr [rcx+060h],ymm5   ;
  vmovdqa       ymmword ptr [rcx+080h],ymm6   ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm7   ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm8   ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm9   ;
  vmovdqa       ymm2,ymmword ptr [rcx+0100h]  ;
  vmovdqa       ymm3,ymmword ptr [rcx+0120h]  ;
  vmovdqa       ymm4,ymmword ptr [rcx+0140h]  ;
  vmovdqa       ymm5,ymmword ptr [rcx+0160h]  ;
  vmovdqa       ymm6,ymmword ptr [rcx+0180h]  ;
  vmovdqa       ymm7,ymmword ptr [rcx+01a0h]  ;
  vmovdqa       ymm8,ymmword ptr [rcx+01c0h]  ;
  vmovdqa       ymm9,ymmword ptr [rcx+01e0h]  ;
  vpmulhw       ymm12,ymm2,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm2,ymm2,ymm12               ;
  vpmulhw       ymm12,ymm3,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm3,ymm3,ymm12               ;
  vpmulhw       ymm12,ymm4,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm4,ymm4,ymm12               ;
  vpmulhw       ymm12,ymm5,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm5,ymm5,ymm12               ;
  vpmulhw       ymm12,ymm6,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm6,ymm6,ymm12               ;
  vpmulhw       ymm12,ymm7,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm7,ymm7,ymm12               ;
  vpmulhw       ymm12,ymm8,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm8,ymm8,ymm12               ;
  vpmulhw       ymm12,ymm9,ymm1               ;
  vpsraw        ymm12,ymm12,0ah               ;
  vpmullw       ymm12,ymm12,ymm0              ;
  vpsubw        ymm9,ymm9,ymm12               ;
  vpsubw        ymm2,ymm2,ymm0                ;
  vpsraw        ymm12,ymm2,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm2,ymm2,ymm12               ;
  vpsubw        ymm3,ymm3,ymm0                ;
  vpsraw        ymm12,ymm3,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm3,ymm3,ymm12               ;
  vpsubw        ymm4,ymm4,ymm0                ;
  vpsraw        ymm12,ymm4,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm4,ymm4,ymm12               ;
  vpsubw        ymm5,ymm5,ymm0                ;
  vpsraw        ymm12,ymm5,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm5,ymm5,ymm12               ;
  vpsubw        ymm6,ymm6,ymm0                ;
  vpsraw        ymm12,ymm6,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm6,ymm6,ymm12               ;
  vpsubw        ymm7,ymm7,ymm0                ;
  vpsraw        ymm12,ymm7,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm7,ymm7,ymm12               ;
  vpsubw        ymm8,ymm8,ymm0                ;
  vpsraw        ymm12,ymm8,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm8,ymm8,ymm12               ;
  vpsubw        ymm9,ymm9,ymm0                ;
  vpsraw        ymm12,ymm9,0fh                ;
  vpand         ymm12,ymm12,ymm0              ;
  vpaddw        ymm9,ymm9,ymm12               ;
  vmovdqa       ymmword ptr [rcx+0100h],ymm2  ;
  vmovdqa       ymmword ptr [rcx+0120h],ymm3  ;
  vmovdqa       ymmword ptr [rcx+0140h],ymm4  ;
  vmovdqa       ymmword ptr [rcx+0160h],ymm5  ;
  vmovdqa       ymmword ptr [rcx+0180h],ymm6  ;
  vmovdqa       ymmword ptr [rcx+01a0h],ymm7  ;
  vmovdqa       ymmword ptr [rcx+01c0h],ymm8  ;
  vmovdqa       ymmword ptr [rcx+01e0h],ymm9  ;

  vzeroupper                                  ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]   ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]   ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]   ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]   ; restore xmm9 from stack
  vmovdqa       xmm12,xmmword ptr [rsp+040h]  ; restore xmm12 from stack

  add           rsp,058h                      ; 058h and not 050h for alignment purposes

  ret                                         ;

FUNC_NAME ENDP

  END
