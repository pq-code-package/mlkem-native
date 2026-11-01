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
; Name: poly_compress_d4_avx2_asm
; Description: x86_64 AVX2 polynomial compression (d=4)
; Signature: void mlk_poly_compress_d4_avx2_asm(uint8_t *r, const int16_t *a, const uint8_t *data)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 128
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
FUNC_NAME EQU mlkem_poly_compress_d4_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,038h                      ; 038h and not 030h for alignment purposes
  .allocstack   038h

  vmovdqa       xmmword ptr [rsp+000h],xmm6   ; save xmm6 on stack
  .savexmm128   xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7   ; save xmm7 on stack
  .savexmm128   xmm7,010h
  vmovdqa       xmmword ptr [rsp+020h],xmm8   ; save xmm8 on stack
  .savexmm128   xmm8,020h
  .endprolog

  mov           eax,04ebf4ebfh                ;
  vmovd         xmm0,eax                      ;
  vpbroadcastd  ymm0,xmm0                     ;
  mov           eax,02000200h                 ;
  vmovd         xmm1,eax                      ;
  vpbroadcastd  ymm1,xmm1                     ;
  mov           eax,0f000fh                   ;
  vmovd         xmm2,eax                      ;
  vpbroadcastd  ymm2,xmm2                     ;
  mov           eax,010011001h                ;
  vmovd         xmm3,eax                      ;
  vpbroadcastd  ymm3,xmm3                     ;
  vmovdqa       ymm4,ymmword ptr [r8]         ;
  vmovdqa       ymm5,ymmword ptr [rdx]        ;
  vmovdqa       ymm6,ymmword ptr [rdx+020h]   ;
  vmovdqa       ymm7,ymmword ptr [rdx+040h]   ;
  vmovdqa       ymm8,ymmword ptr [rdx+060h]   ;
  vpmulhw       ymm5,ymm5,ymm0                ;
  vpmulhw       ymm6,ymm6,ymm0                ;
  vpmulhw       ymm7,ymm7,ymm0                ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpmulhrsw     ymm5,ymm5,ymm1                ;
  vpmulhrsw     ymm6,ymm6,ymm1                ;
  vpmulhrsw     ymm7,ymm7,ymm1                ;
  vpmulhrsw     ymm8,ymm8,ymm1                ;
  vpand         ymm5,ymm5,ymm2                ;
  vpand         ymm6,ymm6,ymm2                ;
  vpand         ymm7,ymm7,ymm2                ;
  vpand         ymm8,ymm8,ymm2                ;
  vpackuswb     ymm5,ymm5,ymm6                ;
  vpackuswb     ymm7,ymm7,ymm8                ;
  vpmaddubsw    ymm5,ymm5,ymm3                ;
  vpmaddubsw    ymm7,ymm7,ymm3                ;
  vpackuswb     ymm5,ymm5,ymm7                ;
  vpermd        ymm5,ymm4,ymm5                ;
  vmovdqu       ymmword ptr [rcx],ymm5        ;
  vmovdqa       ymm5,ymmword ptr [rdx+080h]   ;
  vmovdqa       ymm6,ymmword ptr [rdx+0a0h]   ;
  vmovdqa       ymm7,ymmword ptr [rdx+0c0h]   ;
  vmovdqa       ymm8,ymmword ptr [rdx+0e0h]   ;
  vpmulhw       ymm5,ymm5,ymm0                ;
  vpmulhw       ymm6,ymm6,ymm0                ;
  vpmulhw       ymm7,ymm7,ymm0                ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpmulhrsw     ymm5,ymm5,ymm1                ;
  vpmulhrsw     ymm6,ymm6,ymm1                ;
  vpmulhrsw     ymm7,ymm7,ymm1                ;
  vpmulhrsw     ymm8,ymm8,ymm1                ;
  vpand         ymm5,ymm5,ymm2                ;
  vpand         ymm6,ymm6,ymm2                ;
  vpand         ymm7,ymm7,ymm2                ;
  vpand         ymm8,ymm8,ymm2                ;
  vpackuswb     ymm5,ymm5,ymm6                ;
  vpackuswb     ymm7,ymm7,ymm8                ;
  vpmaddubsw    ymm5,ymm5,ymm3                ;
  vpmaddubsw    ymm7,ymm7,ymm3                ;
  vpackuswb     ymm5,ymm5,ymm7                ;
  vpermd        ymm5,ymm4,ymm5                ;
  vmovdqu       ymmword ptr [rcx+020h],ymm5   ;
  vmovdqa       ymm5,ymmword ptr [rdx+0100h]  ;
  vmovdqa       ymm6,ymmword ptr [rdx+0120h]  ;
  vmovdqa       ymm7,ymmword ptr [rdx+0140h]  ;
  vmovdqa       ymm8,ymmword ptr [rdx+0160h]  ;
  vpmulhw       ymm5,ymm5,ymm0                ;
  vpmulhw       ymm6,ymm6,ymm0                ;
  vpmulhw       ymm7,ymm7,ymm0                ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpmulhrsw     ymm5,ymm5,ymm1                ;
  vpmulhrsw     ymm6,ymm6,ymm1                ;
  vpmulhrsw     ymm7,ymm7,ymm1                ;
  vpmulhrsw     ymm8,ymm8,ymm1                ;
  vpand         ymm5,ymm5,ymm2                ;
  vpand         ymm6,ymm6,ymm2                ;
  vpand         ymm7,ymm7,ymm2                ;
  vpand         ymm8,ymm8,ymm2                ;
  vpackuswb     ymm5,ymm5,ymm6                ;
  vpackuswb     ymm7,ymm7,ymm8                ;
  vpmaddubsw    ymm5,ymm5,ymm3                ;
  vpmaddubsw    ymm7,ymm7,ymm3                ;
  vpackuswb     ymm5,ymm5,ymm7                ;
  vpermd        ymm5,ymm4,ymm5                ;
  vmovdqu       ymmword ptr [rcx+040h],ymm5   ;
  vmovdqa       ymm5,ymmword ptr [rdx+0180h]  ;
  vmovdqa       ymm6,ymmword ptr [rdx+01a0h]  ;
  vmovdqa       ymm7,ymmword ptr [rdx+01c0h]  ;
  vmovdqa       ymm8,ymmword ptr [rdx+01e0h]  ;
  vpmulhw       ymm5,ymm5,ymm0                ;
  vpmulhw       ymm6,ymm6,ymm0                ;
  vpmulhw       ymm7,ymm7,ymm0                ;
  vpmulhw       ymm8,ymm8,ymm0                ;
  vpmulhrsw     ymm5,ymm5,ymm1                ;
  vpmulhrsw     ymm6,ymm6,ymm1                ;
  vpmulhrsw     ymm7,ymm7,ymm1                ;
  vpmulhrsw     ymm8,ymm8,ymm1                ;
  vpand         ymm5,ymm5,ymm2                ;
  vpand         ymm6,ymm6,ymm2                ;
  vpand         ymm7,ymm7,ymm2                ;
  vpand         ymm8,ymm8,ymm2                ;
  vpackuswb     ymm5,ymm5,ymm6                ;
  vpackuswb     ymm7,ymm7,ymm8                ;
  vpmaddubsw    ymm5,ymm5,ymm3                ;
  vpmaddubsw    ymm7,ymm7,ymm3                ;
  vpackuswb     ymm5,ymm5,ymm7                ;
  vpermd        ymm5,ymm4,ymm5                ;
  vmovdqu       ymmword ptr [rcx+060h],ymm5   ;

  vzeroupper                                  ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]   ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]   ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]   ; restore xmm8 from stack

  add           rsp,038h                      ; 038h and not 030h for alignment purposes

  ret                                         ;

FUNC_NAME ENDP

  END
