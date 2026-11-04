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
; Name: poly_decompress_d5_avx2_asm
; Description: x86_64 AVX2 polynomial decompression (d=5)
; Signature: void mlk_poly_decompress_d5_avx2_asm(int16_t *r, const uint8_t *a, const uint8_t *data)
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
;     size_bytes: 160
;     permissions: read-only
;     c_parameter: const uint8_t *a
;     description: Input compressed polynomial
;   r8:
;     type: buffer
;     size_bytes: 96
;     permissions: read-only
;     c_parameter: const uint8_t *data
;     description: Precomputed decompression constants
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_poly_decompress_d5_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  .endprolog

  mov           eax,0d010d01h                      ;
  vmovd         xmm0,eax                           ;
  vpbroadcastd  ymm0,xmm0                          ;
  vmovdqa       ymm1,ymmword ptr [r8]              ;
  vmovdqa       ymm2,ymmword ptr [r8+020h]         ;
  vmovdqa       ymm3,ymmword ptr [r8+040h]         ;
  vmovq         xmm4,qword ptr [rdx]               ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+08h],04h   ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx],ymm4             ;
  vmovq         xmm4,qword ptr [rdx+0ah]           ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+012h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+020h],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+014h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+01ch],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+040h],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+01eh]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+026h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+060h],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+028h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+030h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+080h],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+032h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+03ah],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0a0h],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+03ch]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+044h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0c0h],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+046h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+04eh],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0e0h],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+050h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+058h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0100h],ymm4       ;
  vmovq         xmm4,qword ptr [rdx+05ah]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+062h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0120h],ymm4       ;
  vmovq         xmm4,qword ptr [rdx+064h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+06ch],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0140h],ymm4       ;
  vmovq         xmm4,qword ptr [rdx+06eh]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+076h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0160h],ymm4       ;
  vmovq         xmm4,qword ptr [rdx+078h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+080h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+0180h],ymm4       ;
  vmovq         xmm4,qword ptr [rdx+082h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+08ah],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+01a0h],ymm4       ;
  vmovq         xmm4,qword ptr [rdx+08ch]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+094h],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+01c0h],ymm4       ;
  vmovq         xmm4,qword ptr [rdx+096h]          ;
  vpinsrw       xmm4,xmm4,word ptr [rdx+09eh],04h  ;
  vinserti128   ymm4,ymm4,xmm4,01h                 ;
  vpshufb       ymm4,ymm4,ymm1                     ;
  vpand         ymm4,ymm4,ymm2                     ;
  vpmullw       ymm4,ymm4,ymm3                     ;
  vpmulhrsw     ymm4,ymm4,ymm0                     ;
  vmovdqu       ymmword ptr [rcx+01e0h],ymm4       ;
  vzeroupper                                       ;
  ret                                              ;

FUNC_NAME ENDP

  END
