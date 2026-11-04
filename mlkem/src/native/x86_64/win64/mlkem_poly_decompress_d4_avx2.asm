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
; Name: poly_decompress_d4_avx2_asm
; Description: x86_64 AVX2 polynomial decompression (d=4)
; Signature: void mlk_poly_decompress_d4_avx2_asm(int16_t *r, const uint8_t *a, const uint8_t *data)
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
;     size_bytes: 128
;     permissions: read-only
;     c_parameter: const uint8_t *a
;     description: Input compressed polynomial
;   r8:
;     type: buffer
;     size_bytes: 32
;     permissions: read-only
;     c_parameter: const uint8_t *data
;     description: Precomputed decompression constants
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_poly_decompress_d4_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  .endprolog

  mov           eax,0d010d01h                 ;
  vmovd         xmm0,eax                      ;
  vpbroadcastd  ymm0,xmm0                     ;
  mov           eax,0f0000fh                  ;
  vmovd         xmm1,eax                      ;
  vpbroadcastd  ymm1,xmm1                     ;
  mov           eax,0800800h                  ;
  vmovd         xmm2,eax                      ;
  vpbroadcastd  ymm2,xmm2                     ;
  vmovdqa       ymm3,ymmword ptr [r8]         ;
  vmovq         xmm4,qword ptr [rdx]          ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx],ymm4        ;
  vmovq         xmm4,qword ptr [rdx+08h]      ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+020h],ymm4   ;
  vmovq         xmm4,qword ptr [rdx+010h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+040h],ymm4   ;
  vmovq         xmm4,qword ptr [rdx+018h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+060h],ymm4   ;
  vmovq         xmm4,qword ptr [rdx+020h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+080h],ymm4   ;
  vmovq         xmm4,qword ptr [rdx+028h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0a0h],ymm4   ;
  vmovq         xmm4,qword ptr [rdx+030h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0c0h],ymm4   ;
  vmovq         xmm4,qword ptr [rdx+038h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0e0h],ymm4   ;
  vmovq         xmm4,qword ptr [rdx+040h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0100h],ymm4  ;
  vmovq         xmm4,qword ptr [rdx+048h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0120h],ymm4  ;
  vmovq         xmm4,qword ptr [rdx+050h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0140h],ymm4  ;
  vmovq         xmm4,qword ptr [rdx+058h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0160h],ymm4  ;
  vmovq         xmm4,qword ptr [rdx+060h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0180h],ymm4  ;
  vmovq         xmm4,qword ptr [rdx+068h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+01a0h],ymm4  ;
  vmovq         xmm4,qword ptr [rdx+070h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+01c0h],ymm4  ;
  vmovq         xmm4,qword ptr [rdx+078h]     ;
  vinserti128   ymm4,ymm4,xmm4,01h            ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpand         ymm4,ymm4,ymm1                ;
  vpmullw       ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+01e0h],ymm4  ;
  vzeroupper                                  ;
  ret                                         ;

FUNC_NAME ENDP

  END
