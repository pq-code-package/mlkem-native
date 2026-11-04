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
; Name: poly_decompress_d10_avx2_asm
; Description: x86_64 AVX2 polynomial decompression (d=10)
; Signature: void mlk_poly_decompress_d10_avx2_asm(int16_t *r, const uint8_t *a, const uint8_t *data)
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
;     size_bytes: 320
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
FUNC_NAME EQU mlkem_poly_decompress_d10_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  .endprolog                                  ; none of the XMM registers >= 6 are used, nothing to save/restore

  mov           eax,0d013404h                 ;
  vmovd         xmm0,eax                      ;
  vpbroadcastd  ymm0,xmm0                     ;
  mov           eax,04h                       ;
  vmovq         xmm1,rax                      ;
  vpbroadcastq  ymm1,xmm1                     ;
  mov           eax,07fe01ff8h                ;
  vmovd         xmm2,eax                      ;
  vpbroadcastd  ymm2,xmm2                     ;
  vmovdqa       ymm3,ymmword ptr [r8]         ;
  vmovdqu       xmm4,xmmword ptr [rdx]        ;
  vmovd         xmm5,dword ptr [rdx+010h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx],ymm4        ;
  vmovdqu       xmm4,xmmword ptr [rdx+014h]   ;
  vmovd         xmm5,dword ptr [rdx+024h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+020h],ymm4   ;
  vmovdqu       xmm4,xmmword ptr [rdx+028h]   ;
  vmovd         xmm5,dword ptr [rdx+038h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+040h],ymm4   ;
  vmovdqu       xmm4,xmmword ptr [rdx+03ch]   ;
  vmovd         xmm5,dword ptr [rdx+04ch]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+060h],ymm4   ;
  vmovdqu       xmm4,xmmword ptr [rdx+050h]   ;
  vmovd         xmm5,dword ptr [rdx+060h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+080h],ymm4   ;
  vmovdqu       xmm4,xmmword ptr [rdx+064h]   ;
  vmovd         xmm5,dword ptr [rdx+074h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0a0h],ymm4   ;
  vmovdqu       xmm4,xmmword ptr [rdx+078h]   ;
  vmovd         xmm5,dword ptr [rdx+088h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0c0h],ymm4   ;
  vmovdqu       xmm4,xmmword ptr [rdx+08ch]   ;
  vmovd         xmm5,dword ptr [rdx+09ch]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0e0h],ymm4   ;
  vmovdqu       xmm4,xmmword ptr [rdx+0a0h]   ;
  vmovd         xmm5,dword ptr [rdx+0b0h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0100h],ymm4  ;
  vmovdqu       xmm4,xmmword ptr [rdx+0b4h]   ;
  vmovd         xmm5,dword ptr [rdx+0c4h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0120h],ymm4  ;
  vmovdqu       xmm4,xmmword ptr [rdx+0c8h]   ;
  vmovd         xmm5,dword ptr [rdx+0d8h]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0140h],ymm4  ;
  vmovdqu       xmm4,xmmword ptr [rdx+0dch]   ;
  vmovd         xmm5,dword ptr [rdx+0ech]     ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0160h],ymm4  ;
  vmovdqu       xmm4,xmmword ptr [rdx+0f0h]   ;
  vmovd         xmm5,dword ptr [rdx+0100h]    ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+0180h],ymm4  ;
  vmovdqu       xmm4,xmmword ptr [rdx+0104h]  ;
  vmovd         xmm5,dword ptr [rdx+0114h]    ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+01a0h],ymm4  ;
  vmovdqu       xmm4,xmmword ptr [rdx+0118h]  ;
  vmovd         xmm5,dword ptr [rdx+0128h]    ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+01c0h],ymm4  ;
  vmovdqu       xmm4,xmmword ptr [rdx+012ch]  ;
  vmovd         xmm5,dword ptr [rdx+013ch]    ;
  vinserti128   ymm4,ymm4,xmm5,01h            ;
  vpermq        ymm4,ymm4,094h                ;
  vpshufb       ymm4,ymm4,ymm3                ;
  vpsllvd       ymm4,ymm4,ymm1                ;
  vpsrlw        ymm4,ymm4,01h                 ;
  vpand         ymm4,ymm4,ymm2                ;
  vpmulhrsw     ymm4,ymm4,ymm0                ;
  vmovdqu       ymmword ptr [rcx+01e0h],ymm4  ;
  vzeroupper                                  ;
  ret                                         ;

FUNC_NAME ENDP

  END
