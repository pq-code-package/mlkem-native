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
; Name: poly_decompress_d11_avx2_asm
; Description: x86_64 AVX2 polynomial decompression (d=11)
; Signature: void mlk_poly_decompress_d11_avx2_asm(int16_t *r, const uint8_t *a, const uint8_t *data)
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
;     size_bytes: 352
;     permissions: read-only
;     c_parameter: const uint8_t *a
;     description: Input compressed polynomial
;   r8:
;     type: buffer
;     size_bytes: 128
;     permissions: read-only
;     c_parameter: const uint8_t *data
;     description: Precomputed decompression constants
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_poly_decompress_d11_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,028h                            ; 028h and not 020h for alignment purposes
  .allocstack   028h

  vmovdqa       xmmword ptr [rsp+000h],xmm6         ; save xmm6 on stack
  .savexmm128   xmm6,000h
  vmovdqa       xmmword ptr [rsp+010h],xmm7         ; save xmm7 on stack
  .savexmm128   xmm7,010h
  .endprolog

  mov           eax,0d010d01h                       ;
  vmovd         xmm0,eax                            ;
  vpbroadcastd  ymm0,xmm0                           ;
  mov           eax,07ff07ff0h                      ;
  vmovd         xmm1,eax                            ;
  vpbroadcastd  ymm1,xmm1                           ;
  vmovdqa       ymm2,ymmword ptr [r8]               ;
  vmovdqa       ymm3,ymmword ptr [r8+020h]          ;
  vmovdqa       ymm4,ymmword ptr [r8+040h]          ;
  vmovdqa       ymm5,ymmword ptr [r8+060h]          ;
  vmovdqu       xmm6,xmmword ptr [rdx]              ;
  vmovd         xmm7,dword ptr [rdx+010h]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+014h],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx],ymm6              ;
  vmovdqu       xmm6,xmmword ptr [rdx+016h]         ;
  vmovd         xmm7,dword ptr [rdx+026h]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+02ah],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+020h],ymm6         ;
  vmovdqu       xmm6,xmmword ptr [rdx+02ch]         ;
  vmovd         xmm7,dword ptr [rdx+03ch]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+040h],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+040h],ymm6         ;
  vmovdqu       xmm6,xmmword ptr [rdx+042h]         ;
  vmovd         xmm7,dword ptr [rdx+052h]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+056h],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+060h],ymm6         ;
  vmovdqu       xmm6,xmmword ptr [rdx+058h]         ;
  vmovd         xmm7,dword ptr [rdx+068h]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+06ch],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+080h],ymm6         ;
  vmovdqu       xmm6,xmmword ptr [rdx+06eh]         ;
  vmovd         xmm7,dword ptr [rdx+07eh]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+082h],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0a0h],ymm6         ;
  vmovdqu       xmm6,xmmword ptr [rdx+084h]         ;
  vmovd         xmm7,dword ptr [rdx+094h]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+098h],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0c0h],ymm6         ;
  vmovdqu       xmm6,xmmword ptr [rdx+09ah]         ;
  vmovd         xmm7,dword ptr [rdx+0aah]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+0aeh],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0e0h],ymm6         ;
  vmovdqu       xmm6,xmmword ptr [rdx+0b0h]         ;
  vmovd         xmm7,dword ptr [rdx+0c0h]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+0c4h],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0100h],ymm6        ;
  vmovdqu       xmm6,xmmword ptr [rdx+0c6h]         ;
  vmovd         xmm7,dword ptr [rdx+0d6h]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+0dah],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0120h],ymm6        ;
  vmovdqu       xmm6,xmmword ptr [rdx+0dch]         ;
  vmovd         xmm7,dword ptr [rdx+0ech]           ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+0f0h],02h   ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0140h],ymm6        ;
  vmovdqu       xmm6,xmmword ptr [rdx+0f2h]         ;
  vmovd         xmm7,dword ptr [rdx+0102h]          ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+0106h],02h  ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0160h],ymm6        ;
  vmovdqu       xmm6,xmmword ptr [rdx+0108h]        ;
  vmovd         xmm7,dword ptr [rdx+0118h]          ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+011ch],02h  ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+0180h],ymm6        ;
  vmovdqu       xmm6,xmmword ptr [rdx+011eh]        ;
  vmovd         xmm7,dword ptr [rdx+012eh]          ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+0132h],02h  ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+01a0h],ymm6        ;
  vmovdqu       xmm6,xmmword ptr [rdx+0134h]        ;
  vmovd         xmm7,dword ptr [rdx+0144h]          ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+0148h],02h  ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+01c0h],ymm6        ;
  vmovdqu       xmm6,xmmword ptr [rdx+014ah]        ;
  vmovd         xmm7,dword ptr [rdx+015ah]          ;
  vpinsrw       xmm7,xmm7,word ptr [rdx+015eh],02h  ;
  vinserti128   ymm6,ymm6,xmm7,01h                  ;
  vpermq        ymm6,ymm6,094h                      ;
  vpshufb       ymm6,ymm6,ymm2                      ;
  vpsrlvd       ymm6,ymm6,ymm3                      ;
  vpsrlvq       ymm6,ymm6,ymm4                      ;
  vpmullw       ymm6,ymm6,ymm5                      ;
  vpsrlw        ymm6,ymm6,01h                       ;
  vpand         ymm6,ymm6,ymm1                      ;
  vpmulhrsw     ymm6,ymm6,ymm0                      ;
  vmovdqu       ymmword ptr [rcx+01e0h],ymm6        ;

  vzeroupper                                        ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]         ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]         ; restore xmm7 from stack

  add           rsp,028h                            ; 028h and not 020h for alignment purposes

  ret                                               ;

FUNC_NAME ENDP

  END
