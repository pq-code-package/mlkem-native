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
; Name: poly_mulcache_compute_avx2_asm
; Description: x86_64 AVX2 mulcache computation
; Signature: void mlk_poly_mulcache_compute_avx2_asm(int16_t *out, const int16_t *in, const int16_t *qdata)
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 256
;     permissions: write-only
;     c_parameter: int16_t *out
;     description: Output mulcache (128 x int16_t)
;   rdx:
;     type: buffer
;     size_bytes: 512
;     permissions: read-only
;     c_parameter: const int16_t *in
;     description: Input polynomial (256 x int16_t)
;   r8:
;     type: buffer
;     size_bytes: 1248
;     permissions: read-only
;     c_parameter: const int16_t *qdata
;     description: Precomputed constants (624 x int16_t)
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mlkem_poly_mulcache_compute_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

  sub           rsp,058h                      ; 058h and not 050h for alignment purposes
  .allocstack   058h

  vmovdqa        xmmword ptr [rsp+000h],xmm6  ; save xmm6 on stack
  .savexmm128    xmm6,000h
  vmovdqa        xmmword ptr [rsp+010h],xmm7  ; save xmm7 on stack
  .savexmm128    xmm7,010h
  vmovdqa        xmmword ptr [rsp+020h],xmm8  ; save xmm8 on stack
  .savexmm128    xmm8,020h
  vmovdqa        xmmword ptr [rsp+030h],xmm9  ; save xmm9 on stack
  .savexmm128    xmm9,030h
  vmovdqa        xmmword ptr [rsp+040h],xmm10 ; save xmm10 on stack
  .savexmm128    xmm10,040h
  .endprolog

  mov           eax,0d010d01h                 ;
  vmovd         xmm0,eax                      ;
  vpbroadcastd  ymm0,xmm0                     ;
  vmovdqa       ymm2,ymmword ptr [rdx+020h]   ;
  vmovdqa       ymm3,ymmword ptr [rdx+060h]   ;
  vmovdqa       ymm4,ymmword ptr [r8+03e0h]   ;
  vmovdqa       ymm1,ymmword ptr [r8+0460h]   ;
  vpmullw       ymm5,ymm1,ymm2                ;
  vpmullw       ymm6,ymm1,ymm3                ;
  vpmulhw       ymm7,ymm4,ymm2                ;
  vpmulhw       ymm8,ymm4,ymm3                ;
  vpmulhw       ymm9,ymm0,ymm5                ;
  vpmulhw       ymm10,ymm0,ymm6               ;
  vpsubw        ymm7,ymm7,ymm9                ;
  vpsubw        ymm8,ymm8,ymm10               ;
  vmovdqa       ymmword ptr [rcx],ymm7        ;
  vmovdqa       ymmword ptr [rcx+020h],ymm8   ;
  vmovdqa       ymm2,ymmword ptr [rdx+0a0h]   ;
  vmovdqa       ymm3,ymmword ptr [rdx+0e0h]   ;
  vmovdqa       ymm4,ymmword ptr [r8+0400h]   ;
  vmovdqa       ymm1,ymmword ptr [r8+0480h]   ;
  vpmullw       ymm5,ymm1,ymm2                ;
  vpmullw       ymm6,ymm1,ymm3                ;
  vpmulhw       ymm7,ymm4,ymm2                ;
  vpmulhw       ymm8,ymm4,ymm3                ;
  vpmulhw       ymm9,ymm0,ymm5                ;
  vpmulhw       ymm10,ymm0,ymm6               ;
  vpsubw        ymm7,ymm7,ymm9                ;
  vpsubw        ymm8,ymm8,ymm10               ;
  vmovdqa       ymmword ptr [rcx+040h],ymm7   ;
  vmovdqa       ymmword ptr [rcx+060h],ymm8   ;
  vmovdqa       ymm2,ymmword ptr [rdx+0120h]  ;
  vmovdqa       ymm3,ymmword ptr [rdx+0160h]  ;
  vmovdqa       ymm4,ymmword ptr [r8+0420h]   ;
  vmovdqa       ymm1,ymmword ptr [r8+04a0h]   ;
  vpmullw       ymm5,ymm1,ymm2                ;
  vpmullw       ymm6,ymm1,ymm3                ;
  vpmulhw       ymm7,ymm4,ymm2                ;
  vpmulhw       ymm8,ymm4,ymm3                ;
  vpmulhw       ymm9,ymm0,ymm5                ;
  vpmulhw       ymm10,ymm0,ymm6               ;
  vpsubw        ymm7,ymm7,ymm9                ;
  vpsubw        ymm8,ymm8,ymm10               ;
  vmovdqa       ymmword ptr [rcx+080h],ymm7   ;
  vmovdqa       ymmword ptr [rcx+0a0h],ymm8   ;
  vmovdqa       ymm2,ymmword ptr [rdx+01a0h]  ;
  vmovdqa       ymm3,ymmword ptr [rdx+01e0h]  ;
  vmovdqa       ymm4,ymmword ptr [r8+0440h]   ;
  vmovdqa       ymm1,ymmword ptr [r8+04c0h]   ;
  vpmullw       ymm5,ymm1,ymm2                ;
  vpmullw       ymm6,ymm1,ymm3                ;
  vpmulhw       ymm7,ymm4,ymm2                ;
  vpmulhw       ymm8,ymm4,ymm3                ;
  vpmulhw       ymm9,ymm0,ymm5                ;
  vpmulhw       ymm10,ymm0,ymm6               ;
  vpsubw        ymm7,ymm7,ymm9                ;
  vpsubw        ymm8,ymm8,ymm10               ;
  vmovdqa       ymmword ptr [rcx+0c0h],ymm7   ;
  vmovdqa       ymmword ptr [rcx+0e0h],ymm8   ;

  vzeroupper                                  ;

  vmovdqa       xmm6,xmmword ptr [rsp+000h]   ; restore xmm6 from stack
  vmovdqa       xmm7,xmmword ptr [rsp+010h]   ; restore xmm7 from stack
  vmovdqa       xmm8,xmmword ptr [rsp+020h]   ; restore xmm8 from stack
  vmovdqa       xmm9,xmmword ptr [rsp+030h]   ; restore xmm9 from stack
  vmovdqa       xmm10,xmmword ptr [rsp+040h]  ; restore xmm10 from stack

  add           rsp,058h                      ; 058h and not 050h for alignment purposes

  ret                                         ;

FUNC_NAME ENDP

  END
