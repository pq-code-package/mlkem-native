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
; Name: keccak_f1600_x4_avx2_asm
; Description: x86_64 AVX2 Keccak-f[1600] permutation for four sequential states
; Signature: void mld_keccak_f1600_x4_avx2_asm(uint64_t states[100], const uint64_t rc[24], const uint64_t rho8[4], const uint64_t rho56[4])
; ABI:
;   Architecture: x86_64
;   CallingConvention: Microsoft AMD64 ABI
;   Features: [AVX2]
;   rcx:
;     type: buffer
;     size_bytes: 800
;     permissions: read/write
;     c_parameter: uint64_t states[100]
;     description: Four sequential Keccak states (4 x 25 x uint64_t)
;   rdx:
;     type: buffer
;     size_bytes: 192
;     permissions: read-only
;     c_parameter: const uint64_t rc[24]
;     description: Round constants (24 x uint64_t)
;   r8:
;     type: buffer
;     size_bytes: 32
;     permissions: read-only
;     c_parameter: const uint64_t rho8[4]
;     description: Rotation constant rho8 (4 x uint64_t)
;   r9:
;     type: buffer
;     size_bytes: 32
;     permissions: read-only
;     c_parameter: const uint64_t rho56[4]
;     description: Rotation constant rho56 (4 x uint64_t)
;

IFNDEF FUNC_NAME
FUNC_NAME EQU mldsa_keccak_f1600_x4_avx2_asm
ENDIF

FUNC_NAME PROC FRAME

         sub           rsp,03B8h                            ; 32-byte YMM scratch (+16 for alignment) + 10 XMM saves, RSP 16-byte aligned
         .allocstack   03B8h

         vmovdqa       xmmword ptr [rsp+0310h],xmm6         ; save xmm6 on stack
         .savexmm128   xmm6,0310h
         vmovdqa       xmmword ptr [rsp+0320h],xmm7         ; save xmm7 on stack
         .savexmm128   xmm7,0320h
         vmovdqa       xmmword ptr [rsp+0330h],xmm8         ; save xmm8 on stack
         .savexmm128   xmm8,0330h
         vmovdqa       xmmword ptr [rsp+0340h],xmm9         ; save xmm9 on stack
         .savexmm128   xmm9,0340h
         vmovdqa       xmmword ptr [rsp+0350h],xmm10        ; save xmm10 on stack
         .savexmm128   xmm10,0350h
         vmovdqa       xmmword ptr [rsp+0360h],xmm11        ; save xmm11 on stack
         .savexmm128   xmm11,0360h
         vmovdqa       xmmword ptr [rsp+0370h],xmm12        ; save xmm12 on stack
         .savexmm128   xmm12,0370h
         vmovdqa       xmmword ptr [rsp+0380h],xmm13        ; save xmm13 on stack
         .savexmm128   xmm13,0380h
         vmovdqa       xmmword ptr [rsp+0390h],xmm14        ; save xmm14 on stack
         .savexmm128   xmm14,0390h
         vmovdqa       xmmword ptr [rsp+03A0h],xmm15        ; save xmm15 on stack
         .savexmm128   xmm15,03A0h

         .endprolog

                                                            ; Win64 argument registers are used directly (no SysV shuffling):
                                                            ;   rcx = states, rdx = rc (advances per round),
                                                            ;   r8 = rho8, r9 = rho56, r10 = round counter, r11 = aligned scratch
         lea           r11,[rsp+01fh]                       ; separate 32-byte aligned base for YMM scratch area
         and           r11,0ffffffffffffffe0h               ; r11 is now 32-byte aligned


         vmovdqu       ymm0,ymmword ptr [rcx]               ;
         vmovdqu       ymm3,ymmword ptr [rcx+0c8h]          ;
         vmovdqu       ymm1,ymmword ptr [rcx+0190h]         ;
         vmovdqu       ymm4,ymmword ptr [rcx+0258h]         ;
         vpunpcklqdq   ymm2,ymm0,ymm3                       ;
         vpunpckhqdq   ymm0,ymm0,ymm3                       ;
         vpunpcklqdq   ymm3,ymm1,ymm4                       ;
         vperm2i128    ymm7,ymm2,ymm3,020h                  ;
         vpunpckhqdq   ymm1,ymm1,ymm4                       ;
         vperm2i128    ymm3,ymm2,ymm3,031h                  ;
         vmovdqu       ymm4,ymmword ptr [rcx+0278h]         ;
         vmovdqa       ymmword ptr [r11+040h],ymm3          ;
         vperm2i128    ymm3,ymm0,ymm1,031h                  ;
         vmovdqa       ymmword ptr [r11],ymm7               ;
         vperm2i128    ymm7,ymm0,ymm1,020h                  ;
         vmovdqu       ymm0,ymmword ptr [rcx+020h]          ;
         vmovdqu       ymm1,ymmword ptr [rcx+01b0h]         ;
         vmovdqa       ymmword ptr [r11+060h],ymm3          ;
         vmovdqu       ymm3,ymmword ptr [rcx+0e8h]          ;
         vmovdqa       ymmword ptr [r11+020h],ymm7          ;
         vpunpcklqdq   ymm2,ymm0,ymm3                       ;
         vpunpckhqdq   ymm0,ymm0,ymm3                       ;
         vpunpcklqdq   ymm3,ymm1,ymm4                       ;
         vperm2i128    ymm7,ymm2,ymm3,020h                  ;
         vpunpckhqdq   ymm1,ymm1,ymm4                       ;
         vperm2i128    ymm3,ymm2,ymm3,031h                  ;
         vmovdqu       ymm4,ymmword ptr [rcx+0298h]         ;
         vperm2i128    ymm14,ymm0,ymm1,031h                 ;
         vmovdqa       ymmword ptr [r11+080h],ymm7          ;
         vperm2i128    ymm7,ymm0,ymm1,020h                  ;
         vmovdqu       ymm0,ymmword ptr [rcx+040h]          ;
         vmovdqu       ymm1,ymmword ptr [rcx+01d0h]         ;
         vmovdqa       ymmword ptr [r11+0c0h],ymm3          ;
         vmovdqu       ymm3,ymmword ptr [rcx+0108h]         ;
         vmovdqu       ymm10,ymm14                          ;
         vmovdqa       ymmword ptr [r11+0a0h],ymm7          ;
         vpunpcklqdq   ymm2,ymm0,ymm3                       ;
         vpunpckhqdq   ymm0,ymm0,ymm3                       ;
         vpunpcklqdq   ymm3,ymm1,ymm4                       ;
         vpunpckhqdq   ymm1,ymm1,ymm4                       ;
         vperm2i128    ymm11,ymm2,ymm3,020h                 ;
         vperm2i128    ymm3,ymm2,ymm3,031h                  ;
         vperm2i128    ymm7,ymm0,ymm1,020h                  ;
         vmovdqa       ymmword ptr [r11+0100h],ymm3         ;
         vperm2i128    ymm8,ymm0,ymm1,031h                  ;
         vmovdqu       ymm3,ymmword ptr [rcx+0128h]         ;
         vmovdqu       ymm0,ymmword ptr [rcx+060h]          ;
         vmovdqu       ymm1,ymmword ptr [rcx+01f0h]         ;
         vmovdqa       ymmword ptr [r11+0e0h],ymm7          ;
         vmovdqu       ymm14,ymm11                          ;
         vmovdqu       ymm4,ymmword ptr [rcx+02b8h]         ;
         vmovdqu       ymm5,ymmword ptr [rcx+02f8h]         ;
         vpunpcklqdq   ymm2,ymm0,ymm3                       ;
         vpunpckhqdq   ymm0,ymm0,ymm3                       ;
         vpunpcklqdq   ymm3,ymm1,ymm4                       ;
         vpunpckhqdq   ymm1,ymm1,ymm4                       ;
         vmovdqu       ymm4,ymmword ptr [rcx+02d8h]         ;
         vperm2i128    ymm15,ymm2,ymm3,020h                 ;
         vperm2i128    ymm3,ymm2,ymm3,031h                  ;
         vperm2i128    ymm7,ymm0,ymm1,020h                  ;
         vperm2i128    ymm9,ymm0,ymm1,031h                  ;
         vmovdqa       ymmword ptr [r11+0140h],ymm3         ;
         vmovdqu       ymm0,ymmword ptr [rcx+080h]          ;
         vmovdqu       ymm3,ymmword ptr [rcx+0148h]         ;
         vmovdqu       ymm1,ymmword ptr [rcx+0210h]         ;
         vmovdqa       ymmword ptr [r11+0120h],ymm7         ;
         vpunpcklqdq   ymm2,ymm0,ymm3                       ;
         vpunpckhqdq   ymm0,ymm0,ymm3                       ;
         vpunpcklqdq   ymm3,ymm1,ymm4                       ;
         vpunpckhqdq   ymm1,ymm1,ymm4                       ;
         vperm2i128    ymm7,ymm2,ymm3,020h                  ;
         vperm2i128    ymm13,ymm2,ymm3,031h                 ;
         vperm2i128    ymm3,ymm0,ymm1,031h                  ;
         vmovdqa       ymmword ptr [r11+0160h],ymm7         ;
         vperm2i128    ymm7,ymm0,ymm1,020h                  ;
         vmovdqu       ymm0,ymmword ptr [rcx+0a0h]          ;
         vmovdqu       ymm1,ymmword ptr [rcx+0230h]         ;
         vmovdqa       ymmword ptr [r11+01a0h],ymm3         ;
         vmovdqu       ymm3,ymmword ptr [rcx+0168h]         ;
         vpunpcklqdq   ymm4,ymm1,ymm5                       ;
         vpunpckhqdq   ymm1,ymm1,ymm5                       ;
         vmovdqa       ymmword ptr [r11+0180h],ymm7         ;
         vpunpcklqdq   ymm2,ymm0,ymm3                       ;
         vpunpckhqdq   ymm0,ymm0,ymm3                       ;
         vperm2i128    ymm12,ymm2,ymm4,020h                 ;
         vperm2i128    ymm3,ymm0,ymm1,020h                  ;
         vperm2i128    ymm7,ymm2,ymm4,031h                  ;
         vperm2i128    ymm4,ymm0,ymm1,031h                  ;
         vmovq         xmm0,qword ptr [rcx+0250h]           ;
         vmovq         xmm1,qword ptr [rcx+0c0h]            ;
         vmovdqa       ymmword ptr [r11+01c0h],ymm12        ;
         vmovdqa       ymmword ptr [r11+01e0h],ymm4         ;
         vpinsrq       xmm0,xmm0,qword ptr [rcx+0318h],01h  ;
         vpinsrq       xmm1,xmm1,qword ptr [rcx+0188h],01h  ;
         vinserti128   ymm2,ymm1,xmm0,01h                   ;
         mov           r10,00h                              ;

         ALIGN         16

LLmld_keccak_f1600_x4_avx2_asm:

         vmovdqa       ymm4,ymmword ptr [r11+0a0h]          ;
         vpxor         ymm0,ymm9,ymmword ptr [r11+01c0h]    ;
         vmovdqa       ymmword ptr [r11+0200h],ymm9         ;
         vmovdqu       ymm9,ymm10                           ;
         vmovdqa       ymm11,ymmword ptr [r11+0c0h]         ;
         vmovdqa       ymm12,ymmword ptr [r11+0160h]        ;
         vmovdqa       ymmword ptr [r11+0240h],ymm3         ;
         vpxor         ymm1,ymm4,ymmword ptr [r11+0100h]    ;
         vmovdqa       ymm10,ymmword ptr [r11+040h]         ;
         vmovdqa       ymmword ptr [r11+0220h],ymm4         ;
         vpxor         ymm12,ymm12,ymm3                     ;
         vmovdqa       ymm6,ymmword ptr [r11+020h]          ;
         vmovdqa       ymm4,ymmword ptr [r11+0140h]         ;
         vmovdqa       ymmword ptr [r11+02a0h],ymm14        ;
         vpxor         ymm0,ymm0,ymm1                       ;
         vpxor         ymm1,ymm11,ymm8                      ;
         vpxor         ymm11,ymm7,ymmword ptr [r11+0180h]   ;
         vmovdqa       ymmword ptr [r11+0280h],ymm10        ;
         vpxor         ymm12,ymm12,ymm1                     ;
         vpxor         ymm1,ymm9,ymm15                      ;
         vmovdqa       ymm3,ymmword ptr [r11+0e0h]          ;
         vmovdqa       ymmword ptr [r11+0260h],ymm8         ;
         vpxor         ymm11,ymm11,ymm1                     ;
         vpxor         ymm1,ymm14,ymmword ptr [r11+0120h]   ;
         vpxor         ymm12,ymm12,ymm6                     ;
         vmovdqa       ymm8,ymmword ptr [r11+060h]          ;
         vpxor         ymm11,ymm11,ymm10                    ;
         vpxor         ymm10,ymm13,ymmword ptr [r11+01e0h]  ;
         vpxor         ymm3,ymm3,ymm4                       ;
         vmovdqa       ymmword ptr [r11+02c0h],ymm4         ;
         vpsrlq        ymm4,ymm12,03fh                      ;
         vpsrlq        ymm5,ymm11,03fh                      ;
         vpxor         ymm0,ymm0,ymmword ptr [r11]          ;
         vpxor         ymm10,ymm10,ymm1                     ;
         vmovdqa       ymm1,ymmword ptr [r11+080h]          ;
         vpxor         ymm10,ymm10,ymm8                     ;
         vmovdqu       ymm14,ymm1                           ;
         vpxor         ymm1,ymm2,ymmword ptr [r11+01a0h]    ;
         vmovdqa       ymmword ptr [r11+02e0h],ymm14        ;
         vpxor         ymm1,ymm1,ymm3                       ;
         vpsllq        ymm3,ymm12,01h                       ;
         vpor          ymm3,ymm3,ymm4                       ;
         vpsllq        ymm4,ymm11,01h                       ;
         vpxor         ymm1,ymm1,ymm14                      ;
         vpor          ymm4,ymm4,ymm5                       ;
         vpsrlq        ymm14,ymm10,03fh                     ;
         vpxor         ymm3,ymm3,ymm1                       ;
         vpsllq        ymm5,ymm10,01h                       ;
         vpxor         ymm4,ymm4,ymm0                       ;
         vpor          ymm5,ymm5,ymm14                      ;
         vpxor         ymm6,ymm4,ymm6                       ;
         vpxor         ymm5,ymm5,ymm12                      ;
         vpsrlq        ymm12,ymm1,03fh                      ;
         vpsllq        ymm1,ymm1,01h                        ;
         vpxor         ymm7,ymm5,ymm7                       ;
         vpxor         ymm9,ymm5,ymm9                       ;
         vpor          ymm1,ymm1,ymm12                      ;
         vpxor         ymm12,ymm3,ymmword ptr [r11]         ;
         vpxor         ymm1,ymm1,ymm11                      ;
         vpsrlq        ymm11,ymm0,03fh                      ;
         vpsllq        ymm0,ymm0,01h                        ;
         vpxor         ymm13,ymm1,ymm13                     ;
         vpxor         ymm8,ymm1,ymm8                       ;
         vpor          ymm0,ymm0,ymm11                      ;
         vpxor         ymm0,ymm0,ymm10                      ;
         vpxor         ymm10,ymm4,ymmword ptr [r11+0c0h]    ;
         vpxor         ymm2,ymm0,ymm2                       ;
         vpsrlq        ymm11,ymm10,014h                     ;
         vpsllq        ymm10,ymm10,02ch                     ;
         vpor          ymm10,ymm10,ymm11                    ;
         vpxor         ymm11,ymm5,ymm15                     ;
         vpbroadcastq  ymm15,qword ptr [rdx]                ;
         vpsrlq        ymm14,ymm11,015h                     ;
         vpsllq        ymm11,ymm11,02bh                     ;
         vpor          ymm11,ymm11,ymm14                    ;
         vpandn        ymm14,ymm10,ymm11                    ;
         vpxor         ymm14,ymm14,ymm15                    ;
         vpxor         ymm15,ymm14,ymm12                    ;
         vpsrlq        ymm14,ymm13,02bh                     ;
         vpsllq        ymm13,ymm13,015h                     ;
         vmovdqa       ymmword ptr [r11],ymm15              ;
         vpor          ymm13,ymm13,ymm14                    ;
         vpandn        ymm14,ymm11,ymm13                    ;
         vpxor         ymm15,ymm14,ymm10                    ;
         vpsrlq        ymm14,ymm2,032h                      ;
         vpsllq        ymm2,ymm2,0eh                        ;
         vmovdqa       ymmword ptr [r11+020h],ymm15         ;
         vpor          ymm2,ymm2,ymm14                      ;
         vpandn        ymm14,ymm13,ymm2                     ;
         vpxor         ymm11,ymm14,ymm11                    ;
         vmovdqa       ymmword ptr [r11+040h],ymm11         ;
         vpandn        ymm11,ymm2,ymm12                     ;
         vpandn        ymm12,ymm12,ymm10                    ;
         vpxor         ymm11,ymm11,ymm13                    ;
         vmovdqa       ymmword ptr [r11+060h],ymm11         ;
         vpxor         ymm11,ymm12,ymm2                     ;
         vpsrlq        ymm2,ymm8,024h                       ;
         vpsllq        ymm8,ymm8,01ch                       ;
         vmovdqa       ymmword ptr [r11+080h],ymm11         ;
         vpor          ymm8,ymm8,ymm2                       ;
         vpxor         ymm2,ymm0,ymmword ptr [r11+0e0h]     ;
         vpsrlq        ymm10,ymm2,02ch                      ;
         vpsllq        ymm2,ymm2,014h                       ;
         vpor          ymm2,ymm2,ymm10                      ;
         vpxor         ymm10,ymm3,ymmword ptr [r11+0100h]   ;
         vpsrlq        ymm11,ymm10,03dh                     ;
         vpsllq        ymm10,ymm10,03h                      ;
         vpor          ymm10,ymm10,ymm11                    ;
         vpandn        ymm11,ymm2,ymm10                     ;
         vpxor         ymm11,ymm11,ymm8                     ;
         vmovdqa       ymmword ptr [r11+0a0h],ymm11         ;
         vpxor         ymm11,ymm4,ymmword ptr [r11+0160h]   ;
         vpsrlq        ymm12,ymm11,013h                     ;
         vpsllq        ymm11,ymm11,02dh                     ;
         vpor          ymm11,ymm11,ymm12                    ;
         vpandn        ymm12,ymm10,ymm11                    ;
         vpxor         ymm12,ymm12,ymm2                     ;
         vmovdqa       ymmword ptr [r11+0c0h],ymm12         ;
         vpsrlq        ymm12,ymm7,03h                       ;
         vpsllq        ymm7,ymm7,03dh                       ;
         vpor          ymm7,ymm7,ymm12                      ;
         vpandn        ymm12,ymm11,ymm7                     ;
         vpxor         ymm10,ymm12,ymm10                    ;
         vpandn        ymm12,ymm7,ymm8                      ;
         vpandn        ymm8,ymm8,ymm2                       ;
         vpsrlq        ymm2,ymm6,03fh                       ;
         vpsllq        ymm6,ymm6,01h                        ;
         vpxor         ymm14,ymm12,ymm11                    ;
         vpor          ymm6,ymm6,ymm2                       ;
         vpsrlq        ymm2,ymm9,03ah                       ;
         vpxor         ymm12,ymm8,ymm7                      ;
         vpsllq        ymm9,ymm9,06h                        ;
         vmovdqa       ymmword ptr [r11+0e0h],ymm12         ;
         vpxor         ymm7,ymm0,ymmword ptr [r11+01a0h]    ;
         vpor          ymm9,ymm9,ymm2                       ;
         vpxor         ymm2,ymm1,ymmword ptr [r11+0120h]    ;
         vpshufb       ymm7,ymm7,ymmword ptr [r8]          ;
         vpsrlq        ymm11,ymm2,027h                      ;
         vpsllq        ymm2,ymm2,019h                       ;
         vpor          ymm11,ymm11,ymm2                     ;
         vpandn        ymm2,ymm9,ymm11                      ;
         vpandn        ymm8,ymm11,ymm7                      ;
         vpxor         ymm12,ymm2,ymm6                      ;
         vpxor         ymm2,ymm3,ymmword ptr [r11+01c0h]    ;
         vpxor         ymm8,ymm8,ymm9                       ;
         vmovdqa       ymmword ptr [r11+0100h],ymm12        ;
         vpsrlq        ymm12,ymm2,02eh                      ;
         vpsllq        ymm2,ymm2,012h                       ;
         vpor          ymm2,ymm12,ymm2                      ;
         vpandn        ymm12,ymm7,ymm2                      ;
         vpxor         ymm15,ymm12,ymm11                    ;
         vpandn        ymm11,ymm2,ymm6                      ;
         vpandn        ymm6,ymm6,ymm9                       ;
         vpxor         ymm12,ymm11,ymm7                     ;
         vmovdqa       ymmword ptr [r11+0120h],ymm12        ;
         vpxor         ymm12,ymm6,ymm2                      ;
         vpxor         ymm6,ymm0,ymmword ptr [r11+02e0h]    ;
         vpxor         ymm0,ymm0,ymmword ptr [r11+02c0h]    ;
         vmovdqa       ymmword ptr [r11+0140h],ymm12        ;
         vpsrlq        ymm2,ymm6,025h                       ;
         vpsllq        ymm6,ymm6,01bh                       ;
         vpor          ymm2,ymm2,ymm6                       ;
         vpxor         ymm6,ymm3,ymmword ptr [r11+0220h]    ;
         vpxor         ymm3,ymm3,ymmword ptr [r11+0200h]    ;
         vpsrlq        ymm7,ymm6,01ch                       ;
         vpsllq        ymm6,ymm6,024h                       ;
         vpor          ymm7,ymm7,ymm6                       ;
         vpxor         ymm6,ymm4,ymmword ptr [r11+0260h]    ;
         vpxor         ymm4,ymm4,ymmword ptr [r11+0240h]    ;
         vpsrlq        ymm12,ymm6,036h                      ;
         vpsllq        ymm6,ymm6,0ah                        ;
         vpor          ymm12,ymm12,ymm6                     ;
         vpxor         ymm6,ymm5,ymmword ptr [r11+0180h]    ;
         vpxor         ymm5,ymm5,ymmword ptr [r11+0280h]    ;
         vpandn        ymm9,ymm7,ymm12                      ;
         vpsrlq        ymm11,ymm6,031h                      ;
         vpsllq        ymm6,ymm6,0fh                        ;
         vpxor         ymm9,ymm9,ymm2                       ;
         vpor          ymm11,ymm11,ymm6                     ;
         vpandn        ymm6,ymm12,ymm11                     ;
         vpxor         ymm6,ymm6,ymm7                       ;
         vmovdqa       ymmword ptr [r11+0160h],ymm6         ;
         vpxor         ymm6,ymm1,ymmword ptr [r11+01e0h]    ;
         vpxor         ymm1,ymm1,ymmword ptr [r11+02a0h]    ;
         vpshufb       ymm6,ymm6,ymmword ptr [r9]          ;
         vpandn        ymm13,ymm11,ymm6                     ;
         vpxor         ymm13,ymm13,ymm12                    ;
         vmovdqa       ymmword ptr [r11+0180h],ymm13        ;
         vpandn        ymm13,ymm6,ymm2                      ;
         vpandn        ymm2,ymm2,ymm7                       ;
         vpxor         ymm2,ymm2,ymm6                       ;
         vpsrlq        ymm6,ymm4,03eh                       ;
         vpxor         ymm13,ymm13,ymm11                    ;
         vmovdqa       ymmword ptr [r11+01a0h],ymm2         ;
         vpsrlq        ymm2,ymm5,02h                        ;
         vpsllq        ymm5,ymm5,03eh                       ;
         vpor          ymm2,ymm2,ymm5                       ;
         vpsrlq        ymm5,ymm1,09h                        ;
         vpsllq        ymm1,ymm1,037h                       ;
         vpsllq        ymm4,ymm4,02h                        ;
         vpor          ymm1,ymm5,ymm1                       ;
         vpsrlq        ymm5,ymm0,019h                       ;
         vpor          ymm4,ymm6,ymm4                       ;
         vpsllq        ymm0,ymm0,027h                       ;
         vpor          ymm5,ymm5,ymm0                       ;
         vpandn        ymm0,ymm1,ymm5                       ;
         vpxor         ymm0,ymm0,ymm2                       ;
         vmovdqa       ymmword ptr [r11+01c0h],ymm0         ;
         vpsrlq        ymm0,ymm3,017h                       ;
         vpsllq        ymm3,ymm3,029h                       ;
         vpor          ymm0,ymm0,ymm3                       ;
         vpandn        ymm7,ymm0,ymm4                       ;
         vpandn        ymm3,ymm5,ymm0                       ;
         vpxor         ymm7,ymm7,ymm5                       ;
         vpandn        ymm5,ymm4,ymm2                       ;
         vpandn        ymm2,ymm2,ymm1                       ;
         vpxor         ymm5,ymm5,ymm0                       ;
         vpxor         ymm3,ymm3,ymm1                       ;
         vpxor         ymm2,ymm2,ymm4                       ;
         vmovdqa       ymmword ptr [r11+01e0h],ymm5         ;
         add           rdx,08h                              ;
         add           r10,01h                              ;
         cmp           r10,018h                             ;
         jne           LLmld_keccak_f1600_x4_avx2_asm       ;
         vmovdqa       ymm4,ymmword ptr [r11]               ;
         vmovdqa       ymm5,ymmword ptr [r11+040h]          ;
         vmovdqa       ymm0,ymmword ptr [r11+020h]          ;
         vmovdqa       ymm1,ymmword ptr [r11+060h]          ;
         vmovdqa       ymm12,ymmword ptr [r11+01c0h]        ;
         vmovdqa       ymmword ptr [r11+01c0h],ymm2         ;
         vpunpcklqdq   ymm2,ymm4,ymm0                       ;
         vpunpckhqdq   ymm0,ymm4,ymm0                       ;
         vpunpcklqdq   ymm4,ymm5,ymm1                       ;
         vpunpckhqdq   ymm1,ymm5,ymm1                       ;
         vperm2i128    ymm6,ymm2,ymm4,020h                  ;
         vperm2i128    ymm2,ymm2,ymm4,031h                  ;
         vmovdqa       ymm4,ymmword ptr [r11+080h]          ;
         vperm2i128    ymm5,ymm0,ymm1,020h                  ;
         vperm2i128    ymm0,ymm0,ymm1,031h                  ;
         vmovdqu       ymmword ptr [rcx],ymm6               ;
         vmovdqu       ymmword ptr [rcx+0c8h],ymm5          ;
         vmovdqu       ymmword ptr [rcx+0190h],ymm2         ;
         vmovdqu       ymmword ptr [rcx+0258h],ymm0         ;
         vmovdqa       ymm0,ymmword ptr [r11+0a0h]          ;
         vpunpcklqdq   ymm2,ymm4,ymm0                       ;
         vpunpckhqdq   ymm1,ymm4,ymm0                       ;
         vmovdqa       ymm0,ymmword ptr [r11+0c0h]          ;
         vpunpcklqdq   ymm4,ymm0,ymm10                      ;
         vpunpckhqdq   ymm0,ymm0,ymm10                      ;
         vperm2i128    ymm6,ymm2,ymm4,020h                  ;
         vperm2i128    ymm5,ymm1,ymm0,020h                  ;
         vperm2i128    ymm2,ymm2,ymm4,031h                  ;
         vmovdqa       ymm4,ymmword ptr [r11+0e0h]          ;
         vperm2i128    ymm1,ymm1,ymm0,031h                  ;
         vmovdqa       ymm0,ymmword ptr [r11+0100h]         ;
         vmovdqu       ymmword ptr [rcx+01b0h],ymm2         ;
         vmovdqu       ymmword ptr [rcx+0278h],ymm1         ;
         vpunpcklqdq   ymm2,ymm14,ymm4                      ;
         vpunpckhqdq   ymm1,ymm14,ymm4                      ;
         vpunpcklqdq   ymm4,ymm0,ymm8                       ;
         vpunpckhqdq   ymm0,ymm0,ymm8                       ;
         vmovdqu       ymmword ptr [rcx+020h],ymm6          ;
         vmovdqu       ymmword ptr [rcx+0e8h],ymm5          ;
         vperm2i128    ymm6,ymm2,ymm4,020h                  ;
         vperm2i128    ymm5,ymm1,ymm0,020h                  ;
         vperm2i128    ymm2,ymm2,ymm4,031h                  ;
         vperm2i128    ymm1,ymm1,ymm0,031h                  ;
         vmovdqa       ymm4,ymmword ptr [r11+0120h]         ;
         vmovdqa       ymm0,ymmword ptr [r11+0140h]         ;
         vmovdqu       ymmword ptr [rcx+01d0h],ymm2         ;
         vmovdqu       ymmword ptr [rcx+0298h],ymm1         ;
         vpunpcklqdq   ymm2,ymm15,ymm4                      ;
         vpunpckhqdq   ymm1,ymm15,ymm4                      ;
         vpunpcklqdq   ymm4,ymm0,ymm9                       ;
         vmovdqu       ymmword ptr [rcx+0108h],ymm5         ;
         vpunpckhqdq   ymm0,ymm0,ymm9                       ;
         vmovdqu       ymmword ptr [rcx+040h],ymm6          ;
         vperm2i128    ymm6,ymm2,ymm4,020h                  ;
         vperm2i128    ymm2,ymm2,ymm4,031h                  ;
         vperm2i128    ymm5,ymm1,ymm0,020h                  ;
         vmovdqa       ymm4,ymmword ptr [r11+0160h]         ;
         vperm2i128    ymm1,ymm1,ymm0,031h                  ;
         vmovdqa       ymm0,ymmword ptr [r11+0180h]         ;
         vmovdqu       ymmword ptr [rcx+0128h],ymm5         ;
         vmovdqa       ymm5,ymmword ptr [r11+01a0h]         ;
         vmovdqu       ymmword ptr [rcx+01f0h],ymm2         ;
         vpunpcklqdq   ymm2,ymm4,ymm0                       ;
         vpunpckhqdq   ymm0,ymm4,ymm0                       ;
         vpunpcklqdq   ymm4,ymm13,ymm5                      ;
         vmovdqu       ymmword ptr [rcx+060h],ymm6          ;
         vperm2i128    ymm6,ymm2,ymm4,020h                  ;
         vmovdqu       ymmword ptr [rcx+02b8h],ymm1         ;
         vperm2i128    ymm2,ymm2,ymm4,031h                  ;
         vpunpckhqdq   ymm1,ymm13,ymm5                      ;
         vmovdqu       ymmword ptr [rcx+080h],ymm6          ;
         vmovdqa       ymm4,ymmword ptr [r11+01e0h]         ;
         vperm2i128    ymm5,ymm0,ymm1,020h                  ;
         vperm2i128    ymm0,ymm0,ymm1,031h                  ;
         vmovdqu       ymmword ptr [rcx+0210h],ymm2         ;
         vpunpcklqdq   ymm2,ymm12,ymm3                      ;
         vmovdqu       ymmword ptr [rcx+02d8h],ymm0         ;
         vpunpckhqdq   ymm0,ymm12,ymm3                      ;
         vpunpcklqdq   ymm3,ymm7,ymm4                       ;
         vpunpckhqdq   ymm1,ymm7,ymm4                       ;
         vmovdqu       ymmword ptr [rcx+0148h],ymm5         ;
         vperm2i128    ymm5,ymm2,ymm3,020h                  ;
         vperm2i128    ymm2,ymm2,ymm3,031h                  ;
         vmovdqa       ymm3,ymmword ptr [r11+01c0h]         ;
         vperm2i128    ymm4,ymm0,ymm1,020h                  ;
         vperm2i128    ymm0,ymm0,ymm1,031h                  ;
         vmovdqu       ymmword ptr [rcx+0a0h],ymm5          ;
         vextracti128  xmm15,ymm3,01h                       ;
         vmovdqu       ymmword ptr [rcx+0168h],ymm4         ;
         vmovdqu       ymmword ptr [rcx+0230h],ymm2         ;
         vmovdqu       ymmword ptr [rcx+02f8h],ymm0         ;
         vmovq         qword ptr [rcx+0c0h],xmm3            ;
         vmovhpd       qword ptr [rcx+0188h],xmm3           ;
         vmovq         qword ptr [rcx+0250h],xmm15          ;
         vmovhpd       qword ptr [rcx+0318h],xmm15          ;
         vzeroupper                                         ;

         vmovdqa       xmm6,xmmword ptr [rsp+0310h]         ;
         vmovdqa       xmm7,xmmword ptr [rsp+0320h]         ;
         vmovdqa       xmm8,xmmword ptr [rsp+0330h]         ;
         vmovdqa       xmm9,xmmword ptr [rsp+0340h]         ;
         vmovdqa       xmm10,xmmword ptr [rsp+0350h]        ;
         vmovdqa       xmm11,xmmword ptr [rsp+0360h]        ;
         vmovdqa       xmm12,xmmword ptr [rsp+0370h]        ;
         vmovdqa       xmm13,xmmword ptr [rsp+0380h]        ;
         vmovdqa       xmm14,xmmword ptr [rsp+0390h]        ;
         vmovdqa       xmm15,xmmword ptr [rsp+03A0h]        ;

         add           rsp,03B8h                            ; restore stack pointer
         ret                                                ;


FUNC_NAME ENDP

         END
