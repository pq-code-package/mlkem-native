;
; Copyright (c) 2022 Arm Limited
; Copyright(c) 2022 Hanno Becker
; Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
; Copyright (c) The mlkem-native project authors
; Copyright (c) The mldsa-native project authors
; SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
;

;  References
;  ==========
;
;  - [NeonNTT]
;    Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1
;    Becker, Hwang, Kannwischer, Yang, Yang
;    https://eprint.iacr.org/2021/986
;
;  - [NeonNTT_Autoformalised]
;    Neon NTT - (Auto)formalised
;    Hanno Becker
;    https://eprint.iacr.org/2026/1223
;
;  - [SLOTHY_Paper]
;    Fast and Clean: Auditable high-performance assembly via constraint solving
;    Abdulrahman, Becker, Kannwischer, Klein
;    https://eprint.iacr.org/2022/1303
;
; Windows ARM64 port:
; 'armasm64.exe' re-formatting and SEH unwind information provided by
; Ingo A. Kubbilun <ingo.kubbilun@gmail.com>, Oct. 2026
;

; yaml
; Name: poly_reduce_aarch64_asm
; Description: Barrett reduction of polynomial coefficients
; Signature: void mlk_poly_reduce_aarch64_asm(int16_t p[256])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON]
;   x0:
;     type: buffer
;     size_bytes: 512
;     permissions: read/write
;     c_parameter: int16_t p[256]
;     description: Input/output polynomial
; Stack:
;   bytes: 0
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_poly_reduce_aarch64_asm"
        ENDIF

        AREA     |.drectve|, DRECTVE

        EXPORT   $FUNC_NAME

        AREA     |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN    16

$FUNC_NAME PROC

        ; .cfi_startproc
        mov      w2, #0xd01                              ; 0x00000000, line   20
        dup      v3.8h, w2                               ; 0x00000004, line   21
        mov      w2, #0x4ebf                             ; 0x00000008, line   22
        dup      v4.8h, w2                               ; 0x0000000C, line   23
        mov      x1, #0x8                                ; 0x00000010, line   24
        ldr      q21, [x0], #0x40                        ; 0x00000014, line   25
        ldur     q18, [x0, #-0x20]                       ; 0x00000018, line   26
        ldur     q0, [x0, #-0x30]                        ; 0x0000001C, line   27
        ldur     q5, [x0, #-0x10]                        ; 0x00000020, line   28
        ldr      q26, [x0], #0x40                        ; 0x00000024, line   29
        sqdmulh  v17.8h, v21.8h, v4.h[0]                 ; 0x00000028, line   30
        sqdmulh  v27.8h, v18.8h, v4.h[0]                 ; 0x0000002C, line   31
        sqdmulh  v22.8h, v0.8h, v4.h[0]                  ; 0x00000030, line   32
        srshr    v17.8h, v17.8h, #0xb                    ; 0x00000034, line   33
        sqdmulh  v23.8h, v5.8h, v4.h[0]                  ; 0x00000038, line   34
        srshr    v29.8h, v27.8h, #0xb                    ; 0x0000003C, line   35
        mls      v21.8h, v17.8h, v3.h[0]                 ; 0x00000040, line   36
        srshr    v17.8h, v22.8h, #0xb                    ; 0x00000044, line   37
        mls      v18.8h, v29.8h, v3.h[0]                 ; 0x00000048, line   38
        srshr    v22.8h, v23.8h, #0xb                    ; 0x0000004C, line   39
        mls      v0.8h, v17.8h, v3.h[0]                  ; 0x00000050, line   40
        sshr     v2.8h, v21.8h, #0xf                     ; 0x00000054, line   41
        mls      v5.8h, v22.8h, v3.h[0]                  ; 0x00000058, line   42
        sshr     v29.8h, v18.8h, #0xf                    ; 0x0000005C, line   43
        and      v19.16b, v3.16b, v2.16b                 ; 0x00000060, line   44
        sqdmulh  v2.8h, v26.8h, v4.h[0]                  ; 0x00000064, line   45
        sshr     v31.8h, v0.8h, #0xf                     ; 0x00000068, line   46
        add      v17.8h, v21.8h, v19.8h                  ; 0x0000006C, line   47
        and      v21.16b, v3.16b, v29.16b                ; 0x00000070, line   48
        and      v31.16b, v3.16b, v31.16b                ; 0x00000074, line   49
        sub      x1, x1, #0x2                            ; 0x00000078, line   50
        HINT     #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_poly_reduce_loop_start

        add      v21.8h, v18.8h, v21.8h                  ; 0x00000080, line   53
        ldur     q18, [x0, #-0x20]                       ; 0x00000084, line   54
        add      v25.8h, v0.8h, v31.8h                   ; 0x00000088, line   55
        ldur     q0, [x0, #-0x30]                        ; 0x0000008C, line   56
        stur     q21, [x0, #-0x60]                       ; 0x00000090, line   57
        sshr     v28.8h, v5.8h, #0xf                     ; 0x00000094, line   58
        stur     q17, [x0, #-0x80]                       ; 0x00000098, line   59
        srshr    v23.8h, v2.8h, #0xb                     ; 0x0000009C, line   60
        sqdmulh  v30.8h, v18.8h, v4.h[0]                 ; 0x000000A0, line   61
        stur     q25, [x0, #-0x70]                       ; 0x000000A4, line   62
        and      v22.16b, v3.16b, v28.16b                ; 0x000000A8, line   63
        sqdmulh  v7.8h, v0.8h, v4.h[0]                   ; 0x000000AC, line   64
        add      v16.8h, v5.8h, v22.8h                   ; 0x000000B0, line   65
        ldur     q5, [x0, #-0x10]                        ; 0x000000B4, line   66
        mls      v26.8h, v23.8h, v3.h[0]                 ; 0x000000B8, line   67
        stur     q16, [x0, #-0x50]                       ; 0x000000BC, line   68
        srshr    v6.8h, v30.8h, #0xb                     ; 0x000000C0, line   69
        srshr    v1.8h, v7.8h, #0xb                      ; 0x000000C4, line   70
        sqdmulh  v19.8h, v5.8h, v4.h[0]                  ; 0x000000C8, line   71
        mls      v18.8h, v6.8h, v3.h[0]                  ; 0x000000CC, line   72
        sshr     v24.8h, v26.8h, #0xf                    ; 0x000000D0, line   73
        mls      v0.8h, v1.8h, v3.h[0]                   ; 0x000000D4, line   74
        and      v27.16b, v3.16b, v24.16b                ; 0x000000D8, line   75
        srshr    v29.8h, v19.8h, #0xb                    ; 0x000000DC, line   76
        add      v17.8h, v26.8h, v27.8h                  ; 0x000000E0, line   77
        ldr      q26, [x0], #0x40                        ; 0x000000E4, line   78
        sshr     v1.8h, v18.8h, #0xf                     ; 0x000000E8, line   79
        mls      v5.8h, v29.8h, v3.h[0]                  ; 0x000000EC, line   80
        sshr     v20.8h, v0.8h, #0xf                     ; 0x000000F0, line   81
        and      v21.16b, v3.16b, v1.16b                 ; 0x000000F4, line   82
        and      v31.16b, v3.16b, v20.16b                ; 0x000000F8, line   83
        sqdmulh  v2.8h, v26.8h, v4.h[0]                  ; 0x000000FC, line   84
        subs     x1, x1, #0x1                            ; 0x00000100, line   85
        cbnz     x1, Lmlk_poly_reduce_loop_start         ; 0x00000104, line   86
        add      v28.8h, v0.8h, v31.8h                   ; 0x00000108, line   87
        ldur     q29, [x0, #-0x10]                       ; 0x0000010C, line   88
        add      v21.8h, v18.8h, v21.8h                  ; 0x00000110, line   89
        srshr    v18.8h, v2.8h, #0xb                     ; 0x00000114, line   90
        sshr     v2.8h, v5.8h, #0xf                      ; 0x00000118, line   91
        ldur     q16, [x0, #-0x20]                       ; 0x0000011C, line   92
        stur     q17, [x0, #-0x80]                       ; 0x00000120, line   93
        ldur     q0, [x0, #-0x30]                        ; 0x00000124, line   94
        and      v2.16b, v3.16b, v2.16b                  ; 0x00000128, line   95
        sqdmulh  v24.8h, v29.8h, v4.h[0]                 ; 0x0000012C, line   96
        stur     q28, [x0, #-0x70]                       ; 0x00000130, line   97
        stur     q21, [x0, #-0x60]                       ; 0x00000134, line   98
        add      v31.8h, v5.8h, v2.8h                    ; 0x00000138, line   99
        sqdmulh  v6.8h, v16.8h, v4.h[0]                  ; 0x0000013C, line  100
        stur     q31, [x0, #-0x50]                       ; 0x00000140, line  101
        sqdmulh  v17.8h, v0.8h, v4.h[0]                  ; 0x00000144, line  102
        srshr    v22.8h, v24.8h, #0xb                    ; 0x00000148, line  103
        mls      v26.8h, v18.8h, v3.h[0]                 ; 0x0000014C, line  104
        srshr    v31.8h, v6.8h, #0xb                     ; 0x00000150, line  105
        mls      v29.8h, v22.8h, v3.h[0]                 ; 0x00000154, line  106
        srshr    v19.8h, v17.8h, #0xb                    ; 0x00000158, line  107
        mls      v16.8h, v31.8h, v3.h[0]                 ; 0x0000015C, line  108
        sshr     v7.8h, v26.8h, #0xf                     ; 0x00000160, line  109
        mls      v0.8h, v19.8h, v3.h[0]                  ; 0x00000164, line  110
        and      v5.16b, v3.16b, v7.16b                  ; 0x00000168, line  111
        sshr     v22.8h, v29.8h, #0xf                    ; 0x0000016C, line  112
        add      v27.8h, v26.8h, v5.8h                   ; 0x00000170, line  113
        and      v26.16b, v3.16b, v22.16b                ; 0x00000174, line  114
        sshr     v20.8h, v16.8h, #0xf                    ; 0x00000178, line  115
        stur     q27, [x0, #-0x40]                       ; 0x0000017C, line  116
        and      v2.16b, v3.16b, v20.16b                 ; 0x00000180, line  117
        sshr     v23.8h, v0.8h, #0xf                     ; 0x00000184, line  118
        add      v18.8h, v29.8h, v26.8h                  ; 0x00000188, line  119
        add      v31.8h, v16.8h, v2.8h                   ; 0x0000018C, line  120
        and      v29.16b, v3.16b, v23.16b                ; 0x00000190, line  121
        stur     q18, [x0, #-0x10]                       ; 0x00000194, line  122
        add      v25.8h, v0.8h, v29.8h                   ; 0x00000198, line  123
        stur     q31, [x0, #-0x20]                       ; 0x0000019C, line  124
        stur     q25, [x0, #-0x30]                       ; 0x000001A0, line  125
        ret                                              ; 0x000001A4, line  126
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x000001A8 byte(s)

        END
