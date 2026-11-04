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
; Name: poly_tobytes_aarch64_asm
; Description: Convert polynomial to byte representation
; Signature: void mlk_poly_tobytes_aarch64_asm(uint8_t r[384], const int16_t a[256])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON]
;   x0:
;     type: buffer
;     size_bytes: 384
;     permissions: write-only
;     c_parameter: uint8_t r[384]
;     description: Output byte array
;   x1:
;     type: buffer
;     size_bytes: 512
;     permissions: read-only
;     c_parameter: const int16_t a[256]
;     description: Input polynomial
; Stack:
;   bytes: 0
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_poly_tobytes_aarch64_asm"
        ENDIF

        AREA    |.drectve|, DRECTVE

        EXPORT  $FUNC_NAME

        AREA    |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN   16

$FUNC_NAME PROC

        ; .cfi_startproc
        mov     x2, #0x10                               ; 0x00000000, line   26
        ldr     q5, [x1, #0x10]                         ; 0x00000004, line   27
        ldr     q3, [x1], #0x20                         ; 0x00000008, line   28
        ldr     q29, [x1], #0x20                        ; 0x0000000C, line   29
        ldur    q2, [x1, #-0x10]                        ; 0x00000010, line   30
        ldr     q27, [x1, #0x10]                        ; 0x00000014, line   31
        ldr     q23, [x1, #0x30]                        ; 0x00000018, line   32
        ldr     q17, [x1], #0x20                        ; 0x0000001C, line   33
        ldr     q16, [x1], #0x20                        ; 0x00000020, line   34
        uzp2    v26.8h, v3.8h, v5.8h                    ; 0x00000024, line   35
        uzp1    v19.8h, v3.8h, v5.8h                    ; 0x00000028, line   36
        uzp2    v0.8h, v29.8h, v2.8h                    ; 0x0000002C, line   37
        uzp1    v1.8h, v29.8h, v2.8h                    ; 0x00000030, line   38
        xtn     v5.8b, v26.8h                           ; 0x00000034, line   39
        shrn    v3.8b, v19.8h, #0x8                     ; 0x00000038, line   40
        shrn    v4.8b, v26.8h, #0x4                     ; 0x0000003C, line   41
        xtn     v18.8b, v0.8h                           ; 0x00000040, line   42
        shrn    v30.8b, v0.8h, #0x4                     ; 0x00000044, line   43
        xtn     v28.8b, v1.8h                           ; 0x00000048, line   44
        shrn    v29.8b, v1.8h, #0x8                     ; 0x0000004C, line   45
        sli     v3.8b, v5.8b, #0x4                      ; 0x00000050, line   46
        xtn     v2.8b, v19.8h                           ; 0x00000054, line   47
        sli     v29.8b, v18.8b, #0x4                    ; 0x00000058, line   48
        lsr     x2, x2, #1                              ; 0x0000005C, line   49
        sub     x2, x2, #0x2                            ; 0x00000060, line   50
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_poly_tobytes_loop_start

        uzp1    v25.8h, v17.8h, v27.8h                  ; 0x00000070, line   53
        uzp2    v31.8h, v17.8h, v27.8h                  ; 0x00000074, line   54
        uzp1    v24.8h, v16.8h, v23.8h                  ; 0x00000078, line   55
        uzp2    v6.8h, v16.8h, v23.8h                   ; 0x0000007C, line   56
        st3     { v2.8b, v3.8b, v4.8b }, [x0], #24      ; 0x00000080, line   57
        shrn    v3.8b, v25.8h, #0x8                     ; 0x00000084, line   58
        ldr     q17, [x1], #0x20                        ; 0x00000088, line   59
        shrn    v4.8b, v31.8h, #0x4                     ; 0x0000008C, line   60
        xtn     v21.8b, v6.8h                           ; 0x00000090, line   61
        ldr     q23, [x1, #0x10]                        ; 0x00000094, line   62
        st3     { v28.8b, v29.8b, v30.8b }, [x0], #24   ; 0x00000098, line   63
        shrn    v29.8b, v24.8h, #0x8                    ; 0x0000009C, line   64
        ldur    q27, [x1, #-0x10]                       ; 0x000000A0, line   65
        xtn     v20.8b, v31.8h                          ; 0x000000A4, line   66
        ldr     q16, [x1], #0x20                        ; 0x000000A8, line   67
        sli     v29.8b, v21.8b, #0x4                    ; 0x000000AC, line   68
        xtn     v2.8b, v25.8h                           ; 0x000000B0, line   69
        sli     v3.8b, v20.8b, #0x4                     ; 0x000000B4, line   70
        xtn     v28.8b, v24.8h                          ; 0x000000B8, line   71
        shrn    v30.8b, v6.8h, #0x4                     ; 0x000000BC, line   72
        subs    x2, x2, #0x1                            ; 0x000000C0, line   73
        cbnz    x2, Lmlk_poly_tobytes_loop_start        ; 0x000000C4, line   74
        uzp2    v7.8h, v17.8h, v27.8h                   ; 0x000000C8, line   75
        uzp1    v25.8h, v17.8h, v27.8h                  ; 0x000000CC, line   76
        uzp2    v0.8h, v16.8h, v23.8h                   ; 0x000000D0, line   77
        st3     { v2.8b, v3.8b, v4.8b }, [x0], #24      ; 0x000000D4, line   78
        st3     { v28.8b, v29.8b, v30.8b }, [x0], #24   ; 0x000000D8, line   79
        shrn    v21.8b, v25.8h, #0x8                    ; 0x000000DC, line   80
        uzp1    v2.8h, v16.8h, v23.8h                   ; 0x000000E0, line   81
        shrn    v22.8b, v7.8h, #0x4                     ; 0x000000E4, line   82
        shrn    v4.8b, v0.8h, #0x4                      ; 0x000000E8, line   83
        xtn     v28.8b, v7.8h                           ; 0x000000EC, line   84
        xtn     v27.8b, v0.8h                           ; 0x000000F0, line   85
        shrn    v3.8b, v2.8h, #0x8                      ; 0x000000F4, line   86
        sli     v21.8b, v28.8b, #0x4                    ; 0x000000F8, line   87
        xtn     v2.8b, v2.8h                            ; 0x000000FC, line   88
        sli     v3.8b, v27.8b, #0x4                     ; 0x00000100, line   89
        xtn     v20.8b, v25.8h                          ; 0x00000104, line   90
        st3     { v20.8b, v21.8b, v22.8b }, [x0], #24   ; 0x00000108, line   91
        st3     { v2.8b, v3.8b, v4.8b }, [x0], #24      ; 0x0000010C, line   92
        ret                                             ; 0x00000110, line   93
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000114 byte(s)

        END
