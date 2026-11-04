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
; Name: poly_tomont_aarch64_asm
; Description: Convert polynomial to Montgomery domain
; Signature: void mlk_poly_tomont_aarch64_asm(int16_t p[256])
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
FUNC_NAME SETS    "mlkem_poly_tomont_aarch64_asm"
        ENDIF

        AREA      |.drectve|, DRECTVE

        EXPORT    $FUNC_NAME

        AREA      |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN     16

$FUNC_NAME PROC

        ; .cfi_startproc
        mov       w2, #0xd01                              ; 0x00000000, line   20
        dup       v4.8h, w2                               ; 0x00000004, line   21
        mov       w2, #-0x414                             ; 0x00000008, line   22
        dup       v2.8h, w2                               ; 0x0000000C, line   23
        mov       w2, #-0x2824                            ; 0x00000010, line   24
        dup       v3.8h, w2                               ; 0x00000014, line   25
        mov       x1, #0x8                                ; 0x00000018, line   26
        ldr       q18, [x0, #0x20]                        ; 0x0000001C, line   27
        ldr       q0, [x0, #0x10]                         ; 0x00000020, line   28
        ldr       q16, [x0], #0x40                        ; 0x00000024, line   29
        sqrdmulh  v23.8h, v0.8h, v3.8h                    ; 0x00000028, line   30
        mul       v26.8h, v0.8h, v2.8h                    ; 0x0000002C, line   31
        sqrdmulh  v19.8h, v16.8h, v3.8h                   ; 0x00000030, line   32
        mls       v26.8h, v23.8h, v4.h[0]                 ; 0x00000034, line   33
        mul       v29.8h, v16.8h, v2.8h                   ; 0x00000038, line   34
        ldur      q16, [x0, #-0x10]                       ; 0x0000003C, line   35
        mls       v29.8h, v19.8h, v4.h[0]                 ; 0x00000040, line   36
        stur      q26, [x0, #-0x30]                       ; 0x00000044, line   37
        sqrdmulh  v26.8h, v18.8h, v3.8h                   ; 0x00000048, line   38
        mul       v18.8h, v18.8h, v2.8h                   ; 0x0000004C, line   39
        stur      q29, [x0, #-0x40]                       ; 0x00000050, line   40
        sqrdmulh  v29.8h, v16.8h, v3.8h                   ; 0x00000054, line   41
        mls       v18.8h, v26.8h, v4.h[0]                 ; 0x00000058, line   42
        sub       x1, x1, #0x1                            ; 0x0000005C, line   43

Lmlk_poly_tomont_loop

        ldr       q19, [x0, #0x10]                        ; 0x00000060, line   46
        mul       v26.8h, v16.8h, v2.8h                   ; 0x00000064, line   47
        ldr       q23, [x0, #0x20]                        ; 0x00000068, line   48
        ldr       q17, [x0], #0x40                        ; 0x0000006C, line   49
        mls       v26.8h, v29.8h, v4.h[0]                 ; 0x00000070, line   50
        ldur      q16, [x0, #-0x10]                       ; 0x00000074, line   51
        sqrdmulh  v28.8h, v19.8h, v3.8h                   ; 0x00000078, line   52
        stur      q18, [x0, #-0x60]                       ; 0x0000007C, line   53
        mul       v0.8h, v19.8h, v2.8h                    ; 0x00000080, line   54
        stur      q26, [x0, #-0x50]                       ; 0x00000084, line   55
        sqrdmulh  v24.8h, v23.8h, v3.8h                   ; 0x00000088, line   56
        mul       v18.8h, v23.8h, v2.8h                   ; 0x0000008C, line   57
        sqrdmulh  v22.8h, v17.8h, v3.8h                   ; 0x00000090, line   58
        mul       v26.8h, v17.8h, v2.8h                   ; 0x00000094, line   59
        mls       v0.8h, v28.8h, v4.h[0]                  ; 0x00000098, line   60
        mls       v26.8h, v22.8h, v4.h[0]                 ; 0x0000009C, line   61
        sqrdmulh  v29.8h, v16.8h, v3.8h                   ; 0x000000A0, line   62
        stur      q0, [x0, #-0x30]                        ; 0x000000A4, line   63
        mls       v18.8h, v24.8h, v4.h[0]                 ; 0x000000A8, line   64
        stur      q26, [x0, #-0x40]                       ; 0x000000AC, line   65
        sub       x1, x1, #0x1                            ; 0x000000B0, line   66
        cbnz      x1, Lmlk_poly_tomont_loop               ; 0x000000B4, line   67
        mul       v16.8h, v16.8h, v2.8h                   ; 0x000000B8, line   68
        stur      q18, [x0, #-0x20]                       ; 0x000000BC, line   69
        mls       v16.8h, v29.8h, v4.h[0]                 ; 0x000000C0, line   70
        stur      q16, [x0, #-0x10]                       ; 0x000000C4, line   71
        ret                                               ; 0x000000C8, line   72
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x000000CC byte(s)

        END
