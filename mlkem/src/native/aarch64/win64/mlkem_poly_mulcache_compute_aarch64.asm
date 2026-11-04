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
; Name: poly_mulcache_compute_aarch64_asm
; Description: Compute multiplication cache for polynomial
; Signature: void mlk_poly_mulcache_compute_aarch64_asm(int16_t cache[128], const int16_t mlk_poly[256], const int16_t zetas[128], const int16_t zetas_twisted[128])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON]
;   x0:
;     type: buffer
;     size_bytes: 256
;     permissions: write-only
;     c_parameter: int16_t cache[128]
;     description: Output cache
;   x1:
;     type: buffer
;     size_bytes: 512
;     permissions: read-only
;     c_parameter: const int16_t mlk_poly[256]
;     description: Input polynomial
;   x2:
;     type: buffer
;     size_bytes: 256
;     permissions: read-only
;     c_parameter: const int16_t zetas[128]
;     description: Zeta values
;   x3:
;     type: buffer
;     size_bytes: 256
;     permissions: read-only
;     c_parameter: const int16_t zetas_twisted[128]
;     description: Twisted zeta values
; Stack:
;   bytes: 0
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_poly_mulcache_compute_aarch64_asm"
        ENDIF

        AREA      |.drectve|, DRECTVE

        EXPORT    $FUNC_NAME

        AREA      |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN     16

$FUNC_NAME PROC

        ; .cfi_startproc
        mov       w5, #0xd01                                ; 0x00000000, line   38
        dup       v6.8h, w5                                 ; 0x00000004, line   39
        mov       w5, #0x4ebf                               ; 0x00000008, line   40
        dup       v7.8h, w5                                 ; 0x0000000C, line   41
        mov       x4, #0x10                                 ; 0x00000010, line   42
        ldr       q0, [x1], #0x20                           ; 0x00000014, line   43
        ldur      q2, [x1, #-0x10]                          ; 0x00000018, line   44
        ldr       q19, [x1], #0x20                          ; 0x0000001C, line   45
        ldr       q29, [x3], #0x10                          ; 0x00000020, line   46
        ldur      q16, [x1, #-0x10]                         ; 0x00000024, line   47
        ldr       q18, [x2], #0x10                          ; 0x00000028, line   48
        ldr       q26, [x1], #0x20                          ; 0x0000002C, line   49
        ldr       q25, [x2], #0x10                          ; 0x00000030, line   50
        uzp2      v5.8h, v0.8h, v2.8h                       ; 0x00000034, line   51
        ldr       q28, [x3], #0x10                          ; 0x00000038, line   52
        ldur      q7, [x1, #-0x10]                          ; 0x0000003C, line   53
        ldr       q2, [x1], #0x20                           ; 0x00000040, line   54
        uzp2      v27.8h, v19.8h, v16.8h                    ; 0x00000044, line   55
        sqrdmulh  v16.8h, v5.8h, v29.8h                     ; 0x00000048, line   56
        ldr       q17, [x3], #0x10                          ; 0x0000004C, line   57
        ldr       q19, [x3], #0x10                          ; 0x00000050, line   58
        mul       v5.8h, v5.8h, v18.8h                      ; 0x00000054, line   59
        uzp2      v29.8h, v26.8h, v7.8h                     ; 0x00000058, line   60
        mul       v26.8h, v27.8h, v25.8h                    ; 0x0000005C, line   61
        sqrdmulh  v4.8h, v27.8h, v28.8h                     ; 0x00000060, line   62
        mls       v5.8h, v16.8h, v6.h[0]                    ; 0x00000064, line   63
        lsr       x4, x4, #1                                ; 0x00000068, line   64
        sub       x4, x4, #0x2                              ; 0x0000006C, line   65

Lmlk_poly_mulcache_compute_loop_start

        str       q5, [x0], #0x10                           ; 0x00000070, line   68
        sqrdmulh  v22.8h, v29.8h, v17.8h                    ; 0x00000074, line   69
        ldr       q28, [x2], #0x10                          ; 0x00000078, line   70
        ldur      q24, [x1, #-0x10]                         ; 0x0000007C, line   71
        ldr       q0, [x1], #0x20                           ; 0x00000080, line   72
        mls       v26.8h, v4.8h, v6.h[0]                    ; 0x00000084, line   73
        ldur      q16, [x1, #-0x10]                         ; 0x00000088, line   74
        ldr       q17, [x3], #0x10                          ; 0x0000008C, line   75
        mul       v5.8h, v29.8h, v28.8h                     ; 0x00000090, line   76
        uzp2      v23.8h, v2.8h, v24.8h                     ; 0x00000094, line   77
        ldr       q18, [x2], #0x10                          ; 0x00000098, line   78
        mls       v5.8h, v22.8h, v6.h[0]                    ; 0x0000009C, line   79
        uzp2      v29.8h, v0.8h, v16.8h                     ; 0x000000A0, line   80
        sqrdmulh  v4.8h, v23.8h, v19.8h                     ; 0x000000A4, line   81
        ldr       q2, [x1], #0x20                           ; 0x000000A8, line   82
        ldr       q19, [x3], #0x10                          ; 0x000000AC, line   83
        str       q26, [x0], #0x10                          ; 0x000000B0, line   84
        mul       v26.8h, v23.8h, v18.8h                    ; 0x000000B4, line   85
        subs      x4, x4, #0x1                              ; 0x000000B8, line   86
        cbnz      x4, Lmlk_poly_mulcache_compute_loop_start ; 0x000000BC, line   87
        mls       v26.8h, v4.8h, v6.h[0]                    ; 0x000000C0, line   88
        str       q5, [x0], #0x10                           ; 0x000000C4, line   89
        ldr       q5, [x2], #0x10                           ; 0x000000C8, line   90
        ldur      q4, [x1, #-0x10]                          ; 0x000000CC, line   91
        sqrdmulh  v16.8h, v29.8h, v17.8h                    ; 0x000000D0, line   92
        ldr       q0, [x2], #0x10                           ; 0x000000D4, line   93
        mul       v29.8h, v29.8h, v5.8h                     ; 0x000000D8, line   94
        uzp2      v18.8h, v2.8h, v4.8h                      ; 0x000000DC, line   95
        str       q26, [x0], #0x10                          ; 0x000000E0, line   96
        sqrdmulh  v17.8h, v18.8h, v19.8h                    ; 0x000000E4, line   97
        mls       v29.8h, v16.8h, v6.h[0]                   ; 0x000000E8, line   98
        mul       v26.8h, v18.8h, v0.8h                     ; 0x000000EC, line   99
        mls       v26.8h, v17.8h, v6.h[0]                   ; 0x000000F0, line  100
        str       q29, [x0], #0x10                          ; 0x000000F4, line  101
        str       q26, [x0], #0x10                          ; 0x000000F8, line  102
        ret                                                 ; 0x000000FC, line  103
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000100 byte(s)

        END
