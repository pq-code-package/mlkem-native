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
; Name: rej_uniform_aarch64_asm
; Description: Run rejection sampling on uniform random bytes to generate uniform random integers mod q
; Signature: uint64_t mlk_rej_uniform_aarch64_asm(int16_t r[256], const uint8_t *buf, uint64_t buflen, const uint8_t table[4096])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON]
;   x0:
;     type: buffer
;     size_bytes: 512
;     permissions: write-only
;     c_parameter: int16_t r[256]
;     description: Output buffer
;   x1:
;     type: buffer
;     size_bytes: x2
;     permissions: read-only
;     c_parameter: const uint8_t *buf
;     description: Input buffer
;   x2:
;     type: scalar
;     c_parameter: uint64_t buflen
;     description: Length of input buffer (must be multiple of 24)
;     test_with: 504  # MLKEM_GEN_MATRIX_NBLOCKS * MLK_XOF_RATE
;   x3:
;     type: buffer
;     size_bytes: 4096
;     permissions: read-only
;     c_parameter: const uint8_t table[4096]
;     description: Lookup table
; Stack:
;   bytes: 576
;   description: register preservation and temporary storage
;

         IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_rej_uniform_aarch64_asm"
        ENDIF

       AREA    |.drectve|, DRECTVE

        EXPORT  $FUNC_NAME

        AREA    |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN   16

$FUNC_NAME PROC

        ; .cfi_startproc
        sub     sp, sp, #0x240                          ; 0x00000000, line   38
        ; .cfi_adjust_cfa_offset 0x240
        mov     x7, #0x1                                ; 0x00000004, line   40
        movk    x7, #0x2, lsl #16                       ; 0x00000008, line   41
        movk    x7, #0x4, lsl #32                       ; 0x0000000C, line   42
        movk    x7, #0x8, lsl #48                       ; 0x00000010, line   43
        mov     v31.d[0], x7                            ; 0x00000014, line   44
        mov     x7, #0x10                               ; 0x00000018, line   45
        movk    x7, #0x20, lsl #16                      ; 0x0000001C, line   46
        movk    x7, #0x40, lsl #32                      ; 0x00000020, line   47
        movk    x7, #0x80, lsl #48                      ; 0x00000024, line   48
        mov     v31.d[1], x7                            ; 0x00000028, line   49
        mov     w11, #0xd01                             ; 0x0000002C, line   50
        dup     v30.8h, w11                             ; 0x00000030, line   51
        mov     x8, sp                                  ; 0x00000034, line   52
        mov     x7, x8                                  ; 0x00000038, line   53
        mov     x11, #0x0                               ; 0x0000003C, line   54
        eor     v16.16b, v16.16b, v16.16b               ; 0x00000040, line   55
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_rej_uniform_initial_zero

        str     q16, [x7], #0x40                        ; 0x00000050, line   58
        stur    q16, [x7, #-0x30]                       ; 0x00000054, line   59
        stur    q16, [x7, #-0x20]                       ; 0x00000058, line   60
        stur    q16, [x7, #-0x10]                       ; 0x0000005C, line   61
        add     x11, x11, #0x20                         ; 0x00000060, line   62
        cmp     x11, #0x100                             ; 0x00000064, line   63
        b.lt    Lmlk_rej_uniform_initial_zero           ; 0x00000068, line   64
        mov     x7, x8                                  ; 0x0000006C, line   65
        mov     x9, #0x0                                ; 0x00000070, line   66
        mov     x4, #0x100                              ; 0x00000074, line   67
        cmp     x2, #0x30                               ; 0x00000078, line   68
        b.lo    Lmlk_rej_uniform_loop48_end             ; 0x0000007C, line   69

Lmlk_rej_uniform_loop48

        cmp     x9, x4                                  ; 0x00000080, line   72
        b.hs    Lmlk_rej_uniform_memory_copy            ; 0x00000084, line   73
        sub     x2, x2, #0x30                           ; 0x00000088, line   74
        ld3     { v0.16b, v1.16b, v2.16b }, [x1], #48   ; 0x0000008C, line   75
        zip1    v4.16b, v0.16b, v1.16b                  ; 0x00000090, line   76
        zip2    v5.16b, v0.16b, v1.16b                  ; 0x00000094, line   77
        zip1    v6.16b, v1.16b, v2.16b                  ; 0x00000098, line   78
        zip2    v7.16b, v1.16b, v2.16b                  ; 0x0000009C, line   79
        bic     v4.8h, #0xf0, lsl #8                    ; 0x000000A0, line   80
        bic     v5.8h, #0xf0, lsl #8                    ; 0x000000A4, line   81
        ushr    v6.8h, v6.8h, #0x4                      ; 0x000000A8, line   82
        ushr    v7.8h, v7.8h, #0x4                      ; 0x000000AC, line   83
        zip1    v16.8h, v4.8h, v6.8h                    ; 0x000000B0, line   84
        zip2    v17.8h, v4.8h, v6.8h                    ; 0x000000B4, line   85
        zip1    v18.8h, v5.8h, v7.8h                    ; 0x000000B8, line   86
        zip2    v19.8h, v5.8h, v7.8h                    ; 0x000000BC, line   87
        cmhi    v4.8h, v30.8h, v16.8h                   ; 0x000000C0, line   88
        cmhi    v5.8h, v30.8h, v17.8h                   ; 0x000000C4, line   89
        cmhi    v6.8h, v30.8h, v18.8h                   ; 0x000000C8, line   90
        cmhi    v7.8h, v30.8h, v19.8h                   ; 0x000000CC, line   91
        and     v4.16b, v4.16b, v31.16b                 ; 0x000000D0, line   92
        and     v5.16b, v5.16b, v31.16b                 ; 0x000000D4, line   93
        and     v6.16b, v6.16b, v31.16b                 ; 0x000000D8, line   94
        and     v7.16b, v7.16b, v31.16b                 ; 0x000000DC, line   95
        uaddlv  s20, v4.8h                              ; 0x000000E0, line   96
        uaddlv  s21, v5.8h                              ; 0x000000E4, line   97
        uaddlv  s22, v6.8h                              ; 0x000000E8, line   98
        uaddlv  s23, v7.8h                              ; 0x000000EC, line   99
        fmov    w12, s20                                ; 0x000000F0, line  100
        fmov    w13, s21                                ; 0x000000F4, line  101
        fmov    w14, s22                                ; 0x000000F8, line  102
        fmov    w15, s23                                ; 0x000000FC, line  103
        ldr     q24, [x3, x12, lsl #4]                  ; 0x00000100, line  104
        ldr     q25, [x3, x13, lsl #4]                  ; 0x00000104, line  105
        ldr     q26, [x3, x14, lsl #4]                  ; 0x00000108, line  106
        ldr     q27, [x3, x15, lsl #4]                  ; 0x0000010C, line  107
        cnt     v4.16b, v4.16b                          ; 0x00000110, line  108
        cnt     v5.16b, v5.16b                          ; 0x00000114, line  109
        cnt     v6.16b, v6.16b                          ; 0x00000118, line  110
        cnt     v7.16b, v7.16b                          ; 0x0000011C, line  111
        uaddlv  s20, v4.8h                              ; 0x00000120, line  112
        uaddlv  s21, v5.8h                              ; 0x00000124, line  113
        uaddlv  s22, v6.8h                              ; 0x00000128, line  114
        uaddlv  s23, v7.8h                              ; 0x0000012C, line  115
        fmov    w12, s20                                ; 0x00000130, line  116
        fmov    w13, s21                                ; 0x00000134, line  117
        fmov    w14, s22                                ; 0x00000138, line  118
        fmov    w15, s23                                ; 0x0000013C, line  119
        tbl     v16.16b, { v16.16b }, v24.16b           ; 0x00000140, line  120
        tbl     v17.16b, { v17.16b }, v25.16b           ; 0x00000144, line  121
        tbl     v18.16b, { v18.16b }, v26.16b           ; 0x00000148, line  122
        tbl     v19.16b, { v19.16b }, v27.16b           ; 0x0000014C, line  123
        st1     { v16.8h }, [x7]                        ; 0x00000150, line  124
        add     x7, x7, x12, lsl #1                     ; 0x00000154, line  125
        st1     { v17.8h }, [x7]                        ; 0x00000158, line  126
        add     x7, x7, x13, lsl #1                     ; 0x0000015C, line  127
        st1     { v18.8h }, [x7]                        ; 0x00000160, line  128
        add     x7, x7, x14, lsl #1                     ; 0x00000164, line  129
        st1     { v19.8h }, [x7]                        ; 0x00000168, line  130
        add     x7, x7, x15, lsl #1                     ; 0x0000016C, line  131
        add     x12, x12, x13                           ; 0x00000170, line  132
        add     x14, x14, x15                           ; 0x00000174, line  133
        add     x9, x9, x12                             ; 0x00000178, line  134
        add     x9, x9, x14                             ; 0x0000017C, line  135
        cmp     x2, #0x30                               ; 0x00000180, line  136
        b.hs    Lmlk_rej_uniform_loop48                 ; 0x00000184, line  137
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_rej_uniform_loop48_end

        cmp     x9, x4                                  ; 0x00000190, line  140
        b.hs    Lmlk_rej_uniform_memory_copy            ; 0x00000194, line  141
        cmp     x2, #0x18                               ; 0x00000198, line  142
        b.lo    Lmlk_rej_uniform_memory_copy            ; 0x0000019C, line  143
        ld3     { v0.8b, v1.8b, v2.8b }, [x1], #24      ; 0x000001A0, line  144
        zip1    v4.16b, v0.16b, v1.16b                  ; 0x000001A4, line  145
        zip1    v5.16b, v1.16b, v2.16b                  ; 0x000001A8, line  146
        bic     v4.8h, #0xf0, lsl #8                    ; 0x000001AC, line  147
        ushr    v5.8h, v5.8h, #0x4                      ; 0x000001B0, line  148
        zip1    v16.8h, v4.8h, v5.8h                    ; 0x000001B4, line  149
        zip2    v17.8h, v4.8h, v5.8h                    ; 0x000001B8, line  150
        cmhi    v4.8h, v30.8h, v16.8h                   ; 0x000001BC, line  151
        cmhi    v5.8h, v30.8h, v17.8h                   ; 0x000001C0, line  152
        and     v4.16b, v4.16b, v31.16b                 ; 0x000001C4, line  153
        and     v5.16b, v5.16b, v31.16b                 ; 0x000001C8, line  154
        uaddlv  s20, v4.8h                              ; 0x000001CC, line  155
        uaddlv  s21, v5.8h                              ; 0x000001D0, line  156
        fmov    w12, s20                                ; 0x000001D4, line  157
        fmov    w13, s21                                ; 0x000001D8, line  158
        ldr     q24, [x3, x12, lsl #4]                  ; 0x000001DC, line  159
        ldr     q25, [x3, x13, lsl #4]                  ; 0x000001E0, line  160
        cnt     v4.16b, v4.16b                          ; 0x000001E4, line  161
        cnt     v5.16b, v5.16b                          ; 0x000001E8, line  162
        uaddlv  s20, v4.8h                              ; 0x000001EC, line  163
        uaddlv  s21, v5.8h                              ; 0x000001F0, line  164
        fmov    w12, s20                                ; 0x000001F4, line  165
        fmov    w13, s21                                ; 0x000001F8, line  166
        tbl     v16.16b, { v16.16b }, v24.16b           ; 0x000001FC, line  167
        tbl     v17.16b, { v17.16b }, v25.16b           ; 0x00000200, line  168
        st1     { v16.8h }, [x7]                        ; 0x00000204, line  169
        add     x7, x7, x12, lsl #1                     ; 0x00000208, line  170
        st1     { v17.8h }, [x7]                        ; 0x0000020C, line  171
        add     x9, x9, x12                             ; 0x00000210, line  172
        add     x9, x9, x13                             ; 0x00000214, line  173
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_rej_uniform_memory_copy

        cmp     x9, x4                                  ; 0x00000220, line  176
        csel    x9, x9, x4, lo                          ; 0x00000224, line  177
        mov     x11, #0x0                               ; 0x00000228, line  178
        mov     x7, x8                                  ; 0x0000022C, line  179

Lmlk_rej_uniform_final_copy

        ldr     q16, [x7], #0x40                        ; 0x00000230, line  182
        ldur    q17, [x7, #-0x30]                       ; 0x00000234, line  183
        ldur    q18, [x7, #-0x20]                       ; 0x00000238, line  184
        ldur    q19, [x7, #-0x10]                       ; 0x0000023C, line  185
        str     q16, [x0], #0x40                        ; 0x00000240, line  186
        stur    q17, [x0, #-0x30]                       ; 0x00000244, line  187
        stur    q18, [x0, #-0x20]                       ; 0x00000248, line  188
        stur    q19, [x0, #-0x10]                       ; 0x0000024C, line  189
        add     x11, x11, #0x20                         ; 0x00000250, line  190
        cmp     x11, #0x100                             ; 0x00000254, line  191
        b.lt    Lmlk_rej_uniform_final_copy             ; 0x00000258, line  192
        mov     x0, x9                                  ; 0x0000025C, line  193

Lmlk_rej_uniform_return

        add     sp, sp, #0x240                          ; 0x00000260, line  196
        ; .cfi_adjust_cfa_offset -0x240
        ret                                             ; 0x00000264, line  198
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000268 byte(s)

        AREA    |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD     0x0820009A                              ; header dword
        DCB     0xC0, 0x24                              ; unwind code 'alloc_m', stack space 0x0240
        DCB     0xE4                                    ; unwind code 'end'
        DCB     0x00                                    ; unwind code padding

        AREA    |.pdata|, DATA, READONLY, ALIGN=4

        DCD     $FUNC_NAME                              ; function start RVA
        DCD     XDATA_$FUNC_NAME                        ; pointer in XDATA section

        END
