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
; Name: ntt_aarch64_asm
; Description: AArch64 ML-KEM forward NTT following @[NeonNTT] and @[SLOTHY_Paper]
; Signature: void mlk_ntt_aarch64_asm(int16_t p[256], const int16_t twiddles12345[80], const int16_t twiddles56[384])
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
;   x1:
;     type: buffer
;     size_bytes: 160
;     permissions: read-only
;     c_parameter: const int16_t twiddles12345[80]
;     description: Twiddle factors for layers 1-5
;   x2:
;     type: buffer
;     size_bytes: 768
;     permissions: read-only
;     c_parameter: const int16_t twiddles56[384]
;     description: Twiddle factors for layers 6-7
; Stack:
;   bytes: 64
;   description: saving callee-saved Neon registers
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_ntt_aarch64_asm"
        ENDIF

        AREA      |.drectve|, DRECTVE

        EXPORT    $FUNC_NAME

        AREA      |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN     16

$FUNC_NAME PROC

        ; .cfi_startproc
        sub       sp, sp, #0x40                           ; 0x00000000, line   33
        ; .cfi_adjust_cfa_offset 0x40
        stp       d8, d9, [sp]                            ; 0x00000004, line   35
        ; .cfi_rel_offset d8, 0x0
        ; .cfi_rel_offset d9, 0x8
        stp       d10, d11, [sp, #0x10]                   ; 0x00000008, line   38
        ; .cfi_rel_offset d10, 0x10
        ; .cfi_rel_offset d11, 0x18
        stp       d12, d13, [sp, #0x20]                   ; 0x0000000C, line   41
        ; .cfi_rel_offset d12, 0x20
        ; .cfi_rel_offset d13, 0x28
        stp       d14, d15, [sp, #0x30]                   ; 0x00000010, line   44
        ; .cfi_rel_offset d14, 0x30
        ; .cfi_rel_offset d15, 0x38
        mov       w5, #0xd01                              ; 0x00000014, line   47
        mov       v7.h[0], w5                             ; 0x00000018, line   48
        mov       w5, #0x4ebf                             ; 0x0000001C, line   49
        mov       v7.h[1], w5                             ; 0x00000020, line   50
        mov       x3, x0                                  ; 0x00000024, line   51
        mov       x4, #0x4                                ; 0x00000028, line   52
        ldr       q0, [x1], #0x20                         ; 0x0000002C, line   53
        ldur      q1, [x1, #-0x10]                        ; 0x00000030, line   54
        ldr       q21, [x0, #0x40]                        ; 0x00000034, line   55
        ldr       q5, [x0, #0x1c0]                        ; 0x00000038, line   56
        ldr       q30, [x0, #0x110]                       ; 0x0000003C, line   57
        ldr       q24, [x0, #0x140]                       ; 0x00000040, line   58
        ldr       q12, [x0, #0x80]                        ; 0x00000044, line   59
        sqrdmulh  v9.8h, v5.8h, v0.h[1]                   ; 0x00000048, line   60
        mul       v23.8h, v5.8h, v0.h[0]                  ; 0x0000004C, line   61
        sqrdmulh  v17.8h, v24.8h, v0.h[1]                 ; 0x00000050, line   62
        ldr       q13, [x0, #0xc0]                        ; 0x00000054, line   63
        mls       v23.8h, v9.8h, v7.h[0]                  ; 0x00000058, line   64
        mul       v8.8h, v24.8h, v0.h[0]                  ; 0x0000005C, line   65
        mls       v8.8h, v17.8h, v7.h[0]                  ; 0x00000060, line   66
        add       v9.8h, v13.8h, v23.8h                   ; 0x00000064, line   67
        sub       v10.8h, v13.8h, v23.8h                  ; 0x00000068, line   68
        mul       v11.8h, v30.8h, v0.h[0]                 ; 0x0000006C, line   69
        ldr       q13, [x0, #0x180]                       ; 0x00000070, line   70
        sqrdmulh  v28.8h, v9.8h, v0.h[3]                  ; 0x00000074, line   71
        sub       v29.8h, v21.8h, v8.8h                   ; 0x00000078, line   72
        mul       v26.8h, v9.8h, v0.h[2]                  ; 0x0000007C, line   73
        add       v8.8h, v21.8h, v8.8h                    ; 0x00000080, line   74
        mul       v2.8h, v13.8h, v0.h[0]                  ; 0x00000084, line   75
        mls       v26.8h, v28.8h, v7.h[0]                 ; 0x00000088, line   76
        mul       v28.8h, v10.8h, v0.h[4]                 ; 0x0000008C, line   77
        sqrdmulh  v23.8h, v10.8h, v0.h[5]                 ; 0x00000090, line   78
        add       v22.8h, v8.8h, v26.8h                   ; 0x00000094, line   79
        sqrdmulh  v10.8h, v13.8h, v0.h[1]                 ; 0x00000098, line   80
        sqrdmulh  v21.8h, v22.8h, v0.h[7]                 ; 0x0000009C, line   81
        ldr       q13, [x0, #0x100]                       ; 0x000000A0, line   82
        mul       v16.8h, v22.8h, v0.h[6]                 ; 0x000000A4, line   83
        mls       v28.8h, v23.8h, v7.h[0]                 ; 0x000000A8, line   84
        mls       v2.8h, v10.8h, v7.h[0]                  ; 0x000000AC, line   85
        sqrdmulh  v23.8h, v13.8h, v0.h[1]                 ; 0x000000B0, line   86
        sub       v10.8h, v29.8h, v28.8h                  ; 0x000000B4, line   87
        add       v17.8h, v29.8h, v28.8h                  ; 0x000000B8, line   88
        mls       v16.8h, v21.8h, v7.h[0]                 ; 0x000000BC, line   89
        sub       v18.8h, v12.8h, v2.8h                   ; 0x000000C0, line   90
        ldr       q29, [x0]                               ; 0x000000C4, line   91
        sqrdmulh  v14.8h, v17.8h, v1.h[3]                 ; 0x000000C8, line   92
        add       v22.8h, v12.8h, v2.8h                   ; 0x000000CC, line   93
        sqrdmulh  v9.8h, v18.8h, v0.h[5]                  ; 0x000000D0, line   94
        mul       v21.8h, v13.8h, v0.h[0]                 ; 0x000000D4, line   95
        ldr       q13, [x0, #0x150]                       ; 0x000000D8, line   96
        mul       v5.8h, v18.8h, v0.h[4]                  ; 0x000000DC, line   97
        mls       v5.8h, v9.8h, v7.h[0]                   ; 0x000000E0, line   98
        mul       v18.8h, v13.8h, v0.h[0]                 ; 0x000000E4, line   99
        mls       v21.8h, v23.8h, v7.h[0]                 ; 0x000000E8, line  100
        sqrdmulh  v2.8h, v13.8h, v0.h[1]                  ; 0x000000EC, line  101
        mul       v13.8h, v17.8h, v1.h[2]                 ; 0x000000F0, line  102
        sub       v4.8h, v29.8h, v21.8h                   ; 0x000000F4, line  103
        mls       v13.8h, v14.8h, v7.h[0]                 ; 0x000000F8, line  104
        add       v25.8h, v29.8h, v21.8h                  ; 0x000000FC, line  105
        add       v6.8h, v4.8h, v5.8h                     ; 0x00000100, line  106
        sqrdmulh  v15.8h, v22.8h, v0.h[3]                 ; 0x00000104, line  107
        sub       v21.8h, v4.8h, v5.8h                    ; 0x00000108, line  108
        sub       v5.8h, v8.8h, v26.8h                    ; 0x0000010C, line  109
        mul       v23.8h, v22.8h, v0.h[2]                 ; 0x00000110, line  110
        add       v28.8h, v6.8h, v13.8h                   ; 0x00000114, line  111
        sub       v13.8h, v6.8h, v13.8h                   ; 0x00000118, line  112
        mul       v4.8h, v5.8h, v1.h[0]                   ; 0x0000011C, line  113
        sub       x4, x4, #0x2                            ; 0x00000120, line  114
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_ntt_layer123_start

        mls       v23.8h, v15.8h, v7.h[0]                 ; 0x00000130, line  117
        ldr       q6, [x0, #0x190]                        ; 0x00000134, line  118
        ldr       q15, [x0, #0x90]                        ; 0x00000138, line  119
        ldr       q19, [x0, #0x10]                        ; 0x0000013C, line  120
        mul       v22.8h, v10.8h, v1.h[4]                 ; 0x00000140, line  121
        ldr       q24, [x0, #0x50]                        ; 0x00000144, line  122
        str       q13, [x0, #0x140]                       ; 0x00000148, line  123
        sqrdmulh  v13.8h, v6.8h, v0.h[1]                  ; 0x0000014C, line  124
        sub       v20.8h, v25.8h, v23.8h                  ; 0x00000150, line  125
        sqrdmulh  v3.8h, v30.8h, v0.h[1]                  ; 0x00000154, line  126
        str       q28, [x0, #0x100]                       ; 0x00000158, line  127
        ldr       q30, [x0, #0x120]                       ; 0x0000015C, line  128
        mul       v8.8h, v6.8h, v0.h[0]                   ; 0x00000160, line  129
        sqrdmulh  v27.8h, v10.8h, v1.h[5]                 ; 0x00000164, line  130
        mls       v11.8h, v3.8h, v7.h[0]                  ; 0x00000168, line  131
        mls       v18.8h, v2.8h, v7.h[0]                  ; 0x0000016C, line  132
        ldr       q31, [x0, #0x160]                       ; 0x00000170, line  133
        sqrdmulh  v10.8h, v5.8h, v1.h[1]                  ; 0x00000174, line  134
        mls       v8.8h, v13.8h, v7.h[0]                  ; 0x00000178, line  135
        ldr       q13, [x0, #0x1d0]                       ; 0x0000017C, line  136
        sub       v14.8h, v24.8h, v18.8h                  ; 0x00000180, line  137
        add       v9.8h, v24.8h, v18.8h                   ; 0x00000184, line  138
        sqrdmulh  v2.8h, v31.8h, v0.h[1]                  ; 0x00000188, line  139
        mls       v4.8h, v10.8h, v7.h[0]                  ; 0x0000018C, line  140
        add       v10.8h, v25.8h, v23.8h                  ; 0x00000190, line  141
        sub       v24.8h, v19.8h, v11.8h                  ; 0x00000194, line  142
        add       v25.8h, v19.8h, v11.8h                  ; 0x00000198, line  143
        sqrdmulh  v28.8h, v13.8h, v0.h[1]                 ; 0x0000019C, line  144
        mul       v11.8h, v30.8h, v0.h[0]                 ; 0x000001A0, line  145
        mul       v17.8h, v13.8h, v0.h[0]                 ; 0x000001A4, line  146
        sub       v13.8h, v10.8h, v16.8h                  ; 0x000001A8, line  147
        sub       v6.8h, v15.8h, v8.8h                    ; 0x000001AC, line  148
        mls       v17.8h, v28.8h, v7.h[0]                 ; 0x000001B0, line  149
        str       q13, [x0, #0x40]                        ; 0x000001B4, line  150
        mls       v22.8h, v27.8h, v7.h[0]                 ; 0x000001B8, line  151
        ldr       q13, [x0, #0xd0]                        ; 0x000001BC, line  152
        add       v26.8h, v20.8h, v4.8h                   ; 0x000001C0, line  153
        mul       v18.8h, v31.8h, v0.h[0]                 ; 0x000001C4, line  154
        add       v27.8h, v10.8h, v16.8h                  ; 0x000001C8, line  155
        str       q26, [x0, #0x80]                        ; 0x000001CC, line  156
        sqrdmulh  v31.8h, v6.8h, v0.h[5]                  ; 0x000001D0, line  157
        add       v3.8h, v21.8h, v22.8h                   ; 0x000001D4, line  158
        str       q27, [x0], #0x10                        ; 0x000001D8, line  159
        mul       v26.8h, v6.8h, v0.h[4]                  ; 0x000001DC, line  160
        add       v6.8h, v13.8h, v17.8h                   ; 0x000001E0, line  161
        sub       v5.8h, v13.8h, v17.8h                   ; 0x000001E4, line  162
        str       q3, [x0, #0x170]                        ; 0x000001E8, line  163
        sub       v17.8h, v21.8h, v22.8h                  ; 0x000001EC, line  164
        sqrdmulh  v10.8h, v6.8h, v0.h[3]                  ; 0x000001F0, line  165
        sub       v13.8h, v20.8h, v4.8h                   ; 0x000001F4, line  166
        add       v20.8h, v15.8h, v8.8h                   ; 0x000001F8, line  167
        sqrdmulh  v12.8h, v5.8h, v0.h[5]                  ; 0x000001FC, line  168
        str       q13, [x0, #0xb0]                        ; 0x00000200, line  169
        mul       v8.8h, v6.8h, v0.h[2]                   ; 0x00000204, line  170
        str       q17, [x0, #0x1b0]                       ; 0x00000208, line  171
        mls       v8.8h, v10.8h, v7.h[0]                  ; 0x0000020C, line  172
        mul       v29.8h, v5.8h, v0.h[4]                  ; 0x00000210, line  173
        mls       v29.8h, v12.8h, v7.h[0]                 ; 0x00000214, line  174
        sub       v5.8h, v9.8h, v8.8h                     ; 0x00000218, line  175
        add       v3.8h, v9.8h, v8.8h                     ; 0x0000021C, line  176
        sqrdmulh  v15.8h, v20.8h, v0.h[3]                 ; 0x00000220, line  177
        mul       v4.8h, v5.8h, v1.h[0]                   ; 0x00000224, line  178
        add       v6.8h, v14.8h, v29.8h                   ; 0x00000228, line  179
        sqrdmulh  v9.8h, v3.8h, v0.h[7]                   ; 0x0000022C, line  180
        sqrdmulh  v12.8h, v6.8h, v1.h[3]                  ; 0x00000230, line  181
        sub       v10.8h, v14.8h, v29.8h                  ; 0x00000234, line  182
        mul       v23.8h, v6.8h, v1.h[2]                  ; 0x00000238, line  183
        mls       v26.8h, v31.8h, v7.h[0]                 ; 0x0000023C, line  184
        mls       v23.8h, v12.8h, v7.h[0]                 ; 0x00000240, line  185
        mul       v16.8h, v3.8h, v0.h[6]                  ; 0x00000244, line  186
        add       v13.8h, v24.8h, v26.8h                  ; 0x00000248, line  187
        sub       v21.8h, v24.8h, v26.8h                  ; 0x0000024C, line  188
        mls       v16.8h, v9.8h, v7.h[0]                  ; 0x00000250, line  189
        add       v28.8h, v13.8h, v23.8h                  ; 0x00000254, line  190
        sub       v13.8h, v13.8h, v23.8h                  ; 0x00000258, line  191
        mul       v23.8h, v20.8h, v0.h[2]                 ; 0x0000025C, line  192
        sub       x4, x4, #0x1                            ; 0x00000260, line  193
        cbnz      x4, Lmlk_ntt_layer123_start             ; 0x00000264, line  194
        sqrdmulh  v3.8h, v5.8h, v1.h[1]                   ; 0x00000268, line  195
        mls       v23.8h, v15.8h, v7.h[0]                 ; 0x0000026C, line  196
        ldr       q5, [x0, #0x190]                        ; 0x00000270, line  197
        mul       v29.8h, v10.8h, v1.h[4]                 ; 0x00000274, line  198
        mls       v4.8h, v3.8h, v7.h[0]                   ; 0x00000278, line  199
        sub       v19.8h, v25.8h, v23.8h                  ; 0x0000027C, line  200
        sqrdmulh  v31.8h, v5.8h, v0.h[1]                  ; 0x00000280, line  201
        sqrdmulh  v6.8h, v30.8h, v0.h[1]                  ; 0x00000284, line  202
        sub       v3.8h, v19.8h, v4.8h                    ; 0x00000288, line  203
        mul       v5.8h, v5.8h, v0.h[0]                   ; 0x0000028C, line  204
        str       q3, [x0, #0xc0]                         ; 0x00000290, line  205
        sqrdmulh  v12.8h, v10.8h, v1.h[5]                 ; 0x00000294, line  206
        mls       v18.8h, v2.8h, v7.h[0]                  ; 0x00000298, line  207
        ldr       q3, [x0, #0x1d0]                        ; 0x0000029C, line  208
        mls       v5.8h, v31.8h, v7.h[0]                  ; 0x000002A0, line  209
        sqrdmulh  v10.8h, v3.8h, v0.h[1]                  ; 0x000002A4, line  210
        mls       v11.8h, v6.8h, v7.h[0]                  ; 0x000002A8, line  211
        ldr       q31, [x0, #0x90]                        ; 0x000002AC, line  212
        mul       v30.8h, v3.8h, v0.h[0]                  ; 0x000002B0, line  213
        mls       v30.8h, v10.8h, v7.h[0]                 ; 0x000002B4, line  214
        sub       v10.8h, v31.8h, v5.8h                   ; 0x000002B8, line  215
        mls       v29.8h, v12.8h, v7.h[0]                 ; 0x000002BC, line  216
        ldr       q6, [x0, #0xd0]                         ; 0x000002C0, line  217
        sqrdmulh  v15.8h, v10.8h, v0.h[5]                 ; 0x000002C4, line  218
        mul       v17.8h, v10.8h, v0.h[4]                 ; 0x000002C8, line  219
        add       v10.8h, v6.8h, v30.8h                   ; 0x000002CC, line  220
        sub       v6.8h, v6.8h, v30.8h                    ; 0x000002D0, line  221
        sqrdmulh  v12.8h, v10.8h, v0.h[3]                 ; 0x000002D4, line  222
        sub       v27.8h, v21.8h, v29.8h                  ; 0x000002D8, line  223
        sqrdmulh  v3.8h, v6.8h, v0.h[5]                   ; 0x000002DC, line  224
        mul       v10.8h, v10.8h, v0.h[2]                 ; 0x000002E0, line  225
        ldr       q20, [x0, #0x50]                        ; 0x000002E4, line  226
        mls       v10.8h, v12.8h, v7.h[0]                 ; 0x000002E8, line  227
        mul       v2.8h, v6.8h, v0.h[4]                   ; 0x000002EC, line  228
        add       v6.8h, v20.8h, v18.8h                   ; 0x000002F0, line  229
        add       v5.8h, v31.8h, v5.8h                    ; 0x000002F4, line  230
        mls       v2.8h, v3.8h, v7.h[0]                   ; 0x000002F8, line  231
        sub       v31.8h, v6.8h, v10.8h                   ; 0x000002FC, line  232
        sqrdmulh  v12.8h, v5.8h, v0.h[3]                  ; 0x00000300, line  233
        sub       v22.8h, v20.8h, v18.8h                  ; 0x00000304, line  234
        add       v6.8h, v6.8h, v10.8h                    ; 0x00000308, line  235
        mul       v20.8h, v31.8h, v1.h[0]                 ; 0x0000030C, line  236
        add       v30.8h, v22.8h, v2.8h                   ; 0x00000310, line  237
        sqrdmulh  v3.8h, v6.8h, v0.h[7]                   ; 0x00000314, line  238
        sqrdmulh  v10.8h, v30.8h, v1.h[3]                 ; 0x00000318, line  239
        mul       v9.8h, v30.8h, v1.h[2]                  ; 0x0000031C, line  240
        ldr       q30, [x0, #0x10]                        ; 0x00000320, line  241
        mls       v17.8h, v15.8h, v7.h[0]                 ; 0x00000324, line  242
        mls       v9.8h, v10.8h, v7.h[0]                  ; 0x00000328, line  243
        mul       v15.8h, v6.8h, v0.h[6]                  ; 0x0000032C, line  244
        add       v24.8h, v30.8h, v11.8h                  ; 0x00000330, line  245
        sub       v10.8h, v22.8h, v2.8h                   ; 0x00000334, line  246
        mls       v15.8h, v3.8h, v7.h[0]                  ; 0x00000338, line  247
        add       v6.8h, v19.8h, v4.8h                    ; 0x0000033C, line  248
        add       v22.8h, v25.8h, v23.8h                  ; 0x00000340, line  249
        sqrdmulh  v3.8h, v10.8h, v1.h[5]                  ; 0x00000344, line  250
        str       q13, [x0, #0x140]                       ; 0x00000348, line  251
        sub       v19.8h, v30.8h, v11.8h                  ; 0x0000034C, line  252
        add       v25.8h, v22.8h, v16.8h                  ; 0x00000350, line  253
        mul       v5.8h, v5.8h, v0.h[2]                   ; 0x00000354, line  254
        sub       v13.8h, v22.8h, v16.8h                  ; 0x00000358, line  255
        str       q28, [x0, #0x100]                       ; 0x0000035C, line  256
        mls       v5.8h, v12.8h, v7.h[0]                  ; 0x00000360, line  257
        str       q13, [x0, #0x40]                        ; 0x00000364, line  258
        str       q6, [x0, #0x80]                         ; 0x00000368, line  259
        add       v21.8h, v21.8h, v29.8h                  ; 0x0000036C, line  260
        sqrdmulh  v13.8h, v31.8h, v1.h[1]                 ; 0x00000370, line  261
        str       q25, [x0], #0x10                        ; 0x00000374, line  262
        add       v12.8h, v19.8h, v17.8h                  ; 0x00000378, line  263
        sub       v31.8h, v19.8h, v17.8h                  ; 0x0000037C, line  264
        mul       v30.8h, v10.8h, v1.h[4]                 ; 0x00000380, line  265
        str       q21, [x0, #0x170]                       ; 0x00000384, line  266
        add       v21.8h, v24.8h, v5.8h                   ; 0x00000388, line  267
        add       v6.8h, v12.8h, v9.8h                    ; 0x0000038C, line  268
        mls       v30.8h, v3.8h, v7.h[0]                  ; 0x00000390, line  269
        str       q27, [x0, #0x1b0]                       ; 0x00000394, line  270
        sub       v10.8h, v21.8h, v15.8h                  ; 0x00000398, line  271
        sub       v12.8h, v12.8h, v9.8h                   ; 0x0000039C, line  272
        mls       v20.8h, v13.8h, v7.h[0]                 ; 0x000003A0, line  273
        str       q6, [x0, #0x100]                        ; 0x000003A4, line  274
        str       q10, [x0, #0x40]                        ; 0x000003A8, line  275
        sub       v13.8h, v24.8h, v5.8h                   ; 0x000003AC, line  276
        add       v3.8h, v21.8h, v15.8h                   ; 0x000003B0, line  277
        str       q12, [x0, #0x140]                       ; 0x000003B4, line  278
        sub       v10.8h, v31.8h, v30.8h                  ; 0x000003B8, line  279
        add       v21.8h, v31.8h, v30.8h                  ; 0x000003BC, line  280
        str       q3, [x0], #0x10                         ; 0x000003C0, line  281
        add       v12.8h, v13.8h, v20.8h                  ; 0x000003C4, line  282
        sub       v13.8h, v13.8h, v20.8h                  ; 0x000003C8, line  283
        str       q21, [x0, #0x170]                       ; 0x000003CC, line  284
        str       q10, [x0, #0x1b0]                       ; 0x000003D0, line  285
        str       q12, [x0, #0x70]                        ; 0x000003D4, line  286
        str       q13, [x0, #0xb0]                        ; 0x000003D8, line  287
        mov       x0, x3                                  ; 0x000003DC, line  288
        mov       x4, #0x8                                ; 0x000003E0, line  289
        ldr       q2, [x0, #0x20]                         ; 0x000003E4, line  290
        ldr       q13, [x1], #0x10                        ; 0x000003E8, line  291
        ldr       q30, [x0, #0x30]                        ; 0x000003EC, line  292
        ldr       q25, [x2, #0x40]                        ; 0x000003F0, line  293
        ldr       q5, [x0]                                ; 0x000003F4, line  294
        ldr       q18, [x0, #0x60]                        ; 0x000003F8, line  295
        ldr       q12, [x0, #0x70]                        ; 0x000003FC, line  296
        sqrdmulh  v17.8h, v2.8h, v13.h[1]                 ; 0x00000400, line  297
        ldr       q4, [x1], #0x10                         ; 0x00000404, line  298
        ldr       q23, [x0, #0x10]                        ; 0x00000408, line  299
        sqrdmulh  v21.8h, v30.8h, v13.h[1]                ; 0x0000040C, line  300
        ldr       q24, [x2, #0x20]                        ; 0x00000410, line  301
        ldr       q9, [x2], #0x60                         ; 0x00000414, line  302
        mul       v10.8h, v30.8h, v13.h[0]                ; 0x00000418, line  303
        mul       v11.8h, v2.8h, v13.h[0]                 ; 0x0000041C, line  304
        mls       v10.8h, v21.8h, v7.h[0]                 ; 0x00000420, line  305
        sqrdmulh  v29.8h, v12.8h, v4.h[1]                 ; 0x00000424, line  306
        mul       v1.8h, v12.8h, v4.h[0]                  ; 0x00000428, line  307
        add       v21.8h, v23.8h, v10.8h                  ; 0x0000042C, line  308
        sub       v10.8h, v23.8h, v10.8h                  ; 0x00000430, line  309
        mul       v8.8h, v18.8h, v4.h[0]                  ; 0x00000434, line  310
        sqrdmulh  v23.8h, v21.8h, v13.h[3]                ; 0x00000438, line  311
        mul       v2.8h, v21.8h, v13.h[2]                 ; 0x0000043C, line  312
        mls       v1.8h, v29.8h, v7.h[0]                  ; 0x00000440, line  313
        mls       v2.8h, v23.8h, v7.h[0]                  ; 0x00000444, line  314
        ldur      q15, [x2, #-0x50]                       ; 0x00000448, line  315
        sqrdmulh  v0.8h, v10.8h, v13.h[5]                 ; 0x0000044C, line  316
        mls       v11.8h, v17.8h, v7.h[0]                 ; 0x00000450, line  317
        ldr       q29, [x0, #0x50]                        ; 0x00000454, line  318
        mul       v23.8h, v10.8h, v13.h[4]                ; 0x00000458, line  319
        mls       v23.8h, v0.8h, v7.h[0]                  ; 0x0000045C, line  320
        sub       v16.8h, v29.8h, v1.8h                   ; 0x00000460, line  321
        add       v3.8h, v5.8h, v11.8h                    ; 0x00000464, line  322
        sub       v31.8h, v5.8h, v11.8h                   ; 0x00000468, line  323
        sqrdmulh  v22.8h, v16.8h, v4.h[5]                 ; 0x0000046C, line  324
        add       v30.8h, v3.8h, v2.8h                    ; 0x00000470, line  325
        sub       v0.8h, v3.8h, v2.8h                     ; 0x00000474, line  326
        sqrdmulh  v28.8h, v18.8h, v4.h[1]                 ; 0x00000478, line  327
        add       v21.8h, v31.8h, v23.8h                  ; 0x0000047C, line  328
        sub       v19.8h, v31.8h, v23.8h                  ; 0x00000480, line  329
        mul       v26.8h, v16.8h, v4.h[4]                 ; 0x00000484, line  330
        trn2      v3.4s, v30.4s, v0.4s                    ; 0x00000488, line  331
        ldur      q23, [x2, #-0x10]                       ; 0x0000048C, line  332
        trn2      v18.4s, v21.4s, v19.4s                  ; 0x00000490, line  333
        mls       v26.8h, v22.8h, v7.h[0]                 ; 0x00000494, line  334
        trn1      v13.4s, v30.4s, v0.4s                   ; 0x00000498, line  335
        mls       v8.8h, v28.8h, v7.h[0]                  ; 0x0000049C, line  336
        trn2      v31.2d, v3.2d, v18.2d                   ; 0x000004A0, line  337
        trn1      v11.4s, v21.4s, v19.4s                  ; 0x000004A4, line  338
        add       v27.8h, v29.8h, v1.8h                   ; 0x000004A8, line  339
        sqrdmulh  v6.8h, v31.8h, v15.8h                   ; 0x000004AC, line  340
        trn1      v2.2d, v13.2d, v11.2d                   ; 0x000004B0, line  341
        trn2      v13.2d, v13.2d, v11.2d                  ; 0x000004B4, line  342
        mul       v1.8h, v31.8h, v9.8h                    ; 0x000004B8, line  343
        ldr       q11, [x0, #0x40]                        ; 0x000004BC, line  344
        sqrdmulh  v29.8h, v13.8h, v15.8h                  ; 0x000004C0, line  345
        mls       v1.8h, v6.8h, v7.h[0]                   ; 0x000004C4, line  346
        trn1      v6.2d, v3.2d, v18.2d                    ; 0x000004C8, line  347
        mul       v17.8h, v13.8h, v9.8h                   ; 0x000004CC, line  348
        sub       v13.8h, v11.8h, v8.8h                   ; 0x000004D0, line  349
        sqrdmulh  v10.8h, v27.8h, v4.h[3]                 ; 0x000004D4, line  350
        sub       v12.8h, v13.8h, v26.8h                  ; 0x000004D8, line  351
        sub       v18.8h, v6.8h, v1.8h                    ; 0x000004DC, line  352
        mls       v17.8h, v29.8h, v7.h[0]                 ; 0x000004E0, line  353
        add       v30.8h, v6.8h, v1.8h                    ; 0x000004E4, line  354
        add       v6.8h, v13.8h, v26.8h                   ; 0x000004E8, line  355
        ldur      q13, [x2, #-0x30]                       ; 0x000004EC, line  356
        sqrdmulh  v16.8h, v18.8h, v23.8h                  ; 0x000004F0, line  357
        trn1      v28.4s, v6.4s, v12.4s                   ; 0x000004F4, line  358
        mul       v23.8h, v18.8h, v25.8h                  ; 0x000004F8, line  359
        ldr       q25, [x2, #0x10]                        ; 0x000004FC, line  360
        add       v20.8h, v2.8h, v17.8h                   ; 0x00000500, line  361
        mul       v0.8h, v30.8h, v24.8h                   ; 0x00000504, line  362
        sqrdmulh  v29.8h, v30.8h, v13.8h                  ; 0x00000508, line  363
        sub       v30.8h, v2.8h, v17.8h                   ; 0x0000050C, line  364
        mls       v23.8h, v16.8h, v7.h[0]                 ; 0x00000510, line  365
        sub       x4, x4, #0x2                            ; 0x00000514, line  366
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_ntt_layer4567_start

        ldr       q19, [x2, #0x50]                        ; 0x00000520, line  369
        sub       v31.8h, v30.8h, v23.8h                  ; 0x00000524, line  370
        mls       v0.8h, v29.8h, v7.h[0]                  ; 0x00000528, line  371
        add       v16.8h, v11.8h, v8.8h                   ; 0x0000052C, line  372
        ldr       q18, [x0, #0xa0]                        ; 0x00000530, line  373
        trn2      v14.4s, v6.4s, v12.4s                   ; 0x00000534, line  374
        mul       v26.8h, v27.8h, v4.h[2]                 ; 0x00000538, line  375
        ldr       q4, [x1], #0x10                         ; 0x0000053C, line  376
        ldr       q24, [x2, #0x40]                        ; 0x00000540, line  377
        ldr       q21, [x0, #0xb0]                        ; 0x00000544, line  378
        mls       v26.8h, v10.8h, v7.h[0]                 ; 0x00000548, line  379
        add       v23.8h, v30.8h, v23.8h                  ; 0x0000054C, line  380
        sub       v15.8h, v20.8h, v0.8h                   ; 0x00000550, line  381
        ldr       q9, [x0, #0x90]                         ; 0x00000554, line  382
        add       v10.8h, v20.8h, v0.8h                   ; 0x00000558, line  383
        mul       v8.8h, v18.8h, v4.h[0]                  ; 0x0000055C, line  384
        ldr       q1, [x2], #0x60                         ; 0x00000560, line  385
        trn1      v27.4s, v23.4s, v31.4s                  ; 0x00000564, line  386
        sqrdmulh  v12.8h, v18.8h, v4.h[1]                 ; 0x00000568, line  387
        trn1      v5.4s, v10.4s, v15.4s                   ; 0x0000056C, line  388
        sub       v30.8h, v16.8h, v26.8h                  ; 0x00000570, line  389
        trn2      v13.2d, v5.2d, v27.2d                   ; 0x00000574, line  390
        sqrdmulh  v2.8h, v21.8h, v4.h[1]                  ; 0x00000578, line  391
        add       v29.8h, v16.8h, v26.8h                  ; 0x0000057C, line  392
        mul       v0.8h, v21.8h, v4.h[0]                  ; 0x00000580, line  393
        str       q13, [x0, #0x20]                        ; 0x00000584, line  394
        trn1      v11.4s, v29.4s, v30.4s                  ; 0x00000588, line  395
        mls       v8.8h, v12.8h, v7.h[0]                  ; 0x0000058C, line  396
        trn2      v26.4s, v29.4s, v30.4s                  ; 0x00000590, line  397
        trn2      v6.2d, v11.2d, v28.2d                   ; 0x00000594, line  398
        mls       v0.8h, v2.8h, v7.h[0]                   ; 0x00000598, line  399
        trn2      v16.2d, v26.2d, v14.2d                  ; 0x0000059C, line  400
        trn1      v26.2d, v26.2d, v14.2d                  ; 0x000005A0, line  401
        trn1      v20.2d, v5.2d, v27.2d                   ; 0x000005A4, line  402
        sqrdmulh  v29.8h, v6.8h, v25.8h                   ; 0x000005A8, line  403
        trn2      v15.4s, v10.4s, v15.4s                  ; 0x000005AC, line  404
        sqrdmulh  v13.8h, v16.8h, v25.8h                  ; 0x000005B0, line  405
        str       q20, [x0], #0x40                        ; 0x000005B4, line  406
        sub       v30.8h, v9.8h, v0.8h                    ; 0x000005B8, line  407
        add       v27.8h, v9.8h, v0.8h                    ; 0x000005BC, line  408
        mul       v17.8h, v6.8h, v1.8h                    ; 0x000005C0, line  409
        sqrdmulh  v22.8h, v30.8h, v4.h[5]                 ; 0x000005C4, line  410
        mul       v18.8h, v16.8h, v1.8h                   ; 0x000005C8, line  411
        mls       v18.8h, v13.8h, v7.h[0]                 ; 0x000005CC, line  412
        mul       v2.8h, v30.8h, v4.h[4]                  ; 0x000005D0, line  413
        mls       v2.8h, v22.8h, v7.h[0]                  ; 0x000005D4, line  414
        trn2      v22.4s, v23.4s, v31.4s                  ; 0x000005D8, line  415
        sub       v3.8h, v26.8h, v18.8h                   ; 0x000005DC, line  416
        ldur      q25, [x2, #-0x30]                       ; 0x000005E0, line  417
        mls       v17.8h, v29.8h, v7.h[0]                 ; 0x000005E4, line  418
        trn2      v31.2d, v15.2d, v22.2d                  ; 0x000005E8, line  419
        trn1      v20.2d, v15.2d, v22.2d                  ; 0x000005EC, line  420
        add       v16.8h, v26.8h, v18.8h                  ; 0x000005F0, line  421
        sqrdmulh  v26.8h, v3.8h, v19.8h                   ; 0x000005F4, line  422
        trn1      v21.2d, v11.2d, v28.2d                  ; 0x000005F8, line  423
        ldr       q11, [x0, #0x40]                        ; 0x000005FC, line  424
        sqrdmulh  v29.8h, v16.8h, v25.8h                  ; 0x00000600, line  425
        stur      q20, [x0, #-0x30]                       ; 0x00000604, line  426
        add       v20.8h, v21.8h, v17.8h                  ; 0x00000608, line  427
        stur      q31, [x0, #-0x10]                       ; 0x0000060C, line  428
        mul       v23.8h, v3.8h, v24.8h                   ; 0x00000610, line  429
        ldr       q25, [x2, #0x10]                        ; 0x00000614, line  430
        sub       v13.8h, v11.8h, v8.8h                   ; 0x00000618, line  431
        mls       v23.8h, v26.8h, v7.h[0]                 ; 0x0000061C, line  432
        ldur      q1, [x2, #-0x40]                        ; 0x00000620, line  433
        sub       v12.8h, v13.8h, v2.8h                   ; 0x00000624, line  434
        add       v6.8h, v13.8h, v2.8h                    ; 0x00000628, line  435
        sqrdmulh  v10.8h, v27.8h, v4.h[3]                 ; 0x0000062C, line  436
        sub       v30.8h, v21.8h, v17.8h                  ; 0x00000630, line  437
        mul       v0.8h, v16.8h, v1.8h                    ; 0x00000634, line  438
        trn1      v28.4s, v6.4s, v12.4s                   ; 0x00000638, line  439
        sub       x4, x4, #0x1                            ; 0x0000063C, line  440
        cbnz      x4, Lmlk_ntt_layer4567_start            ; 0x00000640, line  441
        add       v22.8h, v11.8h, v8.8h                   ; 0x00000644, line  442
        mul       v27.8h, v27.8h, v4.h[2]                 ; 0x00000648, line  443
        trn2      v17.4s, v6.4s, v12.4s                   ; 0x0000064C, line  444
        ldr       q15, [x2], #0x60                        ; 0x00000650, line  445
        mls       v27.8h, v10.8h, v7.h[0]                 ; 0x00000654, line  446
        add       v4.8h, v30.8h, v23.8h                   ; 0x00000658, line  447
        sub       v18.8h, v30.8h, v23.8h                  ; 0x0000065C, line  448
        ldur      q6, [x2, #-0x30]                        ; 0x00000660, line  449
        mls       v0.8h, v29.8h, v7.h[0]                  ; 0x00000664, line  450
        ldur      q12, [x2, #-0x40]                       ; 0x00000668, line  451
        ldur      q24, [x2, #-0x20]                       ; 0x0000066C, line  452
        ldur      q2, [x2, #-0x10]                        ; 0x00000670, line  453
        trn1      v9.4s, v4.4s, v18.4s                    ; 0x00000674, line  454
        add       v10.8h, v22.8h, v27.8h                  ; 0x00000678, line  455
        sub       v13.8h, v22.8h, v27.8h                  ; 0x0000067C, line  456
        sub       v1.8h, v20.8h, v0.8h                    ; 0x00000680, line  457
        trn2      v21.4s, v10.4s, v13.4s                  ; 0x00000684, line  458
        add       v27.8h, v20.8h, v0.8h                   ; 0x00000688, line  459
        trn2      v3.2d, v21.2d, v17.2d                   ; 0x0000068C, line  460
        trn1      v13.4s, v10.4s, v13.4s                  ; 0x00000690, line  461
        trn1      v31.4s, v27.4s, v1.4s                   ; 0x00000694, line  462
        sqrdmulh  v10.8h, v3.8h, v25.8h                   ; 0x00000698, line  463
        trn2      v5.2d, v13.2d, v28.2d                   ; 0x0000069C, line  464
        trn1      v13.2d, v13.2d, v28.2d                  ; 0x000006A0, line  465
        trn1      v21.2d, v21.2d, v17.2d                  ; 0x000006A4, line  466
        sqrdmulh  v17.8h, v5.8h, v25.8h                   ; 0x000006A8, line  467
        trn2      v30.2d, v31.2d, v9.2d                   ; 0x000006AC, line  468
        mul       v25.8h, v3.8h, v15.8h                   ; 0x000006B0, line  469
        str       q30, [x0, #0x20]                        ; 0x000006B4, line  470
        trn2      v30.4s, v4.4s, v18.4s                   ; 0x000006B8, line  471
        mls       v25.8h, v10.8h, v7.h[0]                 ; 0x000006BC, line  472
        trn2      v3.4s, v27.4s, v1.4s                    ; 0x000006C0, line  473
        mul       v20.8h, v5.8h, v15.8h                   ; 0x000006C4, line  474
        trn2      v10.2d, v3.2d, v30.2d                   ; 0x000006C8, line  475
        mls       v20.8h, v17.8h, v7.h[0]                 ; 0x000006CC, line  476
        str       q10, [x0, #0x30]                        ; 0x000006D0, line  477
        sub       v18.8h, v21.8h, v25.8h                  ; 0x000006D4, line  478
        add       v10.8h, v21.8h, v25.8h                  ; 0x000006D8, line  479
        trn1      v3.2d, v3.2d, v30.2d                    ; 0x000006DC, line  480
        sqrdmulh  v30.8h, v18.8h, v2.8h                   ; 0x000006E0, line  481
        mul       v12.8h, v10.8h, v12.8h                  ; 0x000006E4, line  482
        sqrdmulh  v6.8h, v10.8h, v6.8h                    ; 0x000006E8, line  483
        str       q3, [x0, #0x10]                         ; 0x000006EC, line  484
        add       v21.8h, v13.8h, v20.8h                  ; 0x000006F0, line  485
        mul       v10.8h, v18.8h, v24.8h                  ; 0x000006F4, line  486
        sub       v13.8h, v13.8h, v20.8h                  ; 0x000006F8, line  487
        mls       v10.8h, v30.8h, v7.h[0]                 ; 0x000006FC, line  488
        mls       v12.8h, v6.8h, v7.h[0]                  ; 0x00000700, line  489
        trn1      v30.2d, v31.2d, v9.2d                   ; 0x00000704, line  490
        sub       v3.8h, v13.8h, v10.8h                   ; 0x00000708, line  491
        add       v6.8h, v13.8h, v10.8h                   ; 0x0000070C, line  492
        add       v10.8h, v21.8h, v12.8h                  ; 0x00000710, line  493
        sub       v21.8h, v21.8h, v12.8h                  ; 0x00000714, line  494
        trn2      v13.4s, v6.4s, v3.4s                    ; 0x00000718, line  495
        trn1      v12.4s, v10.4s, v21.4s                  ; 0x0000071C, line  496
        trn2      v21.4s, v10.4s, v21.4s                  ; 0x00000720, line  497
        trn1      v3.4s, v6.4s, v3.4s                     ; 0x00000724, line  498
        str       q30, [x0], #0x40                        ; 0x00000728, line  499
        trn2      v10.2d, v21.2d, v13.2d                  ; 0x0000072C, line  500
        trn1      v13.2d, v21.2d, v13.2d                  ; 0x00000730, line  501
        trn2      v21.2d, v12.2d, v3.2d                   ; 0x00000734, line  502
        trn1      v3.2d, v12.2d, v3.2d                    ; 0x00000738, line  503
        str       q10, [x0, #0x30]                        ; 0x0000073C, line  504
        str       q13, [x0, #0x10]                        ; 0x00000740, line  505
        str       q3, [x0], #0x40                         ; 0x00000744, line  506
        stur      q21, [x0, #-0x20]                       ; 0x00000748, line  507
        ldp       d8, d9, [sp]                            ; 0x0000074C, line  508
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp       d10, d11, [sp, #0x10]                   ; 0x00000750, line  511
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp       d12, d13, [sp, #0x20]                   ; 0x00000754, line  514
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp       d14, d15, [sp, #0x30]                   ; 0x00000758, line  517
        ; .cfi_restore d14
        ; .cfi_restore d15
        add       sp, sp, #0x40                           ; 0x0000075C, line  520
        ; .cfi_adjust_cfa_offset -0x40
        ret                                               ; 0x00000760, line  522
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000764 byte(s)

        AREA      |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD       0x182001D9                              ; header dword
        DCB       0xD9, 0x86                              ; unwind code 'save_fregp', registers d14,d15 at stack offset 0x0030
        DCB       0xD9, 0x04                              ; unwind code 'save_fregp', registers d12,d13 at stack offset 0x0020
        DCB       0xD8, 0x82                              ; unwind code 'save_fregp', registers d10,d11 at stack offset 0x0010
        DCB       0xD8, 0x00                              ; unwind code 'save_fregp', registers d8,d9 at stack offset 0x0000
        DCB       0x04                                    ; unwind code 'alloc_s', stack space 0x0040
        DCB       0xE4                                    ; unwind code 'end'
        DCB       0x00, 0x00                              ; unwind code padding

        AREA      |.pdata|, DATA, READONLY, ALIGN=4

        DCD       $FUNC_NAME                              ; function start RVA
        DCD       XDATA_$FUNC_NAME                        ; pointer in XDATA section

        END
