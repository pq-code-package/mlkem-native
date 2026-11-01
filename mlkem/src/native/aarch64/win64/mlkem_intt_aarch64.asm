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
; Name: intt_aarch64_asm
; Description: AArch64 ML-KEM inverse NTT following @[NeonNTT] and @[SLOTHY_Paper]
; Signature: void mlk_intt_aarch64_asm(int16_t p[256], const int16_t twiddles12345[80], const int16_t twiddles56[384])
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
FUNC_NAME SETS    "mlkem_intt_aarch64_asm"
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
        mov       w5, #0x200                              ; 0x00000024, line   51
        dup       v29.8h, w5                              ; 0x00000028, line   52
        mov       w5, #0x13b0                             ; 0x0000002C, line   53
        dup       v30.8h, w5                              ; 0x00000030, line   54
        mov       x3, x0                                  ; 0x00000034, line   55
        mov       x4, #0x8                                ; 0x00000038, line   56
        ldr       q13, [x3, #0x20]                        ; 0x0000003C, line   57
        ldr       q8, [x3, #0x30]                         ; 0x00000040, line   58
        ldr       q6, [x3]                                ; 0x00000044, line   59
        ldr       q16, [x3, #0x10]                        ; 0x00000048, line   60
        ldr       q4, [x3, #0x50]                         ; 0x0000004C, line   61
        ldr       q11, [x3, #0x40]                        ; 0x00000050, line   62
        ldr       q3, [x3, #0x70]                         ; 0x00000054, line   63
        trn1      v23.4s, v13.4s, v8.4s                   ; 0x00000058, line   64
        ldr       q0, [x3, #0x60]                         ; 0x0000005C, line   65
        trn2      v19.4s, v6.4s, v16.4s                   ; 0x00000060, line   66
        trn2      v21.4s, v13.4s, v8.4s                   ; 0x00000064, line   67
        trn1      v6.4s, v6.4s, v16.4s                    ; 0x00000068, line   68
        ldr       q24, [x2, #0x20]                        ; 0x0000006C, line   69
        trn1      v10.2d, v19.2d, v21.2d                  ; 0x00000070, line   70
        ldr       q16, [x2], #0x60                        ; 0x00000074, line   71
        trn1      v5.2d, v6.2d, v23.2d                    ; 0x00000078, line   72
        trn1      v28.4s, v0.4s, v3.4s                    ; 0x0000007C, line   73
        trn2      v18.2d, v6.2d, v23.2d                   ; 0x00000080, line   74
        mul       v31.8h, v10.8h, v29.8h                  ; 0x00000084, line   75
        trn2      v13.4s, v0.4s, v3.4s                    ; 0x00000088, line   76
        ldur      q14, [x2, #-0x50]                       ; 0x0000008C, line   77
        sqrdmulh  v26.8h, v18.8h, v30.8h                  ; 0x00000090, line   78
        ldur      q20, [x2, #-0x20]                       ; 0x00000094, line   79
        mul       v17.8h, v18.8h, v29.8h                  ; 0x00000098, line   80
        trn2      v18.2d, v19.2d, v21.2d                  ; 0x0000009C, line   81
        mul       v9.8h, v18.8h, v29.8h                   ; 0x000000A0, line   82
        trn1      v12.4s, v11.4s, v4.4s                   ; 0x000000A4, line   83
        sqrdmulh  v22.8h, v18.8h, v30.8h                  ; 0x000000A8, line   84
        sqrdmulh  v3.8h, v10.8h, v30.8h                   ; 0x000000AC, line   85
        sqrdmulh  v25.8h, v5.8h, v30.8h                   ; 0x000000B0, line   86
        mls       v9.8h, v22.8h, v7.h[0]                  ; 0x000000B4, line   87
        mls       v17.8h, v26.8h, v7.h[0]                 ; 0x000000B8, line   88
        trn2      v26.4s, v11.4s, v4.4s                   ; 0x000000BC, line   89
        mul       v8.8h, v5.8h, v29.8h                    ; 0x000000C0, line   90
        trn1      v10.2d, v26.2d, v13.2d                  ; 0x000000C4, line   91
        ldur      q11, [x2, #-0x10]                       ; 0x000000C8, line   92
        mls       v31.8h, v3.8h, v7.h[0]                  ; 0x000000CC, line   93
        trn1      v6.2d, v12.2d, v28.2d                   ; 0x000000D0, line   94
        trn2      v3.2d, v26.2d, v13.2d                   ; 0x000000D4, line   95
        ldur      q4, [x2, #-0x30]                        ; 0x000000D8, line   96
        mls       v8.8h, v25.8h, v7.h[0]                  ; 0x000000DC, line   97
        sub       v19.8h, v17.8h, v9.8h                   ; 0x000000E0, line   98
        trn2      v13.2d, v12.2d, v28.2d                  ; 0x000000E4, line   99
        sqrdmulh  v1.8h, v3.8h, v30.8h                    ; 0x000000E8, line  100
        add       v9.8h, v17.8h, v9.8h                    ; 0x000000EC, line  101
        mul       v18.8h, v19.8h, v20.8h                  ; 0x000000F0, line  102
        add       v28.8h, v8.8h, v31.8h                   ; 0x000000F4, line  103
        sqrdmulh  v20.8h, v19.8h, v11.8h                  ; 0x000000F8, line  104
        sub       v12.8h, v28.8h, v9.8h                   ; 0x000000FC, line  105
        sub       v23.8h, v8.8h, v31.8h                   ; 0x00000100, line  106
        sqrdmulh  v11.8h, v13.8h, v30.8h                  ; 0x00000104, line  107
        sqrdmulh  v5.8h, v23.8h, v4.8h                    ; 0x00000108, line  108
        mul       v0.8h, v23.8h, v24.8h                   ; 0x0000010C, line  109
        mul       v2.8h, v13.8h, v29.8h                   ; 0x00000110, line  110
        mls       v0.8h, v5.8h, v7.h[0]                   ; 0x00000114, line  111
        add       v24.8h, v28.8h, v9.8h                   ; 0x00000118, line  112
        mls       v18.8h, v20.8h, v7.h[0]                 ; 0x0000011C, line  113
        sqrdmulh  v15.8h, v6.8h, v30.8h                   ; 0x00000120, line  114
        sqrdmulh  v25.8h, v12.8h, v14.8h                  ; 0x00000124, line  115
        mul       v21.8h, v12.8h, v16.8h                  ; 0x00000128, line  116
        sub       v23.8h, v0.8h, v18.8h                   ; 0x0000012C, line  117
        sqrdmulh  v8.8h, v23.8h, v14.8h                   ; 0x00000130, line  118
        mul       v23.8h, v23.8h, v16.8h                  ; 0x00000134, line  119
        mls       v21.8h, v25.8h, v7.h[0]                 ; 0x00000138, line  120
        mls       v23.8h, v8.8h, v7.h[0]                  ; 0x0000013C, line  121
        mul       v14.8h, v3.8h, v29.8h                   ; 0x00000140, line  122
        add       v3.8h, v0.8h, v18.8h                    ; 0x00000144, line  123
        trn2      v4.4s, v24.4s, v3.4s                    ; 0x00000148, line  124
        mls       v14.8h, v1.8h, v7.h[0]                  ; 0x0000014C, line  125
        trn1      v9.4s, v24.4s, v3.4s                    ; 0x00000150, line  126
        trn2      v12.4s, v21.4s, v23.4s                  ; 0x00000154, line  127
        mls       v2.8h, v11.8h, v7.h[0]                  ; 0x00000158, line  128
        trn1      v28.4s, v21.4s, v23.4s                  ; 0x0000015C, line  129
        ldr       q11, [x1], #0x10                        ; 0x00000160, line  130
        mul       v31.8h, v10.8h, v29.8h                  ; 0x00000164, line  131
        trn1      v25.2d, v4.2d, v12.2d                   ; 0x00000168, line  132
        trn1      v20.2d, v9.2d, v28.2d                   ; 0x0000016C, line  133
        ldr       q23, [x2, #0x50]                        ; 0x00000170, line  134
        trn2      v13.2d, v4.2d, v12.2d                   ; 0x00000174, line  135
        sqrdmulh  v21.8h, v10.8h, v30.8h                  ; 0x00000178, line  136
        trn2      v4.2d, v9.2d, v28.2d                    ; 0x0000017C, line  137
        ldr       q9, [x2, #0x40]                         ; 0x00000180, line  138
        mul       v27.8h, v6.8h, v29.8h                   ; 0x00000184, line  139
        add       v26.8h, v20.8h, v25.8h                  ; 0x00000188, line  140
        sub       v3.8h, v2.8h, v14.8h                    ; 0x0000018C, line  141
        sqdmulh   v12.8h, v26.8h, v7.h[1]                 ; 0x00000190, line  142
        add       v5.8h, v4.8h, v13.8h                    ; 0x00000194, line  143
        sub       v8.8h, v4.8h, v13.8h                    ; 0x00000198, line  144
        add       v10.8h, v2.8h, v14.8h                   ; 0x0000019C, line  145
        sqdmulh   v6.8h, v5.8h, v7.h[1]                   ; 0x000001A0, line  146
        ldr       q2, [x2, #0x10]                         ; 0x000001A4, line  147
        mls       v27.8h, v15.8h, v7.h[0]                 ; 0x000001A8, line  148
        ldr       q15, [x2, #0x20]                        ; 0x000001AC, line  149
        srshr     v12.8h, v12.8h, #0xb                    ; 0x000001B0, line  150
        mls       v31.8h, v21.8h, v7.h[0]                 ; 0x000001B4, line  151
        srshr     v6.8h, v6.8h, #0xb                      ; 0x000001B8, line  152
        sqrdmulh  v23.8h, v3.8h, v23.8h                   ; 0x000001BC, line  153
        mls       v26.8h, v12.8h, v7.h[0]                 ; 0x000001C0, line  154
        add       v21.8h, v27.8h, v31.8h                  ; 0x000001C4, line  155
        mls       v5.8h, v6.8h, v7.h[0]                   ; 0x000001C8, line  156
        sub       v6.8h, v27.8h, v31.8h                   ; 0x000001CC, line  157
        sub       v14.8h, v21.8h, v10.8h                  ; 0x000001D0, line  158
        ldr       q27, [x2], #0x60                        ; 0x000001D4, line  159
        mul       v3.8h, v3.8h, v9.8h                     ; 0x000001D8, line  160
        mls       v3.8h, v23.8h, v7.h[0]                  ; 0x000001DC, line  161
        ldur      q13, [x2, #-0x30]                       ; 0x000001E0, line  162
        sub       v12.8h, v26.8h, v5.8h                   ; 0x000001E4, line  163
        add       v5.8h, v26.8h, v5.8h                    ; 0x000001E8, line  164
        sqrdmulh  v31.8h, v8.8h, v11.h[5]                 ; 0x000001EC, line  165
        sqrdmulh  v19.8h, v12.8h, v11.h[1]                ; 0x000001F0, line  166
        mul       v24.8h, v12.8h, v11.h[0]                ; 0x000001F4, line  167
        sqrdmulh  v13.8h, v6.8h, v13.8h                   ; 0x000001F8, line  168
        mls       v24.8h, v19.8h, v7.h[0]                 ; 0x000001FC, line  169
        sub       x4, x4, #0x2                            ; 0x00000200, line  170
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT      #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_intt_layer4567_start

        add       v16.8h, v21.8h, v10.8h                  ; 0x00000210, line  173
        mul       v18.8h, v6.8h, v15.8h                   ; 0x00000214, line  174
        sub       v19.8h, v20.8h, v25.8h                  ; 0x00000218, line  175
        ldr       q21, [x3, #0xa0]                        ; 0x0000021C, line  176
        str       q5, [x3], #0x40                         ; 0x00000220, line  177
        mls       v18.8h, v13.8h, v7.h[0]                 ; 0x00000224, line  178
        sqrdmulh  v15.8h, v14.8h, v2.8h                   ; 0x00000228, line  179
        ldr       q10, [x3, #0x50]                        ; 0x0000022C, line  180
        ldr       q12, [x3, #0x40]                        ; 0x00000230, line  181
        stur      q24, [x3, #-0x20]                       ; 0x00000234, line  182
        mul       v5.8h, v8.8h, v11.h[4]                  ; 0x00000238, line  183
        sub       v0.8h, v18.8h, v3.8h                    ; 0x0000023C, line  184
        ldr       q24, [x3, #0x70]                        ; 0x00000240, line  185
        mls       v5.8h, v31.8h, v7.h[0]                  ; 0x00000244, line  186
        ldr       q26, [x2, #0x50]                        ; 0x00000248, line  187
        trn2      v1.4s, v12.4s, v10.4s                   ; 0x0000024C, line  188
        add       v6.8h, v18.8h, v3.8h                    ; 0x00000250, line  189
        sqrdmulh  v20.8h, v0.8h, v2.8h                    ; 0x00000254, line  190
        trn1      v13.4s, v12.4s, v10.4s                  ; 0x00000258, line  191
        trn1      v18.4s, v16.4s, v6.4s                   ; 0x0000025C, line  192
        mul       v22.8h, v0.8h, v27.8h                   ; 0x00000260, line  193
        trn1      v17.4s, v21.4s, v24.4s                  ; 0x00000264, line  194
        sqrdmulh  v0.8h, v19.8h, v11.h[3]                 ; 0x00000268, line  195
        trn1      v25.2d, v13.2d, v17.2d                  ; 0x0000026C, line  196
        mls       v22.8h, v20.8h, v7.h[0]                 ; 0x00000270, line  197
        trn2      v21.4s, v21.4s, v24.4s                  ; 0x00000274, line  198
        mul       v24.8h, v25.8h, v29.8h                  ; 0x00000278, line  199
        trn2      v28.2d, v13.2d, v17.2d                  ; 0x0000027C, line  200
        sqrdmulh  v4.8h, v25.8h, v30.8h                   ; 0x00000280, line  201
        trn2      v3.2d, v1.2d, v21.2d                    ; 0x00000284, line  202
        mul       v17.8h, v28.8h, v29.8h                  ; 0x00000288, line  203
        sqrdmulh  v31.8h, v28.8h, v30.8h                  ; 0x0000028C, line  204
        ldr       q2, [x2, #0x10]                         ; 0x00000290, line  205
        mls       v24.8h, v4.8h, v7.h[0]                  ; 0x00000294, line  206
        mul       v4.8h, v19.8h, v11.h[2]                 ; 0x00000298, line  207
        ldr       q19, [x2, #0x40]                        ; 0x0000029C, line  208
        mls       v4.8h, v0.8h, v7.h[0]                   ; 0x000002A0, line  209
        mul       v0.8h, v14.8h, v27.8h                   ; 0x000002A4, line  210
        mls       v0.8h, v15.8h, v7.h[0]                  ; 0x000002A8, line  211
        sub       v8.8h, v4.8h, v5.8h                     ; 0x000002AC, line  212
        mul       v12.8h, v3.8h, v29.8h                   ; 0x000002B0, line  213
        mul       v23.8h, v8.8h, v11.h[0]                 ; 0x000002B4, line  214
        trn2      v28.4s, v16.4s, v6.4s                   ; 0x000002B8, line  215
        sqrdmulh  v10.8h, v8.8h, v11.h[1]                 ; 0x000002BC, line  216
        trn1      v9.4s, v0.4s, v22.4s                    ; 0x000002C0, line  217
        trn2      v22.4s, v0.4s, v22.4s                   ; 0x000002C4, line  218
        ldr       q11, [x1], #0x10                        ; 0x000002C8, line  219
        mls       v17.8h, v31.8h, v7.h[0]                 ; 0x000002CC, line  220
        trn1      v20.2d, v18.2d, v9.2d                   ; 0x000002D0, line  221
        trn2      v14.2d, v18.2d, v9.2d                   ; 0x000002D4, line  222
        ldr       q15, [x2, #0x20]                        ; 0x000002D8, line  223
        trn1      v6.2d, v1.2d, v21.2d                    ; 0x000002DC, line  224
        sqrdmulh  v9.8h, v3.8h, v30.8h                    ; 0x000002E0, line  225
        trn1      v25.2d, v28.2d, v22.2d                  ; 0x000002E4, line  226
        trn2      v16.2d, v28.2d, v22.2d                  ; 0x000002E8, line  227
        mls       v23.8h, v10.8h, v7.h[0]                 ; 0x000002EC, line  228
        add       v1.8h, v20.8h, v25.8h                   ; 0x000002F0, line  229
        sqrdmulh  v21.8h, v6.8h, v30.8h                   ; 0x000002F4, line  230
        add       v8.8h, v14.8h, v16.8h                   ; 0x000002F8, line  231
        ldr       q27, [x2], #0x60                        ; 0x000002FC, line  232
        sqdmulh   v28.8h, v8.8h, v7.h[1]                  ; 0x00000300, line  233
        mls       v12.8h, v9.8h, v7.h[0]                  ; 0x00000304, line  234
        sqdmulh   v31.8h, v1.8h, v7.h[1]                  ; 0x00000308, line  235
        mul       v0.8h, v6.8h, v29.8h                    ; 0x0000030C, line  236
        sub       v10.8h, v17.8h, v12.8h                  ; 0x00000310, line  237
        mls       v0.8h, v21.8h, v7.h[0]                  ; 0x00000314, line  238
        srshr     v21.8h, v28.8h, #0xb                    ; 0x00000318, line  239
        srshr     v13.8h, v31.8h, #0xb                    ; 0x0000031C, line  240
        sqrdmulh  v22.8h, v10.8h, v26.8h                  ; 0x00000320, line  241
        mls       v8.8h, v21.8h, v7.h[0]                  ; 0x00000324, line  242
        mls       v1.8h, v13.8h, v7.h[0]                  ; 0x00000328, line  243
        add       v21.8h, v24.8h, v0.8h                   ; 0x0000032C, line  244
        stur      q23, [x3, #-0x10]                       ; 0x00000330, line  245
        sub       v6.8h, v24.8h, v0.8h                    ; 0x00000334, line  246
        mul       v3.8h, v10.8h, v19.8h                   ; 0x00000338, line  247
        add       v0.8h, v4.8h, v5.8h                     ; 0x0000033C, line  248
        sqdmulh   v13.8h, v0.8h, v7.h[1]                  ; 0x00000340, line  249
        ldur      q10, [x2, #-0x30]                       ; 0x00000344, line  250
        add       v5.8h, v1.8h, v8.8h                     ; 0x00000348, line  251
        mls       v3.8h, v22.8h, v7.h[0]                  ; 0x0000034C, line  252
        sub       v8.8h, v1.8h, v8.8h                     ; 0x00000350, line  253
        mul       v24.8h, v8.8h, v11.h[0]                 ; 0x00000354, line  254
        sqrdmulh  v8.8h, v8.8h, v11.h[1]                  ; 0x00000358, line  255
        srshr     v1.8h, v13.8h, #0xb                     ; 0x0000035C, line  256
        sqrdmulh  v13.8h, v6.8h, v10.8h                   ; 0x00000360, line  257
        mls       v0.8h, v1.8h, v7.h[0]                   ; 0x00000364, line  258
        add       v10.8h, v17.8h, v12.8h                  ; 0x00000368, line  259
        mls       v24.8h, v8.8h, v7.h[0]                  ; 0x0000036C, line  260
        sub       v8.8h, v14.8h, v16.8h                   ; 0x00000370, line  261
        sqrdmulh  v31.8h, v8.8h, v11.h[5]                 ; 0x00000374, line  262
        sub       v14.8h, v21.8h, v10.8h                  ; 0x00000378, line  263
        stur      q0, [x3, #-0x30]                        ; 0x0000037C, line  264
        sub       x4, x4, #0x1                            ; 0x00000380, line  265
        cbnz      x4, Lmlk_intt_layer4567_start           ; 0x00000384, line  266
        mul       v15.8h, v6.8h, v15.8h                   ; 0x00000388, line  267
        sub       v22.8h, v20.8h, v25.8h                  ; 0x0000038C, line  268
        add       v4.8h, v21.8h, v10.8h                   ; 0x00000390, line  269
        str       q24, [x3, #0x20]                        ; 0x00000394, line  270
        mls       v15.8h, v13.8h, v7.h[0]                 ; 0x00000398, line  271
        str       q5, [x3], #0x40                         ; 0x0000039C, line  272
        ldr       q9, [x1], #0x10                         ; 0x000003A0, line  273
        sqrdmulh  v28.8h, v14.8h, v2.8h                   ; 0x000003A4, line  274
        mul       v16.8h, v14.8h, v27.8h                  ; 0x000003A8, line  275
        sub       v18.8h, v15.8h, v3.8h                   ; 0x000003AC, line  276
        add       v15.8h, v15.8h, v3.8h                   ; 0x000003B0, line  277
        sqrdmulh  v0.8h, v18.8h, v2.8h                    ; 0x000003B4, line  278
        trn2      v24.4s, v4.4s, v15.4s                   ; 0x000003B8, line  279
        trn1      v2.4s, v4.4s, v15.4s                    ; 0x000003BC, line  280
        mul       v18.8h, v18.8h, v27.8h                  ; 0x000003C0, line  281
        mls       v16.8h, v28.8h, v7.h[0]                 ; 0x000003C4, line  282
        mls       v18.8h, v0.8h, v7.h[0]                  ; 0x000003C8, line  283
        mul       v23.8h, v8.8h, v11.h[4]                 ; 0x000003CC, line  284
        sqrdmulh  v12.8h, v22.8h, v11.h[3]                ; 0x000003D0, line  285
        trn1      v17.4s, v16.4s, v18.4s                  ; 0x000003D4, line  286
        trn2      v4.4s, v16.4s, v18.4s                   ; 0x000003D8, line  287
        mls       v23.8h, v31.8h, v7.h[0]                 ; 0x000003DC, line  288
        trn2      v3.2d, v2.2d, v17.2d                    ; 0x000003E0, line  289
        trn2      v6.2d, v24.2d, v4.2d                    ; 0x000003E4, line  290
        mul       v26.8h, v22.8h, v11.h[2]                ; 0x000003E8, line  291
        trn1      v28.2d, v2.2d, v17.2d                   ; 0x000003EC, line  292
        mls       v26.8h, v12.8h, v7.h[0]                 ; 0x000003F0, line  293
        add       v25.8h, v3.8h, v6.8h                    ; 0x000003F4, line  294
        sub       v18.8h, v3.8h, v6.8h                    ; 0x000003F8, line  295
        trn1      v24.2d, v24.2d, v4.2d                   ; 0x000003FC, line  296
        sqdmulh   v1.8h, v25.8h, v7.h[1]                  ; 0x00000400, line  297
        sub       v27.8h, v28.8h, v24.8h                  ; 0x00000404, line  298
        sqrdmulh  v2.8h, v18.8h, v9.h[5]                  ; 0x00000408, line  299
        add       v28.8h, v28.8h, v24.8h                  ; 0x0000040C, line  300
        mul       v24.8h, v27.8h, v9.h[2]                 ; 0x00000410, line  301
        sqdmulh   v12.8h, v28.8h, v7.h[1]                 ; 0x00000414, line  302
        mul       v20.8h, v18.8h, v9.h[4]                 ; 0x00000418, line  303
        mls       v20.8h, v2.8h, v7.h[0]                  ; 0x0000041C, line  304
        srshr     v1.8h, v1.8h, #0xb                      ; 0x00000420, line  305
        sqrdmulh  v19.8h, v27.8h, v9.h[3]                 ; 0x00000424, line  306
        srshr     v15.8h, v12.8h, #0xb                    ; 0x00000428, line  307
        mls       v25.8h, v1.8h, v7.h[0]                  ; 0x0000042C, line  308
        add       v8.8h, v26.8h, v23.8h                   ; 0x00000430, line  309
        sub       v4.8h, v26.8h, v23.8h                   ; 0x00000434, line  310
        mls       v28.8h, v15.8h, v7.h[0]                 ; 0x00000438, line  311
        mls       v24.8h, v19.8h, v7.h[0]                 ; 0x0000043C, line  312
        mul       v2.8h, v4.8h, v11.h[0]                  ; 0x00000440, line  313
        sub       v19.8h, v28.8h, v25.8h                  ; 0x00000444, line  314
        sqrdmulh  v15.8h, v4.8h, v11.h[1]                 ; 0x00000448, line  315
        add       v25.8h, v28.8h, v25.8h                  ; 0x0000044C, line  316
        sub       v10.8h, v24.8h, v20.8h                  ; 0x00000450, line  317
        str       q25, [x3], #0x40                        ; 0x00000454, line  318
        sqrdmulh  v22.8h, v19.8h, v9.h[1]                 ; 0x00000458, line  319
        add       v28.8h, v24.8h, v20.8h                  ; 0x0000045C, line  320
        sqrdmulh  v25.8h, v10.8h, v9.h[1]                 ; 0x00000460, line  321
        mul       v27.8h, v19.8h, v9.h[0]                 ; 0x00000464, line  322
        mul       v26.8h, v10.8h, v9.h[0]                 ; 0x00000468, line  323
        sqdmulh   v20.8h, v28.8h, v7.h[1]                 ; 0x0000046C, line  324
        sqdmulh   v16.8h, v8.8h, v7.h[1]                  ; 0x00000470, line  325
        mls       v26.8h, v25.8h, v7.h[0]                 ; 0x00000474, line  326
        mls       v2.8h, v15.8h, v7.h[0]                  ; 0x00000478, line  327
        srshr     v15.8h, v20.8h, #0xb                    ; 0x0000047C, line  328
        srshr     v1.8h, v16.8h, #0xb                     ; 0x00000480, line  329
        mls       v27.8h, v22.8h, v7.h[0]                 ; 0x00000484, line  330
        mls       v28.8h, v15.8h, v7.h[0]                 ; 0x00000488, line  331
        mls       v8.8h, v1.8h, v7.h[0]                   ; 0x0000048C, line  332
        stur      q27, [x3, #-0x20]                       ; 0x00000490, line  333
        stur      q2, [x3, #-0x50]                        ; 0x00000494, line  334
        stur      q28, [x3, #-0x30]                       ; 0x00000498, line  335
        stur      q26, [x3, #-0x10]                       ; 0x0000049C, line  336
        stur      q8, [x3, #-0x70]                        ; 0x000004A0, line  337
        mov       x4, #0x4                                ; 0x000004A4, line  338
        ldr       q0, [x1], #0x20                         ; 0x000004A8, line  339
        ldur      q1, [x1, #-0x10]                        ; 0x000004AC, line  340
        ldr       q26, [x0]                               ; 0x000004B0, line  341
        ldr       q13, [x0, #0x40]                        ; 0x000004B4, line  342
        ldr       q28, [x0, #0xc0]                        ; 0x000004B8, line  343
        ldr       q2, [x0, #0x140]                        ; 0x000004BC, line  344
        ldr       q6, [x0, #0x80]                         ; 0x000004C0, line  345
        ldr       q9, [x0, #0x100]                        ; 0x000004C4, line  346
        ldr       q29, [x0, #0x1c0]                       ; 0x000004C8, line  347
        ldr       q23, [x0, #0x180]                       ; 0x000004CC, line  348
        sub       v17.8h, v26.8h, v13.8h                  ; 0x000004D0, line  349
        add       v4.8h, v26.8h, v13.8h                   ; 0x000004D4, line  350
        ldr       q25, [x0, #0xd0]                        ; 0x000004D8, line  351
        ldr       q24, [x0, #0x50]                        ; 0x000004DC, line  352
        add       v5.8h, v6.8h, v28.8h                    ; 0x000004E0, line  353
        mul       v19.8h, v17.8h, v0.h[6]                 ; 0x000004E4, line  354
        sub       v10.8h, v6.8h, v28.8h                   ; 0x000004E8, line  355
        ldr       q30, [x0, #0x150]                       ; 0x000004EC, line  356
        sqrdmulh  v12.8h, v17.8h, v0.h[7]                 ; 0x000004F0, line  357
        add       v17.8h, v9.8h, v2.8h                    ; 0x000004F4, line  358
        sub       v28.8h, v9.8h, v2.8h                    ; 0x000004F8, line  359
        ldr       q2, [x0, #0x90]                         ; 0x000004FC, line  360
        sub       v26.8h, v23.8h, v29.8h                  ; 0x00000500, line  361
        sqrdmulh  v31.8h, v10.8h, v1.h[1]                 ; 0x00000504, line  362
        add       v22.8h, v23.8h, v29.8h                  ; 0x00000508, line  363
        ldr       q3, [x0, #0x110]                        ; 0x0000050C, line  364
        sqrdmulh  v9.8h, v28.8h, v1.h[3]                  ; 0x00000510, line  365
        sub       v20.8h, v4.8h, v5.8h                    ; 0x00000514, line  366
        sub       v27.8h, v17.8h, v22.8h                  ; 0x00000518, line  367
        ldr       q29, [x0, #0x10]                        ; 0x0000051C, line  368
        add       v16.8h, v4.8h, v5.8h                    ; 0x00000520, line  369
        sqrdmulh  v4.8h, v26.8h, v1.h[5]                  ; 0x00000524, line  370
        add       v6.8h, v17.8h, v22.8h                   ; 0x00000528, line  371
        ldr       q22, [x0, #0x1d0]                       ; 0x0000052C, line  372
        mul       v8.8h, v28.8h, v1.h[2]                  ; 0x00000530, line  373
        sub       v21.8h, v2.8h, v25.8h                   ; 0x00000534, line  374
        sub       v5.8h, v16.8h, v6.8h                    ; 0x00000538, line  375
        mul       v17.8h, v26.8h, v1.h[4]                 ; 0x0000053C, line  376
        mul       v26.8h, v10.8h, v1.h[0]                 ; 0x00000540, line  377
        mls       v26.8h, v31.8h, v7.h[0]                 ; 0x00000544, line  378
        mls       v17.8h, v4.8h, v7.h[0]                  ; 0x00000548, line  379
        mls       v19.8h, v12.8h, v7.h[0]                 ; 0x0000054C, line  380
        mls       v8.8h, v9.8h, v7.h[0]                   ; 0x00000550, line  381
        sqrdmulh  v10.8h, v27.8h, v0.h[5]                 ; 0x00000554, line  382
        sub       v12.8h, v19.8h, v26.8h                  ; 0x00000558, line  383
        add       v9.8h, v19.8h, v26.8h                   ; 0x0000055C, line  384
        sqrdmulh  v26.8h, v20.8h, v0.h[3]                 ; 0x00000560, line  385
        sub       v11.8h, v8.8h, v17.8h                   ; 0x00000564, line  386
        add       v14.8h, v8.8h, v17.8h                   ; 0x00000568, line  387
        sqrdmulh  v13.8h, v12.8h, v0.h[3]                 ; 0x0000056C, line  388
        add       v23.8h, v9.8h, v14.8h                   ; 0x00000570, line  389
        sqrdmulh  v28.8h, v11.8h, v0.h[5]                 ; 0x00000574, line  390
        sub       v19.8h, v9.8h, v14.8h                   ; 0x00000578, line  391
        mul       v17.8h, v27.8h, v0.h[4]                 ; 0x0000057C, line  392
        str       q23, [x0, #0x40]                        ; 0x00000580, line  393
        mul       v14.8h, v20.8h, v0.h[2]                 ; 0x00000584, line  394
        mul       v8.8h, v11.8h, v0.h[4]                  ; 0x00000588, line  395
        mul       v4.8h, v12.8h, v0.h[2]                  ; 0x0000058C, line  396
        mls       v14.8h, v26.8h, v7.h[0]                 ; 0x00000590, line  397
        mls       v17.8h, v10.8h, v7.h[0]                 ; 0x00000594, line  398
        mls       v8.8h, v28.8h, v7.h[0]                  ; 0x00000598, line  399
        mls       v4.8h, v13.8h, v7.h[0]                  ; 0x0000059C, line  400
        sub       v10.8h, v14.8h, v17.8h                  ; 0x000005A0, line  401
        add       v20.8h, v14.8h, v17.8h                  ; 0x000005A4, line  402
        sqrdmulh  v28.8h, v5.8h, v0.h[1]                  ; 0x000005A8, line  403
        mul       v18.8h, v5.8h, v0.h[0]                  ; 0x000005AC, line  404
        str       q20, [x0, #0x80]                        ; 0x000005B0, line  405
        sub       v13.8h, v4.8h, v8.8h                    ; 0x000005B4, line  406
        mul       v23.8h, v10.8h, v0.h[0]                 ; 0x000005B8, line  407
        mul       v17.8h, v19.8h, v0.h[0]                 ; 0x000005BC, line  408
        sqrdmulh  v9.8h, v13.8h, v0.h[1]                  ; 0x000005C0, line  409
        mls       v18.8h, v28.8h, v7.h[0]                 ; 0x000005C4, line  410
        sqrdmulh  v10.8h, v10.8h, v0.h[1]                 ; 0x000005C8, line  411
        sub       x4, x4, #0x2                            ; 0x000005CC, line  412

Lmlk_intt_layer123_start

        sub       v12.8h, v3.8h, v30.8h                   ; 0x000005D0, line  415
        mul       v11.8h, v21.8h, v1.h[0]                 ; 0x000005D4, line  416
        add       v28.8h, v4.8h, v8.8h                    ; 0x000005D8, line  417
        ldr       q20, [x0, #0x190]                       ; 0x000005DC, line  418
        add       v27.8h, v16.8h, v6.8h                   ; 0x000005E0, line  419
        sqrdmulh  v8.8h, v12.8h, v1.h[3]                  ; 0x000005E4, line  420
        add       v16.8h, v29.8h, v24.8h                  ; 0x000005E8, line  421
        str       q28, [x0, #0xc0]                        ; 0x000005EC, line  422
        mls       v23.8h, v10.8h, v7.h[0]                 ; 0x000005F0, line  423
        str       q27, [x0], #0x10                        ; 0x000005F4, line  424
        add       v15.8h, v20.8h, v22.8h                  ; 0x000005F8, line  425
        str       q18, [x0, #0xf0]                        ; 0x000005FC, line  426
        mul       v14.8h, v13.8h, v0.h[0]                 ; 0x00000600, line  427
        add       v2.8h, v2.8h, v25.8h                    ; 0x00000604, line  428
        sub       v26.8h, v20.8h, v22.8h                  ; 0x00000608, line  429
        mul       v4.8h, v12.8h, v1.h[2]                  ; 0x0000060C, line  430
        sub       v5.8h, v16.8h, v2.8h                    ; 0x00000610, line  431
        str       q23, [x0, #0x170]                       ; 0x00000614, line  432
        add       v20.8h, v3.8h, v30.8h                   ; 0x00000618, line  433
        sqrdmulh  v27.8h, v26.8h, v1.h[5]                 ; 0x0000061C, line  434
        add       v16.8h, v16.8h, v2.8h                   ; 0x00000620, line  435
        mul       v18.8h, v26.8h, v1.h[4]                 ; 0x00000624, line  436
        sub       v31.8h, v20.8h, v15.8h                  ; 0x00000628, line  437
        mls       v4.8h, v8.8h, v7.h[0]                   ; 0x0000062C, line  438
        sub       v28.8h, v29.8h, v24.8h                  ; 0x00000630, line  439
        mls       v18.8h, v27.8h, v7.h[0]                 ; 0x00000634, line  440
        ldr       q22, [x0, #0x1d0]                       ; 0x00000638, line  441
        mul       v26.8h, v28.8h, v0.h[6]                 ; 0x0000063C, line  442
        mul       v2.8h, v5.8h, v0.h[2]                   ; 0x00000640, line  443
        sub       v12.8h, v4.8h, v18.8h                   ; 0x00000644, line  444
        sqrdmulh  v24.8h, v28.8h, v0.h[7]                 ; 0x00000648, line  445
        mls       v14.8h, v9.8h, v7.h[0]                  ; 0x0000064C, line  446
        sqrdmulh  v10.8h, v12.8h, v0.h[5]                 ; 0x00000650, line  447
        mls       v26.8h, v24.8h, v7.h[0]                 ; 0x00000654, line  448
        ldr       q24, [x0, #0x50]                        ; 0x00000658, line  449
        mul       v8.8h, v12.8h, v0.h[4]                  ; 0x0000065C, line  450
        str       q14, [x0, #0x1b0]                       ; 0x00000660, line  451
        add       v28.8h, v4.8h, v18.8h                   ; 0x00000664, line  452
        sqrdmulh  v5.8h, v5.8h, v0.h[3]                   ; 0x00000668, line  453
        add       v6.8h, v20.8h, v15.8h                   ; 0x0000066C, line  454
        sqrdmulh  v3.8h, v19.8h, v0.h[1]                  ; 0x00000670, line  455
        sub       v13.8h, v16.8h, v6.8h                   ; 0x00000674, line  456
        sqrdmulh  v12.8h, v21.8h, v1.h[1]                 ; 0x00000678, line  457
        sqrdmulh  v21.8h, v13.8h, v0.h[1]                 ; 0x0000067C, line  458
        sqrdmulh  v27.8h, v31.8h, v0.h[5]                 ; 0x00000680, line  459
        ldr       q25, [x0, #0xd0]                        ; 0x00000684, line  460
        mls       v11.8h, v12.8h, v7.h[0]                 ; 0x00000688, line  461
        mul       v23.8h, v31.8h, v0.h[4]                 ; 0x0000068C, line  462
        mul       v18.8h, v13.8h, v0.h[0]                 ; 0x00000690, line  463
        add       v30.8h, v26.8h, v11.8h                  ; 0x00000694, line  464
        sub       v13.8h, v26.8h, v11.8h                  ; 0x00000698, line  465
        mls       v23.8h, v27.8h, v7.h[0]                 ; 0x0000069C, line  466
        add       v12.8h, v30.8h, v28.8h                  ; 0x000006A0, line  467
        sub       v19.8h, v30.8h, v28.8h                  ; 0x000006A4, line  468
        mls       v2.8h, v5.8h, v7.h[0]                   ; 0x000006A8, line  469
        str       q12, [x0, #0x40]                        ; 0x000006AC, line  470
        sqrdmulh  v26.8h, v13.8h, v0.h[3]                 ; 0x000006B0, line  471
        mls       v8.8h, v10.8h, v7.h[0]                  ; 0x000006B4, line  472
        ldr       q30, [x0, #0x150]                       ; 0x000006B8, line  473
        sub       v20.8h, v2.8h, v23.8h                   ; 0x000006BC, line  474
        mul       v4.8h, v13.8h, v0.h[2]                  ; 0x000006C0, line  475
        add       v13.8h, v2.8h, v23.8h                   ; 0x000006C4, line  476
        mls       v4.8h, v26.8h, v7.h[0]                  ; 0x000006C8, line  477
        ldr       q2, [x0, #0x90]                         ; 0x000006CC, line  478
        mul       v23.8h, v20.8h, v0.h[0]                 ; 0x000006D0, line  479
        ldr       q29, [x0, #0x10]                        ; 0x000006D4, line  480
        sqrdmulh  v10.8h, v20.8h, v0.h[1]                 ; 0x000006D8, line  481
        str       q13, [x0, #0x80]                        ; 0x000006DC, line  482
        sub       v13.8h, v4.8h, v8.8h                    ; 0x000006E0, line  483
        mls       v17.8h, v3.8h, v7.h[0]                  ; 0x000006E4, line  484
        ldr       q3, [x0, #0x110]                        ; 0x000006E8, line  485
        mls       v18.8h, v21.8h, v7.h[0]                 ; 0x000006EC, line  486
        sub       v21.8h, v2.8h, v25.8h                   ; 0x000006F0, line  487
        sqrdmulh  v9.8h, v13.8h, v0.h[1]                  ; 0x000006F4, line  488
        str       q17, [x0, #0x130]                       ; 0x000006F8, line  489
        mul       v17.8h, v19.8h, v0.h[0]                 ; 0x000006FC, line  490
        sub       x4, x4, #0x1                            ; 0x00000700, line  491
        cbnz      x4, Lmlk_intt_layer123_start            ; 0x00000704, line  492
        mls       v23.8h, v10.8h, v7.h[0]                 ; 0x00000708, line  493
        ldr       q11, [x0, #0x190]                       ; 0x0000070C, line  494
        str       q18, [x0, #0x100]                       ; 0x00000710, line  495
        add       v27.8h, v3.8h, v30.8h                   ; 0x00000714, line  496
        mul       v13.8h, v13.8h, v0.h[0]                 ; 0x00000718, line  497
        sub       v5.8h, v29.8h, v24.8h                   ; 0x0000071C, line  498
        add       v14.8h, v16.8h, v6.8h                   ; 0x00000720, line  499
        mls       v13.8h, v9.8h, v7.h[0]                  ; 0x00000724, line  500
        add       v10.8h, v11.8h, v22.8h                  ; 0x00000728, line  501
        str       q23, [x0, #0x180]                       ; 0x0000072C, line  502
        sub       v20.8h, v11.8h, v22.8h                  ; 0x00000730, line  503
        sub       v23.8h, v27.8h, v10.8h                  ; 0x00000734, line  504
        sqrdmulh  v16.8h, v21.8h, v1.h[1]                 ; 0x00000738, line  505
        sqrdmulh  v31.8h, v23.8h, v0.h[5]                 ; 0x0000073C, line  506
        str       q13, [x0, #0x1c0]                       ; 0x00000740, line  507
        add       v13.8h, v4.8h, v8.8h                    ; 0x00000744, line  508
        mul       v18.8h, v21.8h, v1.h[0]                 ; 0x00000748, line  509
        str       q13, [x0, #0xc0]                        ; 0x0000074C, line  510
        sqrdmulh  v13.8h, v19.8h, v0.h[1]                 ; 0x00000750, line  511
        sqrdmulh  v28.8h, v20.8h, v1.h[5]                 ; 0x00000754, line  512
        str       q14, [x0], #0x10                        ; 0x00000758, line  513
        mul       v4.8h, v20.8h, v1.h[4]                  ; 0x0000075C, line  514
        mls       v17.8h, v13.8h, v7.h[0]                 ; 0x00000760, line  515
        sub       v13.8h, v3.8h, v30.8h                   ; 0x00000764, line  516
        sqrdmulh  v8.8h, v13.8h, v1.h[3]                  ; 0x00000768, line  517
        mul       v12.8h, v13.8h, v1.h[2]                 ; 0x0000076C, line  518
        mls       v4.8h, v28.8h, v7.h[0]                  ; 0x00000770, line  519
        mls       v12.8h, v8.8h, v7.h[0]                  ; 0x00000774, line  520
        mls       v18.8h, v16.8h, v7.h[0]                 ; 0x00000778, line  521
        str       q17, [x0, #0x130]                       ; 0x0000077C, line  522
        sqrdmulh  v15.8h, v5.8h, v0.h[7]                  ; 0x00000780, line  523
        add       v11.8h, v27.8h, v10.8h                  ; 0x00000784, line  524
        mul       v16.8h, v5.8h, v0.h[6]                  ; 0x00000788, line  525
        sub       v8.8h, v12.8h, v4.8h                    ; 0x0000078C, line  526
        sqrdmulh  v28.8h, v8.8h, v0.h[5]                  ; 0x00000790, line  527
        add       v13.8h, v2.8h, v25.8h                   ; 0x00000794, line  528
        mls       v16.8h, v15.8h, v7.h[0]                 ; 0x00000798, line  529
        add       v26.8h, v12.8h, v4.8h                   ; 0x0000079C, line  530
        mul       v8.8h, v8.8h, v0.h[4]                   ; 0x000007A0, line  531
        add       v4.8h, v29.8h, v24.8h                   ; 0x000007A4, line  532
        mls       v8.8h, v28.8h, v7.h[0]                  ; 0x000007A8, line  533
        sub       v20.8h, v4.8h, v13.8h                   ; 0x000007AC, line  534
        add       v14.8h, v4.8h, v13.8h                   ; 0x000007B0, line  535
        add       v12.8h, v16.8h, v18.8h                  ; 0x000007B4, line  536
        sqrdmulh  v22.8h, v20.8h, v0.h[3]                 ; 0x000007B8, line  537
        add       v27.8h, v14.8h, v11.8h                  ; 0x000007BC, line  538
        sub       v13.8h, v16.8h, v18.8h                  ; 0x000007C0, line  539
        mul       v4.8h, v20.8h, v0.h[2]                  ; 0x000007C4, line  540
        str       q27, [x0], #0x10                        ; 0x000007C8, line  541
        sub       v24.8h, v12.8h, v26.8h                  ; 0x000007CC, line  542
        sqrdmulh  v3.8h, v13.8h, v0.h[3]                  ; 0x000007D0, line  543
        mul       v13.8h, v13.8h, v0.h[2]                 ; 0x000007D4, line  544
        sqrdmulh  v27.8h, v24.8h, v0.h[1]                 ; 0x000007D8, line  545
        mls       v13.8h, v3.8h, v7.h[0]                  ; 0x000007DC, line  546
        mul       v9.8h, v24.8h, v0.h[0]                  ; 0x000007E0, line  547
        mls       v9.8h, v27.8h, v7.h[0]                  ; 0x000007E4, line  548
        add       v30.8h, v13.8h, v8.8h                   ; 0x000007E8, line  549
        sub       v13.8h, v13.8h, v8.8h                   ; 0x000007EC, line  550
        mls       v4.8h, v22.8h, v7.h[0]                  ; 0x000007F0, line  551
        str       q30, [x0, #0xb0]                        ; 0x000007F4, line  552
        sqrdmulh  v16.8h, v13.8h, v0.h[1]                 ; 0x000007F8, line  553
        str       q9, [x0, #0x130]                        ; 0x000007FC, line  554
        mul       v9.8h, v13.8h, v0.h[0]                  ; 0x00000800, line  555
        add       v13.8h, v12.8h, v26.8h                  ; 0x00000804, line  556
        str       q13, [x0, #0x30]                        ; 0x00000808, line  557
        mul       v13.8h, v23.8h, v0.h[4]                 ; 0x0000080C, line  558
        sub       v23.8h, v14.8h, v11.8h                  ; 0x00000810, line  559
        mls       v13.8h, v31.8h, v7.h[0]                 ; 0x00000814, line  560
        mls       v9.8h, v16.8h, v7.h[0]                  ; 0x00000818, line  561
        mul       v30.8h, v23.8h, v0.h[0]                 ; 0x0000081C, line  562
        sub       v24.8h, v4.8h, v13.8h                   ; 0x00000820, line  563
        add       v13.8h, v4.8h, v13.8h                   ; 0x00000824, line  564
        sqrdmulh  v23.8h, v23.8h, v0.h[1]                 ; 0x00000828, line  565
        str       q9, [x0, #0x1b0]                        ; 0x0000082C, line  566
        str       q13, [x0, #0x70]                        ; 0x00000830, line  567
        sqrdmulh  v13.8h, v24.8h, v0.h[1]                 ; 0x00000834, line  568
        mul       v21.8h, v24.8h, v0.h[0]                 ; 0x00000838, line  569
        mls       v30.8h, v23.8h, v7.h[0]                 ; 0x0000083C, line  570
        mls       v21.8h, v13.8h, v7.h[0]                 ; 0x00000840, line  571
        str       q30, [x0, #0xf0]                        ; 0x00000844, line  572
        str       q21, [x0, #0x170]                       ; 0x00000848, line  573
        ldp       d8, d9, [sp]                            ; 0x0000084C, line  574
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp       d10, d11, [sp, #0x10]                   ; 0x00000850, line  577
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp       d12, d13, [sp, #0x20]                   ; 0x00000854, line  580
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp       d14, d15, [sp, #0x30]                   ; 0x00000858, line  583
        ; .cfi_restore d14
        ; .cfi_restore d15
        add       sp, sp, #0x40                           ; 0x0000085C, line  586
        ; .cfi_adjust_cfa_offset -0x40
        ret                                               ; 0x00000860, line  588
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000864 byte(s)

        AREA      |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD       0x18200219                              ; header dword
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
