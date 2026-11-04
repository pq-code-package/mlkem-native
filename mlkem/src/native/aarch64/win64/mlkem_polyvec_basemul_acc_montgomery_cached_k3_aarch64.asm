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
; Name: polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm
; Description: Re-implementation of asymmetric base multiplication following @[NeonNTT] for k=3
; Signature: void mlk_polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm(int16_t r[256], const int16_t a[768], const int16_t b[768], const int16_t b_cache[384])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON]
;   x0:
;     type: buffer
;     size_bytes: 512
;     permissions: write-only
;     c_parameter: int16_t r[256]
;     description: Output polynomial
;   x1:
;     type: buffer
;     size_bytes: 1536
;     permissions: read-only
;     c_parameter: const int16_t a[768]
;     description: Input polynomial vector a
;   x2:
;     type: buffer
;     size_bytes: 1536
;     permissions: read-only
;     c_parameter: const int16_t b[768]
;     description: Input polynomial vector b
;   x3:
;     type: buffer
;     size_bytes: 768
;     permissions: read-only
;     c_parameter: const int16_t b_cache[384]
;     description: Cached values for b
; Stack:
;   bytes: 64
;   description: saving callee-saved Neon registers
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm"
        ENDIF

        AREA    |.drectve|, DRECTVE

        EXPORT  $FUNC_NAME

        AREA    |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN   16

$FUNC_NAME PROC

        ; .cfi_startproc
        sub     sp, sp, #0x40                                                 ; 0x00000000, line   39
        ; .cfi_adjust_cfa_offset 0x40
        stp     d8, d9, [sp]                                                  ; 0x00000004, line   41
        ; .cfi_rel_offset d8, 0x0
        ; .cfi_rel_offset d9, 0x8
        stp     d10, d11, [sp, #0x10]                                         ; 0x00000008, line   44
        ; .cfi_rel_offset d10, 0x10
        ; .cfi_rel_offset d11, 0x18
        stp     d12, d13, [sp, #0x20]                                         ; 0x0000000C, line   47
        ; .cfi_rel_offset d12, 0x20
        ; .cfi_rel_offset d13, 0x28
        stp     d14, d15, [sp, #0x30]                                         ; 0x00000010, line   50
        ; .cfi_rel_offset d14, 0x30
        ; .cfi_rel_offset d15, 0x38
        mov     w14, #0xd01                                                   ; 0x00000014, line   53
        dup     v0.8h, w14                                                    ; 0x00000018, line   54
        mov     w14, #0xcff                                                   ; 0x0000001C, line   55
        dup     v2.8h, w14                                                    ; 0x00000020, line   56
        add     x4, x1, #0x200                                                ; 0x00000024, line   57
        add     x5, x2, #0x200                                                ; 0x00000028, line   58
        add     x6, x3, #0x100                                                ; 0x0000002C, line   59
        add     x7, x1, #0x400                                                ; 0x00000030, line   60
        add     x8, x2, #0x400                                                ; 0x00000034, line   61
        add     x9, x3, #0x200                                                ; 0x00000038, line   62
        mov     x13, #0x10                                                    ; 0x0000003C, line   63
        ldr     q6, [x7], #0x20                                               ; 0x00000040, line   64
        ldr     q19, [x2, #0x10]                                              ; 0x00000044, line   65
        ldr     q23, [x1], #0x20                                              ; 0x00000048, line   66
        ldur    q14, [x1, #-0x10]                                             ; 0x0000004C, line   67
        ldr     q17, [x2], #0x20                                              ; 0x00000050, line   68
        ldr     q11, [x4, #0x10]                                              ; 0x00000054, line   69
        ldur    q28, [x7, #-0x10]                                             ; 0x00000058, line   70
        ld1     { v30.8h }, [x3], #16                                         ; 0x0000005C, line   71
        ldr     q26, [x4], #0x20                                              ; 0x00000060, line   72
        ldr     q16, [x8, #0x10]                                              ; 0x00000064, line   73
        uzp1    v8.8h, v23.8h, v14.8h                                         ; 0x00000068, line   74
        ldr     q22, [x5, #0x10]                                              ; 0x0000006C, line   75
        ldr     q18, [x5], #0x20                                              ; 0x00000070, line   76
        uzp1    v20.8h, v17.8h, v19.8h                                        ; 0x00000074, line   77
        uzp2    v24.8h, v23.8h, v14.8h                                        ; 0x00000078, line   78
        ldr     q31, [x8], #0x20                                              ; 0x0000007C, line   79
        smull2  v4.4s, v8.8h, v20.8h                                          ; 0x00000080, line   80
        uzp1    v25.8h, v26.8h, v11.8h                                        ; 0x00000084, line   81
        smull   v13.4s, v8.4h, v20.4h                                         ; 0x00000088, line   82
        ld1     { v23.8h }, [x6], #16                                         ; 0x0000008C, line   83
        uzp1    v1.8h, v18.8h, v22.8h                                         ; 0x00000090, line   84
        smlal   v13.4s, v24.4h, v30.4h                                        ; 0x00000094, line   85
        smlal2  v4.4s, v24.8h, v30.8h                                         ; 0x00000098, line   86
        uzp2    v5.8h, v26.8h, v11.8h                                         ; 0x0000009C, line   87
        smlal2  v4.4s, v25.8h, v1.8h                                          ; 0x000000A0, line   88
        uzp1    v29.8h, v6.8h, v28.8h                                         ; 0x000000A4, line   89
        smlal2  v4.4s, v5.8h, v23.8h                                          ; 0x000000A8, line   90
        ld1     { v7.8h }, [x9], #16                                          ; 0x000000AC, line   91
        smlal   v13.4s, v25.4h, v1.4h                                         ; 0x000000B0, line   92
        uzp2    v17.8h, v17.8h, v19.8h                                        ; 0x000000B4, line   93
        uzp1    v27.8h, v31.8h, v16.8h                                        ; 0x000000B8, line   94
        smlal   v13.4s, v5.4h, v23.4h                                         ; 0x000000BC, line   95
        uzp2    v22.8h, v18.8h, v22.8h                                        ; 0x000000C0, line   96
        smull   v18.4s, v8.4h, v17.4h                                         ; 0x000000C4, line   97
        uzp2    v28.8h, v6.8h, v28.8h                                         ; 0x000000C8, line   98
        smlal   v13.4s, v29.4h, v27.4h                                        ; 0x000000CC, line   99
        smlal2  v4.4s, v29.8h, v27.8h                                         ; 0x000000D0, line  100
        uzp2    v26.8h, v31.8h, v16.8h                                        ; 0x000000D4, line  101
        smlal2  v4.4s, v28.8h, v7.8h                                          ; 0x000000D8, line  102
        ldr     q3, [x7, #0x10]                                               ; 0x000000DC, line  103
        smlal   v13.4s, v28.4h, v7.4h                                         ; 0x000000E0, line  104
        ldr     q7, [x1], #0x20                                               ; 0x000000E4, line  105
        smlal   v18.4s, v24.4h, v20.4h                                        ; 0x000000E8, line  106
        ldr     q15, [x2], #0x20                                              ; 0x000000EC, line  107
        smlal   v18.4s, v25.4h, v22.4h                                        ; 0x000000F0, line  108
        smull2  v8.4s, v8.8h, v17.8h                                          ; 0x000000F4, line  109
        ldur    q17, [x1, #-0x10]                                             ; 0x000000F8, line  110
        uzp1    v23.8h, v13.8h, v4.8h                                         ; 0x000000FC, line  111
        smlal   v18.4s, v5.4h, v1.4h                                          ; 0x00000100, line  112
        smlal2  v8.4s, v24.8h, v20.8h                                         ; 0x00000104, line  113
        ld1     { v16.8h }, [x3], #16                                         ; 0x00000108, line  114
        mul     v23.8h, v23.8h, v2.8h                                         ; 0x0000010C, line  115
        ldr     q19, [x5, #0x10]                                              ; 0x00000110, line  116
        ldr     q14, [x4, #0x10]                                              ; 0x00000114, line  117
        ldr     q11, [x4], #0x20                                              ; 0x00000118, line  118
        ldur    q20, [x2, #-0x10]                                             ; 0x0000011C, line  119
        smlal2  v8.4s, v25.8h, v22.8h                                         ; 0x00000120, line  120
        smlal2  v8.4s, v5.8h, v1.8h                                           ; 0x00000124, line  121
        ldr     q22, [x5], #0x20                                              ; 0x00000128, line  122
        uzp1    v1.8h, v7.8h, v17.8h                                          ; 0x0000012C, line  123
        smlal   v18.4s, v29.4h, v26.4h                                        ; 0x00000130, line  124
        smlal   v13.4s, v23.4h, v0.4h                                         ; 0x00000134, line  125
        uzp2    v31.8h, v11.8h, v14.8h                                        ; 0x00000138, line  126
        uzp1    v21.8h, v15.8h, v20.8h                                        ; 0x0000013C, line  127
        smlal2  v4.4s, v23.8h, v0.8h                                          ; 0x00000140, line  128
        ld1     { v9.8h }, [x6], #16                                          ; 0x00000144, line  129
        smlal   v18.4s, v28.4h, v27.4h                                        ; 0x00000148, line  130
        smlal2  v8.4s, v29.8h, v26.8h                                         ; 0x0000014C, line  131
        ldr     q25, [x7], #0x20                                              ; 0x00000150, line  132
        smull   v26.4s, v1.4h, v21.4h                                         ; 0x00000154, line  133
        uzp1    v24.8h, v22.8h, v19.8h                                        ; 0x00000158, line  134
        smlal2  v8.4s, v28.8h, v27.8h                                         ; 0x0000015C, line  135
        uzp2    v28.8h, v7.8h, v17.8h                                         ; 0x00000160, line  136
        uzp1    v29.8h, v11.8h, v14.8h                                        ; 0x00000164, line  137
        smull2  v23.4s, v1.8h, v21.8h                                         ; 0x00000168, line  138
        ldr     q27, [x8], #0x20                                              ; 0x0000016C, line  139
        smlal2  v23.4s, v28.8h, v16.8h                                        ; 0x00000170, line  140
        ldur    q11, [x8, #-0x10]                                             ; 0x00000174, line  141
        smlal2  v23.4s, v29.8h, v24.8h                                        ; 0x00000178, line  142
        uzp2    v7.8h, v13.8h, v4.8h                                          ; 0x0000017C, line  143
        uzp2    v19.8h, v22.8h, v19.8h                                        ; 0x00000180, line  144
        ld1     { v4.8h }, [x9], #16                                          ; 0x00000184, line  145
        smlal2  v23.4s, v31.8h, v9.8h                                         ; 0x00000188, line  146
        uzp1    v13.8h, v25.8h, v3.8h                                         ; 0x0000018C, line  147
        uzp1    v14.8h, v18.8h, v8.8h                                         ; 0x00000190, line  148
        smlal   v26.4s, v28.4h, v16.4h                                        ; 0x00000194, line  149
        uzp2    v17.8h, v27.8h, v11.8h                                        ; 0x00000198, line  150
        uzp2    v20.8h, v15.8h, v20.8h                                        ; 0x0000019C, line  151
        mul     v14.8h, v14.8h, v2.8h                                         ; 0x000001A0, line  152
        sub     x13, x13, #0x2                                                ; 0x000001A4, line  153
        HINT    #0x0                                                          ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                                          ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_polyvec_basemul_acc_montgomery_cached_k3_loop_start

        uzp1    v6.8h, v27.8h, v11.8h                                         ; 0x000001B0, line  156
        smlal   v26.4s, v29.4h, v24.4h                                        ; 0x000001B4, line  157
        uzp2    v16.8h, v25.8h, v3.8h                                         ; 0x000001B8, line  158
        smlal   v26.4s, v31.4h, v9.4h                                         ; 0x000001BC, line  159
        ldr     q3, [x7, #0x10]                                               ; 0x000001C0, line  160
        smlal   v26.4s, v13.4h, v6.4h                                         ; 0x000001C4, line  161
        smlal2  v8.4s, v14.8h, v0.8h                                          ; 0x000001C8, line  162
        ldr     q27, [x8], #0x20                                              ; 0x000001CC, line  163
        smlal   v18.4s, v14.4h, v0.4h                                         ; 0x000001D0, line  164
        ldr     q25, [x7], #0x20                                              ; 0x000001D4, line  165
        smlal2  v23.4s, v13.8h, v6.8h                                         ; 0x000001D8, line  166
        ldr     q11, [x1], #0x20                                              ; 0x000001DC, line  167
        smlal2  v23.4s, v16.8h, v4.8h                                         ; 0x000001E0, line  168
        smlal   v26.4s, v16.4h, v4.4h                                         ; 0x000001E4, line  169
        ldur    q22, [x1, #-0x10]                                             ; 0x000001E8, line  170
        uzp2    v30.8h, v18.8h, v8.8h                                         ; 0x000001EC, line  171
        smull   v18.4s, v1.4h, v20.4h                                         ; 0x000001F0, line  172
        smlal   v18.4s, v28.4h, v21.4h                                        ; 0x000001F4, line  173
        ldr     q14, [x2], #0x20                                              ; 0x000001F8, line  174
        smlal   v18.4s, v29.4h, v19.4h                                        ; 0x000001FC, line  175
        zip1    v5.8h, v7.8h, v30.8h                                          ; 0x00000200, line  176
        uzp1    v4.8h, v26.8h, v23.8h                                         ; 0x00000204, line  177
        smull2  v8.4s, v1.8h, v20.8h                                          ; 0x00000208, line  178
        zip2    v10.8h, v7.8h, v30.8h                                         ; 0x0000020C, line  179
        smlal   v18.4s, v31.4h, v24.4h                                        ; 0x00000210, line  180
        mul     v12.8h, v4.8h, v2.8h                                          ; 0x00000214, line  181
        ldr     q4, [x5, #0x10]                                               ; 0x00000218, line  182
        ldr     q20, [x4, #0x10]                                              ; 0x0000021C, line  183
        ldr     q1, [x4], #0x20                                               ; 0x00000220, line  184
        ldur    q30, [x2, #-0x10]                                             ; 0x00000224, line  185
        smlal2  v8.4s, v28.8h, v21.8h                                         ; 0x00000228, line  186
        smlal2  v8.4s, v29.8h, v19.8h                                         ; 0x0000022C, line  187
        ldr     q19, [x5], #0x20                                              ; 0x00000230, line  188
        smlal2  v8.4s, v31.8h, v24.8h                                         ; 0x00000234, line  189
        ld1     { v15.8h }, [x3], #16                                         ; 0x00000238, line  190
        uzp2    v31.8h, v1.8h, v20.8h                                         ; 0x0000023C, line  191
        smlal   v26.4s, v12.4h, v0.4h                                         ; 0x00000240, line  192
        smlal2  v23.4s, v12.8h, v0.8h                                         ; 0x00000244, line  193
        uzp1    v21.8h, v14.8h, v30.8h                                        ; 0x00000248, line  194
        uzp1    v29.8h, v1.8h, v20.8h                                         ; 0x0000024C, line  195
        uzp1    v1.8h, v11.8h, v22.8h                                         ; 0x00000250, line  196
        smlal2  v8.4s, v13.8h, v17.8h                                         ; 0x00000254, line  197
        ld1     { v9.8h }, [x6], #16                                          ; 0x00000258, line  198
        smlal   v18.4s, v13.4h, v17.4h                                        ; 0x0000025C, line  199
        uzp1    v24.8h, v19.8h, v4.8h                                         ; 0x00000260, line  200
        uzp2    v7.8h, v26.8h, v23.8h                                         ; 0x00000264, line  201
        smull   v26.4s, v1.4h, v21.4h                                         ; 0x00000268, line  202
        smlal   v18.4s, v16.4h, v6.4h                                         ; 0x0000026C, line  203
        uzp2    v19.8h, v19.8h, v4.8h                                         ; 0x00000270, line  204
        smlal2  v8.4s, v16.8h, v6.8h                                          ; 0x00000274, line  205
        uzp2    v28.8h, v11.8h, v22.8h                                        ; 0x00000278, line  206
        smull2  v23.4s, v1.8h, v21.8h                                         ; 0x0000027C, line  207
        uzp1    v13.8h, v25.8h, v3.8h                                         ; 0x00000280, line  208
        smlal2  v23.4s, v28.8h, v15.8h                                        ; 0x00000284, line  209
        ldur    q11, [x8, #-0x10]                                             ; 0x00000288, line  210
        smlal2  v23.4s, v29.8h, v24.8h                                        ; 0x0000028C, line  211
        ld1     { v4.8h }, [x9], #16                                          ; 0x00000290, line  212
        smlal2  v23.4s, v31.8h, v9.8h                                         ; 0x00000294, line  213
        uzp1    v12.8h, v18.8h, v8.8h                                         ; 0x00000298, line  214
        uzp2    v20.8h, v14.8h, v30.8h                                        ; 0x0000029C, line  215
        smlal   v26.4s, v28.4h, v15.4h                                        ; 0x000002A0, line  216
        str     q5, [x0], #0x20                                               ; 0x000002A4, line  217
        mul     v14.8h, v12.8h, v2.8h                                         ; 0x000002A8, line  218
        stur    q10, [x0, #-0x10]                                             ; 0x000002AC, line  219
        uzp2    v17.8h, v27.8h, v11.8h                                        ; 0x000002B0, line  220
        subs    x13, x13, #0x1                                                ; 0x000002B4, line  221
        cbnz    x13, Lmlk_polyvec_basemul_acc_montgomery_cached_k3_loop_start ; 0x000002B8, line  222
        uzp2    v3.8h, v25.8h, v3.8h                                          ; 0x000002BC, line  223
        smull2  v16.4s, v1.8h, v20.8h                                         ; 0x000002C0, line  224
        smull   v25.4s, v1.4h, v20.4h                                         ; 0x000002C4, line  225
        uzp1    v22.8h, v27.8h, v11.8h                                        ; 0x000002C8, line  226
        smlal2  v16.4s, v28.8h, v21.8h                                        ; 0x000002CC, line  227
        smlal   v25.4s, v28.4h, v21.4h                                        ; 0x000002D0, line  228
        smlal2  v16.4s, v29.8h, v19.8h                                        ; 0x000002D4, line  229
        smlal   v25.4s, v29.4h, v19.4h                                        ; 0x000002D8, line  230
        smlal2  v16.4s, v31.8h, v24.8h                                        ; 0x000002DC, line  231
        smlal   v25.4s, v31.4h, v24.4h                                        ; 0x000002E0, line  232
        smlal   v25.4s, v13.4h, v17.4h                                        ; 0x000002E4, line  233
        smlal2  v16.4s, v13.8h, v17.8h                                        ; 0x000002E8, line  234
        smlal2  v16.4s, v3.8h, v22.8h                                         ; 0x000002EC, line  235
        smlal   v25.4s, v3.4h, v22.4h                                         ; 0x000002F0, line  236
        smlal2  v23.4s, v13.8h, v22.8h                                        ; 0x000002F4, line  237
        smlal   v26.4s, v29.4h, v24.4h                                        ; 0x000002F8, line  238
        smlal   v26.4s, v31.4h, v9.4h                                         ; 0x000002FC, line  239
        smlal   v26.4s, v13.4h, v22.4h                                        ; 0x00000300, line  240
        uzp1    v10.8h, v25.8h, v16.8h                                        ; 0x00000304, line  241
        smlal2  v23.4s, v3.8h, v4.8h                                          ; 0x00000308, line  242
        smlal   v26.4s, v3.4h, v4.4h                                          ; 0x0000030C, line  243
        mul     v13.8h, v10.8h, v2.8h                                         ; 0x00000310, line  244
        smlal   v18.4s, v14.4h, v0.4h                                         ; 0x00000314, line  245
        smlal2  v8.4s, v14.8h, v0.8h                                          ; 0x00000318, line  246
        uzp1    v3.8h, v26.8h, v23.8h                                         ; 0x0000031C, line  247
        mul     v24.8h, v3.8h, v2.8h                                          ; 0x00000320, line  248
        uzp2    v17.8h, v18.8h, v8.8h                                         ; 0x00000324, line  249
        smlal   v25.4s, v13.4h, v0.4h                                         ; 0x00000328, line  250
        smlal2  v16.4s, v13.8h, v0.8h                                         ; 0x0000032C, line  251
        zip1    v21.8h, v7.8h, v17.8h                                         ; 0x00000330, line  252
        zip2    v20.8h, v7.8h, v17.8h                                         ; 0x00000334, line  253
        smlal2  v23.4s, v24.8h, v0.8h                                         ; 0x00000338, line  254
        str     q21, [x0], #0x20                                              ; 0x0000033C, line  255
        smlal   v26.4s, v24.4h, v0.4h                                         ; 0x00000340, line  256
        uzp2    v13.8h, v25.8h, v16.8h                                        ; 0x00000344, line  257
        stur    q20, [x0, #-0x10]                                             ; 0x00000348, line  258
        uzp2    v23.8h, v26.8h, v23.8h                                        ; 0x0000034C, line  259
        zip1    v18.8h, v23.8h, v13.8h                                        ; 0x00000350, line  260
        zip2    v13.8h, v23.8h, v13.8h                                        ; 0x00000354, line  261
        str     q18, [x0], #0x20                                              ; 0x00000358, line  262
        stur    q13, [x0, #-0x10]                                             ; 0x0000035C, line  263
        ldp     d8, d9, [sp]                                                  ; 0x00000360, line  264
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp     d10, d11, [sp, #0x10]                                         ; 0x00000364, line  267
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp     d12, d13, [sp, #0x20]                                         ; 0x00000368, line  270
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp     d14, d15, [sp, #0x30]                                         ; 0x0000036C, line  273
        ; .cfi_restore d14
        ; .cfi_restore d15
        add     sp, sp, #0x40                                                 ; 0x00000370, line  276
        ; .cfi_adjust_cfa_offset -0x40
        ret                                                                   ; 0x00000374, line  278
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000378 byte(s)

        AREA    |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD     0x182000DE                                                    ; header dword
        DCB     0xD9, 0x86                                                    ; unwind code 'save_fregp', registers d14,d15 at stack offset 0x0030
        DCB     0xD9, 0x04                                                    ; unwind code 'save_fregp', registers d12,d13 at stack offset 0x0020
        DCB     0xD8, 0x82                                                    ; unwind code 'save_fregp', registers d10,d11 at stack offset 0x0010
        DCB     0xD8, 0x00                                                    ; unwind code 'save_fregp', registers d8,d9 at stack offset 0x0000
        DCB     0x04                                                          ; unwind code 'alloc_s', stack space 0x0040
        DCB     0xE4                                                          ; unwind code 'end'
        DCB     0x00, 0x00                                                    ; unwind code padding

        AREA    |.pdata|, DATA, READONLY, ALIGN=4

        DCD     $FUNC_NAME                                                    ; function start RVA
        DCD     XDATA_$FUNC_NAME                                              ; pointer in XDATA section

        END
