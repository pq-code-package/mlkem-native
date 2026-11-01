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
; Name: polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm
; Description: Re-implementation of asymmetric base multiplication following @[NeonNTT] for k=4
; Signature: void mlk_polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm(int16_t r[256], const int16_t a[1024], const int16_t b[1024], const int16_t b_cache[512])
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
;     size_bytes: 2048
;     permissions: read-only
;     c_parameter: const int16_t a[1024]
;     description: Input polynomial vector a
;   x2:
;     type: buffer
;     size_bytes: 2048
;     permissions: read-only
;     c_parameter: const int16_t b[1024]
;     description: Input polynomial vector b
;   x3:
;     type: buffer
;     size_bytes: 1024
;     permissions: read-only
;     c_parameter: const int16_t b_cache[512]
;     description: Cached values for b
; Stack:
;   bytes: 64
;   description: saving callee-saved Neon registers
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm"
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
        add     x10, x1, #0x600                                               ; 0x0000003C, line   63
        add     x11, x2, #0x600                                               ; 0x00000040, line   64
        add     x12, x3, #0x300                                               ; 0x00000044, line   65
        mov     x13, #0x10                                                    ; 0x00000048, line   66
        ldr     q28, [x1], #0x20                                              ; 0x0000004C, line   67
        ldur    q5, [x1, #-0x10]                                              ; 0x00000050, line   68
        ldr     q31, [x2], #0x20                                              ; 0x00000054, line   69
        ldur    q27, [x2, #-0x10]                                             ; 0x00000058, line   70
        ldr     q7, [x5], #0x20                                               ; 0x0000005C, line   71
        ldr     q10, [x4], #0x20                                              ; 0x00000060, line   72
        ldur    q18, [x5, #-0x10]                                             ; 0x00000064, line   73
        ldur    q9, [x4, #-0x10]                                              ; 0x00000068, line   74
        uzp1    v11.8h, v28.8h, v5.8h                                         ; 0x0000006C, line   75
        uzp2    v19.8h, v28.8h, v5.8h                                         ; 0x00000070, line   76
        uzp2    v4.8h, v31.8h, v27.8h                                         ; 0x00000074, line   77
        uzp1    v1.8h, v31.8h, v27.8h                                         ; 0x00000078, line   78
        ldr     q29, [x7], #0x20                                              ; 0x0000007C, line   79
        ldr     q28, [x8, #0x10]                                              ; 0x00000080, line   80
        uzp1    v24.8h, v10.8h, v9.8h                                         ; 0x00000084, line   81
        uzp1    v17.8h, v7.8h, v18.8h                                         ; 0x00000088, line   82
        uzp2    v7.8h, v7.8h, v18.8h                                          ; 0x0000008C, line   83
        ldr     q21, [x8], #0x20                                              ; 0x00000090, line   84
        uzp2    v27.8h, v10.8h, v9.8h                                         ; 0x00000094, line   85
        ldur    q6, [x7, #-0x10]                                              ; 0x00000098, line   86
        smull   v18.4s, v11.4h, v4.4h                                         ; 0x0000009C, line   87
        ld1     { v9.8h }, [x3], #16                                          ; 0x000000A0, line   88
        smull2  v8.4s, v11.8h, v4.8h                                          ; 0x000000A4, line   89
        ldr     q16, [x11], #0x20                                             ; 0x000000A8, line   90
        smlal2  v8.4s, v19.8h, v1.8h                                          ; 0x000000AC, line   91
        ldur    q14, [x11, #-0x10]                                            ; 0x000000B0, line   92
        smlal   v18.4s, v19.4h, v1.4h                                         ; 0x000000B4, line   93
        uzp1    v10.8h, v21.8h, v28.8h                                        ; 0x000000B8, line   94
        smlal   v18.4s, v24.4h, v7.4h                                         ; 0x000000BC, line   95
        ldr     q4, [x10], #0x20                                              ; 0x000000C0, line   96
        smlal2  v8.4s, v24.8h, v7.8h                                          ; 0x000000C4, line   97
        ld1     { v12.8h }, [x6], #16                                         ; 0x000000C8, line   98
        smull2  v23.4s, v11.8h, v1.8h                                         ; 0x000000CC, line   99
        uzp2    v13.8h, v29.8h, v6.8h                                         ; 0x000000D0, line  100
        smull   v26.4s, v11.4h, v1.4h                                         ; 0x000000D4, line  101
        uzp1    v29.8h, v29.8h, v6.8h                                         ; 0x000000D8, line  102
        smlal   v26.4s, v19.4h, v9.4h                                         ; 0x000000DC, line  103
        ldur    q15, [x10, #-0x10]                                            ; 0x000000E0, line  104
        smlal2  v23.4s, v19.8h, v9.8h                                         ; 0x000000E4, line  105
        uzp2    v9.8h, v21.8h, v28.8h                                         ; 0x000000E8, line  106
        smlal   v18.4s, v27.4h, v17.4h                                        ; 0x000000EC, line  107
        uzp2    v6.8h, v16.8h, v14.8h                                         ; 0x000000F0, line  108
        uzp1    v21.8h, v16.8h, v14.8h                                        ; 0x000000F4, line  109
        smlal2  v8.4s, v27.8h, v17.8h                                         ; 0x000000F8, line  110
        smlal2  v8.4s, v29.8h, v9.8h                                          ; 0x000000FC, line  111
        uzp1    v30.8h, v4.8h, v15.8h                                         ; 0x00000100, line  112
        uzp2    v16.8h, v4.8h, v15.8h                                         ; 0x00000104, line  113
        smlal   v18.4s, v29.4h, v9.4h                                         ; 0x00000108, line  114
        smlal2  v8.4s, v13.8h, v10.8h                                         ; 0x0000010C, line  115
        ld1     { v15.8h }, [x9], #16                                         ; 0x00000110, line  116
        smlal   v18.4s, v13.4h, v10.4h                                        ; 0x00000114, line  117
        ldr     q11, [x4], #0x20                                              ; 0x00000118, line  118
        smlal   v18.4s, v30.4h, v6.4h                                         ; 0x0000011C, line  119
        ldr     q7, [x2], #0x20                                               ; 0x00000120, line  120
        smlal2  v8.4s, v30.8h, v6.8h                                          ; 0x00000124, line  121
        ld1     { v9.8h }, [x12], #16                                         ; 0x00000128, line  122
        smlal2  v23.4s, v24.8h, v17.8h                                        ; 0x0000012C, line  123
        ldur    q4, [x2, #-0x10]                                              ; 0x00000130, line  124
        smlal   v26.4s, v24.4h, v17.4h                                        ; 0x00000134, line  125
        ldur    q25, [x4, #-0x10]                                             ; 0x00000138, line  126
        smlal2  v8.4s, v16.8h, v21.8h                                         ; 0x0000013C, line  127
        ldr     q5, [x5], #0x20                                               ; 0x00000140, line  128
        smlal   v18.4s, v16.4h, v21.4h                                        ; 0x00000144, line  129
        ldur    q22, [x5, #-0x10]                                             ; 0x00000148, line  130
        smlal   v26.4s, v27.4h, v12.4h                                        ; 0x0000014C, line  131
        ldr     q19, [x1, #0x10]                                              ; 0x00000150, line  132
        smlal   v26.4s, v29.4h, v10.4h                                        ; 0x00000154, line  133
        ld1     { v20.8h }, [x3], #16                                         ; 0x00000158, line  134
        smlal   v26.4s, v13.4h, v15.4h                                        ; 0x0000015C, line  135
        uzp1    v24.8h, v7.8h, v4.8h                                          ; 0x00000160, line  136
        smlal2  v23.4s, v27.8h, v12.8h                                        ; 0x00000164, line  137
        uzp1    v28.8h, v18.8h, v8.8h                                         ; 0x00000168, line  138
        smlal   v26.4s, v30.4h, v21.4h                                        ; 0x0000016C, line  139
        uzp2    v27.8h, v11.8h, v25.8h                                        ; 0x00000170, line  140
        smlal2  v23.4s, v29.8h, v10.8h                                        ; 0x00000174, line  141
        uzp2    v31.8h, v7.8h, v4.8h                                          ; 0x00000178, line  142
        smlal2  v23.4s, v13.8h, v15.8h                                        ; 0x0000017C, line  143
        uzp1    v14.8h, v5.8h, v22.8h                                         ; 0x00000180, line  144
        uzp1    v17.8h, v11.8h, v25.8h                                        ; 0x00000184, line  145
        smlal   v26.4s, v16.4h, v9.4h                                         ; 0x00000188, line  146
        mul     v29.8h, v28.8h, v2.8h                                         ; 0x0000018C, line  147
        sub     x13, x13, #0x2                                                ; 0x00000190, line  148
        HINT    #0x0                                                          ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                                          ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                                          ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmlk_polyvec_basemul_acc_montgomery_cached_k4_loop_start

        smlal2  v23.4s, v30.8h, v21.8h                                        ; 0x000001A0, line  151
        ldr     q11, [x1], #0x20                                              ; 0x000001A4, line  152
        uzp2    v15.8h, v5.8h, v22.8h                                         ; 0x000001A8, line  153
        smlal   v18.4s, v29.4h, v0.4h                                         ; 0x000001AC, line  154
        ldr     q12, [x7], #0x20                                              ; 0x000001B0, line  155
        smlal2  v8.4s, v29.8h, v0.8h                                          ; 0x000001B4, line  156
        ldur    q3, [x7, #-0x10]                                              ; 0x000001B8, line  157
        ldr     q21, [x8], #0x20                                              ; 0x000001BC, line  158
        uzp1    v29.8h, v11.8h, v19.8h                                        ; 0x000001C0, line  159
        ldur    q13, [x8, #-0x10]                                             ; 0x000001C4, line  160
        uzp2    v5.8h, v11.8h, v19.8h                                         ; 0x000001C8, line  161
        smlal2  v23.4s, v16.8h, v9.8h                                         ; 0x000001CC, line  162
        uzp2    v28.8h, v18.8h, v8.8h                                         ; 0x000001D0, line  163
        smull2  v8.4s, v29.8h, v31.8h                                         ; 0x000001D4, line  164
        smlal2  v8.4s, v5.8h, v24.8h                                          ; 0x000001D8, line  165
        uzp1    v7.8h, v12.8h, v3.8h                                          ; 0x000001DC, line  166
        smlal2  v8.4s, v17.8h, v15.8h                                         ; 0x000001E0, line  167
        uzp2    v11.8h, v21.8h, v13.8h                                        ; 0x000001E4, line  168
        uzp1    v4.8h, v26.8h, v23.8h                                         ; 0x000001E8, line  169
        smlal2  v8.4s, v27.8h, v14.8h                                         ; 0x000001EC, line  170
        smlal2  v8.4s, v7.8h, v11.8h                                          ; 0x000001F0, line  171
        mul     v6.8h, v4.8h, v2.8h                                           ; 0x000001F4, line  172
        ldr     q19, [x11], #0x20                                             ; 0x000001F8, line  173
        uzp2    v25.8h, v12.8h, v3.8h                                         ; 0x000001FC, line  174
        ldr     q12, [x10], #0x20                                             ; 0x00000200, line  175
        smull   v18.4s, v29.4h, v31.4h                                        ; 0x00000204, line  176
        ldur    q3, [x10, #-0x10]                                             ; 0x00000208, line  177
        smlal   v18.4s, v5.4h, v24.4h                                         ; 0x0000020C, line  178
        uzp1    v4.8h, v21.8h, v13.8h                                         ; 0x00000210, line  179
        smlal   v18.4s, v17.4h, v15.4h                                        ; 0x00000214, line  180
        ldur    q13, [x11, #-0x10]                                            ; 0x00000218, line  181
        ld1     { v1.8h }, [x6], #16                                          ; 0x0000021C, line  182
        smlal   v26.4s, v6.4h, v0.4h                                          ; 0x00000220, line  183
        smlal2  v23.4s, v6.8h, v0.8h                                          ; 0x00000224, line  184
        ld1     { v10.8h }, [x9], #16                                         ; 0x00000228, line  185
        smlal   v18.4s, v27.4h, v14.4h                                        ; 0x0000022C, line  186
        uzp1    v30.8h, v12.8h, v3.8h                                         ; 0x00000230, line  187
        smlal2  v8.4s, v25.8h, v4.8h                                          ; 0x00000234, line  188
        uzp2    v31.8h, v19.8h, v13.8h                                        ; 0x00000238, line  189
        smlal   v18.4s, v7.4h, v11.4h                                         ; 0x0000023C, line  190
        ld1     { v9.8h }, [x12], #16                                         ; 0x00000240, line  191
        smlal   v18.4s, v25.4h, v4.4h                                         ; 0x00000244, line  192
        uzp1    v21.8h, v19.8h, v13.8h                                        ; 0x00000248, line  193
        uzp2    v16.8h, v12.8h, v3.8h                                         ; 0x0000024C, line  194
        smlal   v18.4s, v30.4h, v31.4h                                        ; 0x00000250, line  195
        smlal2  v8.4s, v30.8h, v31.8h                                         ; 0x00000254, line  196
        uzp2    v31.8h, v26.8h, v23.8h                                        ; 0x00000258, line  197
        smlal2  v8.4s, v16.8h, v21.8h                                         ; 0x0000025C, line  198
        smlal   v18.4s, v16.4h, v21.4h                                        ; 0x00000260, line  199
        zip1    v15.8h, v31.8h, v28.8h                                        ; 0x00000264, line  200
        ldr     q19, [x1, #0x10]                                              ; 0x00000268, line  201
        smull2  v23.4s, v29.8h, v24.8h                                        ; 0x0000026C, line  202
        smull   v26.4s, v29.4h, v24.4h                                        ; 0x00000270, line  203
        ldr     q3, [x2, #0x10]                                               ; 0x00000274, line  204
        smlal   v26.4s, v5.4h, v20.4h                                         ; 0x00000278, line  205
        ldr     q11, [x2], #0x20                                              ; 0x0000027C, line  206
        uzp1    v6.8h, v18.8h, v8.8h                                          ; 0x00000280, line  207
        smlal   v26.4s, v17.4h, v14.4h                                        ; 0x00000284, line  208
        smlal   v26.4s, v27.4h, v1.4h                                         ; 0x00000288, line  209
        zip2    v13.8h, v31.8h, v28.8h                                        ; 0x0000028C, line  210
        smlal   v26.4s, v7.4h, v4.4h                                          ; 0x00000290, line  211
        str     q15, [x0], #0x20                                              ; 0x00000294, line  212
        smlal   v26.4s, v25.4h, v10.4h                                        ; 0x00000298, line  213
        stur    q13, [x0, #-0x10]                                             ; 0x0000029C, line  214
        mul     v29.8h, v6.8h, v2.8h                                          ; 0x000002A0, line  215
        uzp1    v24.8h, v11.8h, v3.8h                                         ; 0x000002A4, line  216
        uzp2    v31.8h, v11.8h, v3.8h                                         ; 0x000002A8, line  217
        ldr     q11, [x4], #0x20                                              ; 0x000002AC, line  218
        smlal2  v23.4s, v5.8h, v20.8h                                         ; 0x000002B0, line  219
        ldur    q28, [x4, #-0x10]                                             ; 0x000002B4, line  220
        smlal2  v23.4s, v17.8h, v14.8h                                        ; 0x000002B8, line  221
        ldr     q5, [x5], #0x20                                               ; 0x000002BC, line  222
        smlal2  v23.4s, v27.8h, v1.8h                                         ; 0x000002C0, line  223
        ldur    q22, [x5, #-0x10]                                             ; 0x000002C4, line  224
        smlal   v26.4s, v30.4h, v21.4h                                        ; 0x000002C8, line  225
        ld1     { v20.8h }, [x3], #16                                         ; 0x000002CC, line  226
        smlal   v26.4s, v16.4h, v9.4h                                         ; 0x000002D0, line  227
        uzp1    v17.8h, v11.8h, v28.8h                                        ; 0x000002D4, line  228
        smlal2  v23.4s, v7.8h, v4.8h                                          ; 0x000002D8, line  229
        uzp2    v27.8h, v11.8h, v28.8h                                        ; 0x000002DC, line  230
        smlal2  v23.4s, v25.8h, v10.8h                                        ; 0x000002E0, line  231
        uzp1    v14.8h, v5.8h, v22.8h                                         ; 0x000002E4, line  232
        subs    x13, x13, #0x1                                                ; 0x000002E8, line  233
        cbnz    x13, Lmlk_polyvec_basemul_acc_montgomery_cached_k4_loop_start ; 0x000002EC, line  234
        smlal   v18.4s, v29.4h, v0.4h                                         ; 0x000002F0, line  235
        ldr     q11, [x1], #0x20                                              ; 0x000002F4, line  236
        uzp2    v28.8h, v5.8h, v22.8h                                         ; 0x000002F8, line  237
        smlal2  v23.4s, v30.8h, v21.8h                                        ; 0x000002FC, line  238
        smlal2  v8.4s, v29.8h, v0.8h                                          ; 0x00000300, line  239
        ldr     q15, [x8, #0x10]                                              ; 0x00000304, line  240
        smlal2  v23.4s, v16.8h, v9.8h                                         ; 0x00000308, line  241
        ldr     q21, [x8], #0x20                                              ; 0x0000030C, line  242
        uzp1    v22.8h, v11.8h, v19.8h                                        ; 0x00000310, line  243
        uzp2    v12.8h, v11.8h, v19.8h                                        ; 0x00000314, line  244
        ldr     q1, [x7, #0x10]                                               ; 0x00000318, line  245
        ld1     { v6.8h }, [x6], #16                                          ; 0x0000031C, line  246
        uzp2    v3.8h, v18.8h, v8.8h                                          ; 0x00000320, line  247
        smull   v9.4s, v22.4h, v31.4h                                         ; 0x00000324, line  248
        smull2  v18.4s, v22.8h, v31.8h                                        ; 0x00000328, line  249
        ldr     q16, [x7], #0x20                                              ; 0x0000032C, line  250
        smull   v19.4s, v22.4h, v24.4h                                        ; 0x00000330, line  251
        uzp1    v30.8h, v21.8h, v15.8h                                        ; 0x00000334, line  252
        uzp2    v25.8h, v21.8h, v15.8h                                        ; 0x00000338, line  253
        smull2  v8.4s, v22.8h, v24.8h                                         ; 0x0000033C, line  254
        smlal   v19.4s, v12.4h, v20.4h                                        ; 0x00000340, line  255
        ldr     q13, [x10, #0x10]                                             ; 0x00000344, line  256
        smlal2  v8.4s, v12.8h, v20.8h                                         ; 0x00000348, line  257
        uzp1    v29.8h, v16.8h, v1.8h                                         ; 0x0000034C, line  258
        smlal2  v18.4s, v12.8h, v24.8h                                        ; 0x00000350, line  259
        ldr     q5, [x10], #0x20                                              ; 0x00000354, line  260
        smlal   v9.4s, v12.4h, v24.4h                                         ; 0x00000358, line  261
        ldr     q4, [x11], #0x20                                              ; 0x0000035C, line  262
        smlal   v9.4s, v17.4h, v28.4h                                         ; 0x00000360, line  263
        ldur    q22, [x11, #-0x10]                                            ; 0x00000364, line  264
        smlal2  v18.4s, v17.8h, v28.8h                                        ; 0x00000368, line  265
        uzp2    v16.8h, v16.8h, v1.8h                                         ; 0x0000036C, line  266
        smlal   v19.4s, v17.4h, v14.4h                                        ; 0x00000370, line  267
        ld1     { v28.8h }, [x9], #16                                         ; 0x00000374, line  268
        smlal2  v8.4s, v17.8h, v14.8h                                         ; 0x00000378, line  269
        uzp1    v7.8h, v5.8h, v13.8h                                          ; 0x0000037C, line  270
        smlal   v9.4s, v27.4h, v14.4h                                         ; 0x00000380, line  271
        uzp1    v17.8h, v4.8h, v22.8h                                         ; 0x00000384, line  272
        smlal2  v18.4s, v27.8h, v14.8h                                        ; 0x00000388, line  273
        uzp2    v12.8h, v5.8h, v13.8h                                         ; 0x0000038C, line  274
        uzp2    v21.8h, v4.8h, v22.8h                                         ; 0x00000390, line  275
        smlal   v19.4s, v27.4h, v6.4h                                         ; 0x00000394, line  276
        smlal2  v8.4s, v27.8h, v6.8h                                          ; 0x00000398, line  277
        ld1     { v15.8h }, [x12], #16                                        ; 0x0000039C, line  278
        smlal   v19.4s, v29.4h, v30.4h                                        ; 0x000003A0, line  279
        uzp1    v20.8h, v26.8h, v23.8h                                        ; 0x000003A4, line  280
        smlal   v9.4s, v29.4h, v25.4h                                         ; 0x000003A8, line  281
        smlal2  v18.4s, v29.8h, v25.8h                                        ; 0x000003AC, line  282
        smlal2  v8.4s, v29.8h, v30.8h                                         ; 0x000003B0, line  283
        smlal   v19.4s, v16.4h, v28.4h                                        ; 0x000003B4, line  284
        smlal2  v8.4s, v16.8h, v28.8h                                         ; 0x000003B8, line  285
        smlal2  v18.4s, v16.8h, v30.8h                                        ; 0x000003BC, line  286
        smlal   v9.4s, v16.4h, v30.4h                                         ; 0x000003C0, line  287
        smlal   v9.4s, v7.4h, v21.4h                                          ; 0x000003C4, line  288
        smlal2  v18.4s, v7.8h, v21.8h                                         ; 0x000003C8, line  289
        smlal2  v8.4s, v7.8h, v17.8h                                          ; 0x000003CC, line  290
        smlal   v19.4s, v7.4h, v17.4h                                         ; 0x000003D0, line  291
        smlal   v19.4s, v12.4h, v15.4h                                        ; 0x000003D4, line  292
        smlal2  v8.4s, v12.8h, v15.8h                                         ; 0x000003D8, line  293
        smlal2  v18.4s, v12.8h, v17.8h                                        ; 0x000003DC, line  294
        smlal   v9.4s, v12.4h, v17.4h                                         ; 0x000003E0, line  295
        mul     v6.8h, v20.8h, v2.8h                                          ; 0x000003E4, line  296
        uzp1    v4.8h, v19.8h, v8.8h                                          ; 0x000003E8, line  297
        mul     v17.8h, v4.8h, v2.8h                                          ; 0x000003EC, line  298
        uzp1    v12.8h, v9.8h, v18.8h                                         ; 0x000003F0, line  299
        smlal   v26.4s, v6.4h, v0.4h                                          ; 0x000003F4, line  300
        mul     v21.8h, v12.8h, v2.8h                                         ; 0x000003F8, line  301
        smlal2  v23.4s, v6.8h, v0.8h                                          ; 0x000003FC, line  302
        smlal2  v8.4s, v17.8h, v0.8h                                          ; 0x00000400, line  303
        smlal   v19.4s, v17.4h, v0.4h                                         ; 0x00000404, line  304
        smlal2  v18.4s, v21.8h, v0.8h                                         ; 0x00000408, line  305
        uzp2    v23.8h, v26.8h, v23.8h                                        ; 0x0000040C, line  306
        smlal   v9.4s, v21.4h, v0.4h                                          ; 0x00000410, line  307
        zip2    v12.8h, v23.8h, v3.8h                                         ; 0x00000414, line  308
        zip1    v22.8h, v23.8h, v3.8h                                         ; 0x00000418, line  309
        uzp2    v14.8h, v19.8h, v8.8h                                         ; 0x0000041C, line  310
        uzp2    v18.8h, v9.8h, v18.8h                                         ; 0x00000420, line  311
        str     q12, [x0, #0x10]                                              ; 0x00000424, line  312
        str     q22, [x0], #0x20                                              ; 0x00000428, line  313
        zip2    v24.8h, v14.8h, v18.8h                                        ; 0x0000042C, line  314
        zip1    v21.8h, v14.8h, v18.8h                                        ; 0x00000430, line  315
        str     q24, [x0, #0x10]                                              ; 0x00000434, line  316
        str     q21, [x0], #0x20                                              ; 0x00000438, line  317
        ldp     d8, d9, [sp]                                                  ; 0x0000043C, line  318
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp     d10, d11, [sp, #0x10]                                         ; 0x00000440, line  321
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp     d12, d13, [sp, #0x20]                                         ; 0x00000444, line  324
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp     d14, d15, [sp, #0x30]                                         ; 0x00000448, line  327
        ; .cfi_restore d14
        ; .cfi_restore d15
        add     sp, sp, #0x40                                                 ; 0x0000044C, line  330
        ; .cfi_adjust_cfa_offset -0x40
        ret                                                                   ; 0x00000450, line  332
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000454 byte(s)

        AREA    |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD     0x18200115                                                    ; header dword
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
