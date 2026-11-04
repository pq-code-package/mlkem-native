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
; Name: keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm
; Description: AArch64 hybrid scalar/vector implementation of Keccak-f[1600] permutation for four sequential states
; Signature: void mld_keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm(uint64_t state[100], const uint64_t rc[24])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON]
;   x0:
;     type: buffer
;     size_bytes: 800
;     permissions: read/write
;     c_parameter: uint64_t state[100]
;     description: Four sequential Keccak states (state0[25], state1[25], state2[25], state3[25])
;   x1:
;     type: buffer
;     size_bytes: 192
;     permissions: read-only
;     c_parameter: uint64_t const *rc
;     description: Round constants (24 x uint64_t)
; Stack:
;   bytes: 224
;   description: register preservation and temporary storage
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm"
        ENDIF

        AREA    |.drectve|, DRECTVE

        EXPORT  $FUNC_NAME

        AREA    |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN   16

$FUNC_NAME PROC

        ; .cfi_startproc
        sub     sp, sp, #0xe0                                  ; 0x00000000, line   27
        ; .cfi_adjust_cfa_offset 0xE0
        stp     x19, x20, [sp, #0x30]                          ; 0x00000004, line   29
        ; .cfi_rel_offset x19, 0x30
        ; .cfi_rel_offset x20, 0x38
        stp     x21, x22, [sp, #0x40]                          ; 0x00000008, line   32
        ; .cfi_rel_offset x21, 0x40
        ; .cfi_rel_offset x22, 0x48
        stp     x23, x24, [sp, #0x50]                          ; 0x0000000C, line   35
        ; .cfi_rel_offset x23, 0x50
        ; .cfi_rel_offset x24, 0x58
        stp     x25, x26, [sp, #0x60]                          ; 0x00000010, line   38
        ; .cfi_rel_offset x25, 0x60
        ; .cfi_rel_offset x26, 0x68
        stp     x27, x28, [sp, #0x70]                          ; 0x00000014, line   41
        ; .cfi_rel_offset x27, 0x70
        ; .cfi_rel_offset x28, 0x78
        stp     x29, x30, [sp, #0x80]                          ; 0x00000018, line   44
        ; .cfi_rel_offset x29, 0x80
        ; .cfi_rel_offset x30, 0x88
        stp     d8, d9, [sp, #0x90]                            ; 0x0000001C, line   47
        ; .cfi_rel_offset d8, 0x90
        ; .cfi_rel_offset d9, 0x98
        stp     d10, d11, [sp, #0xa0]                          ; 0x00000020, line   50
        ; .cfi_rel_offset d10, 0xA0
        ; .cfi_rel_offset d11, 0xA8
        stp     d12, d13, [sp, #0xb0]                          ; 0x00000024, line   53
        ; .cfi_rel_offset d12, 0xB0
        ; .cfi_rel_offset d13, 0xB8
        stp     d14, d15, [sp, #0xc0]                          ; 0x00000028, line   56
        ; .cfi_rel_offset d14, 0xC0
        ; .cfi_rel_offset d15, 0xC8
        mov     x29, x1                                        ; 0x0000002C, line   59
        mov     x30, #0x0                                      ; 0x00000030, line   60
        str     x30, [sp, #0x20]                               ; 0x00000034, line   61
        str     x29, [sp, #0x8]                                ; 0x00000038, line   62
        str     x29, [sp, #0x10]                               ; 0x0000003C, line   63
        str     x0, [sp]                                       ; 0x00000040, line   64
        add     x4, x0, #0xc8                                  ; 0x00000044, line   65
        ldp     q25, q26, [x0], #0x20                          ; 0x00000048, line   66
        ld1     { v27.2d, v28.2d }, [x4], #32                  ; 0x0000004C, line   67
        trn1    v0.2d, v25.2d, v27.2d                          ; 0x00000050, line   68
        trn2    v1.2d, v25.2d, v27.2d                          ; 0x00000054, line   69
        trn1    v2.2d, v26.2d, v28.2d                          ; 0x00000058, line   70
        trn2    v3.2d, v26.2d, v28.2d                          ; 0x0000005C, line   71
        ldp     q25, q26, [x0], #0x20                          ; 0x00000060, line   72
        ld1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000064, line   73
        trn1    v4.2d, v25.2d, v27.2d                          ; 0x00000068, line   74
        trn2    v5.2d, v25.2d, v27.2d                          ; 0x0000006C, line   75
        trn1    v6.2d, v26.2d, v28.2d                          ; 0x00000070, line   76
        trn2    v7.2d, v26.2d, v28.2d                          ; 0x00000074, line   77
        ldp     q25, q26, [x0], #0x20                          ; 0x00000078, line   78
        ld1     { v27.2d, v28.2d }, [x4], #32                  ; 0x0000007C, line   79
        trn1    v8.2d, v25.2d, v27.2d                          ; 0x00000080, line   80
        trn2    v9.2d, v25.2d, v27.2d                          ; 0x00000084, line   81
        trn1    v10.2d, v26.2d, v28.2d                         ; 0x00000088, line   82
        trn2    v11.2d, v26.2d, v28.2d                         ; 0x0000008C, line   83
        ldp     q25, q26, [x0], #0x20                          ; 0x00000090, line   84
        ld1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000094, line   85
        trn1    v12.2d, v25.2d, v27.2d                         ; 0x00000098, line   86
        trn2    v13.2d, v25.2d, v27.2d                         ; 0x0000009C, line   87
        trn1    v14.2d, v26.2d, v28.2d                         ; 0x000000A0, line   88
        trn2    v15.2d, v26.2d, v28.2d                         ; 0x000000A4, line   89
        ldp     q25, q26, [x0], #0x20                          ; 0x000000A8, line   90
        ld1     { v27.2d, v28.2d }, [x4], #32                  ; 0x000000AC, line   91
        trn1    v16.2d, v25.2d, v27.2d                         ; 0x000000B0, line   92
        trn2    v17.2d, v25.2d, v27.2d                         ; 0x000000B4, line   93
        trn1    v18.2d, v26.2d, v28.2d                         ; 0x000000B8, line   94
        trn2    v19.2d, v26.2d, v28.2d                         ; 0x000000BC, line   95
        ldp     q25, q26, [x0], #0x20                          ; 0x000000C0, line   96
        ld1     { v27.2d, v28.2d }, [x4], #32                  ; 0x000000C4, line   97
        trn1    v20.2d, v25.2d, v27.2d                         ; 0x000000C8, line   98
        trn2    v21.2d, v25.2d, v27.2d                         ; 0x000000CC, line   99
        trn1    v22.2d, v26.2d, v28.2d                         ; 0x000000D0, line  100
        trn2    v23.2d, v26.2d, v28.2d                         ; 0x000000D4, line  101
        ldr     d25, [x0]                                      ; 0x000000D8, line  102
        ldr     d27, [x4]                                      ; 0x000000DC, line  103
        trn1    v24.2d, v25.2d, v27.2d                         ; 0x000000E0, line  104
        sub     x0, x0, #0xc0                                  ; 0x000000E4, line  105
        add     x0, x0, #0x190                                 ; 0x000000E8, line  106
        ldp     x1, x6, [x0]                                   ; 0x000000EC, line  107
        ldp     x11, x16, [x0, #0x10]                          ; 0x000000F0, line  108
        ldp     x21, x2, [x0, #0x20]                           ; 0x000000F4, line  109
        ldp     x7, x12, [x0, #0x30]                           ; 0x000000F8, line  110
        ldp     x17, x22, [x0, #0x40]                          ; 0x000000FC, line  111
        ldp     x3, x8, [x0, #0x50]                            ; 0x00000100, line  112
        ldp     x13, x28, [x0, #0x60]                          ; 0x00000104, line  113
        ldp     x23, x4, [x0, #0x70]                           ; 0x00000108, line  114
        ldp     x9, x14, [x0, #0x80]                           ; 0x0000010C, line  115
        ldp     x19, x24, [x0, #0x90]                          ; 0x00000110, line  116
        ldp     x5, x10, [x0, #0xa0]                           ; 0x00000114, line  117
        ldp     x15, x20, [x0, #0xb0]                          ; 0x00000118, line  118
        ldr     x25, [x0, #0xc0]                               ; 0x0000011C, line  119
        sub     x0, x0, #0x190                                 ; 0x00000120, line  120
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x4_v8a_scalar_hybrid_initial

        eor     x30, x24, x25                                  ; 0x00000130, line  123
        eor     x27, x9, x10                                   ; 0x00000134, line  124
        eor     v30.16b, v0.16b, v5.16b                        ; 0x00000138, line  125
        eor     v30.16b, v30.16b, v10.16b                      ; 0x0000013C, line  126
        eor     x0, x30, x21                                   ; 0x00000140, line  127
        eor     v30.16b, v30.16b, v15.16b                      ; 0x00000144, line  128
        eor     x26, x27, x6                                   ; 0x00000148, line  129
        eor     x27, x26, x7                                   ; 0x0000014C, line  130
        eor     v30.16b, v30.16b, v20.16b                      ; 0x00000150, line  131
        eor     x29, x0, x22                                   ; 0x00000154, line  132
        eor     v29.16b, v1.16b, v6.16b                        ; 0x00000158, line  133
        eor     x26, x29, x23                                  ; 0x0000015C, line  134
        eor     v29.16b, v29.16b, v11.16b                      ; 0x00000160, line  135
        eor     x29, x4, x5                                    ; 0x00000164, line  136
        eor     x30, x29, x1                                   ; 0x00000168, line  137
        eor     v29.16b, v29.16b, v16.16b                      ; 0x0000016C, line  138
        eor     x0, x27, x8                                    ; 0x00000170, line  139
        eor     v29.16b, v29.16b, v21.16b                      ; 0x00000174, line  140
        eor     x29, x30, x2                                   ; 0x00000178, line  141
        eor     v28.16b, v2.16b, v7.16b                        ; 0x0000017C, line  142
        eor     x30, x19, x20                                  ; 0x00000180, line  143
        eor     x30, x30, x16                                  ; 0x00000184, line  144
        eor     v28.16b, v28.16b, v12.16b                      ; 0x00000188, line  145
        eor     x27, x26, x0, ror #63                          ; 0x0000018C, line  146
        eor     v28.16b, v28.16b, v17.16b                      ; 0x00000190, line  147
        eor     x4, x4, x27                                    ; 0x00000194, line  148
        eor     v28.16b, v28.16b, v22.16b                      ; 0x00000198, line  149
        eor     x30, x30, x17                                  ; 0x0000019C, line  150
        eor     x30, x30, x28                                  ; 0x000001A0, line  151
        eor     v27.16b, v3.16b, v8.16b                        ; 0x000001A4, line  152
        eor     x29, x29, x3                                   ; 0x000001A8, line  153
        eor     v27.16b, v27.16b, v13.16b                      ; 0x000001AC, line  154
        eor     x0, x0, x30, ror #63                           ; 0x000001B0, line  155
        eor     v27.16b, v27.16b, v18.16b                      ; 0x000001B4, line  156
        eor     x30, x30, x29, ror #63                         ; 0x000001B8, line  157
        eor     x22, x22, x30                                  ; 0x000001BC, line  158
        eor     v27.16b, v27.16b, v23.16b                      ; 0x000001C0, line  159
        eor     x23, x23, x30                                  ; 0x000001C4, line  160
        eor     v26.16b, v4.16b, v9.16b                        ; 0x000001C8, line  161
        str     x23, [sp, #0xd0]                               ; 0x000001CC, line  162
        eor     v26.16b, v26.16b, v14.16b                      ; 0x000001D0, line  163
        eor     x23, x14, x15                                  ; 0x000001D4, line  164
        eor     x14, x14, x0                                   ; 0x000001D8, line  165
        eor     v26.16b, v26.16b, v19.16b                      ; 0x000001DC, line  166
        eor     x23, x23, x11                                  ; 0x000001E0, line  167
        eor     v26.16b, v26.16b, v24.16b                      ; 0x000001E4, line  168
        eor     x15, x15, x0                                   ; 0x000001E8, line  169
        eor     x1, x1, x27                                    ; 0x000001EC, line  170
        add     v31.2d, v28.2d, v28.2d                         ; 0x000001F0, line  171
        eor     x23, x23, x12                                  ; 0x000001F4, line  172
        sri     v31.2d, v28.2d, #0x3f                          ; 0x000001F8, line  173
        eor     x23, x23, x13                                  ; 0x000001FC, line  174
        eor     v25.16b, v31.16b, v30.16b                      ; 0x00000200, line  175
        eor     x11, x11, x0                                   ; 0x00000204, line  176
        eor     x29, x29, x23, ror #63                         ; 0x00000208, line  177
        add     v31.2d, v26.2d, v26.2d                         ; 0x0000020C, line  178
        eor     x23, x23, x26, ror #63                         ; 0x00000210, line  179
        sri     v31.2d, v26.2d, #0x3f                          ; 0x00000214, line  180
        eor     x26, x13, x0                                   ; 0x00000218, line  181
        eor     v28.16b, v31.16b, v28.16b                      ; 0x0000021C, line  182
        eor     x13, x28, x23                                  ; 0x00000220, line  183
        eor     x28, x24, x30                                  ; 0x00000224, line  184
        add     v31.2d, v29.2d, v29.2d                         ; 0x00000228, line  185
        eor     x24, x16, x23                                  ; 0x0000022C, line  186
        sri     v31.2d, v29.2d, #0x3f                          ; 0x00000230, line  187
        eor     x16, x21, x30                                  ; 0x00000234, line  188
        eor     v26.16b, v31.16b, v26.16b                      ; 0x00000238, line  189
        eor     x21, x25, x30                                  ; 0x0000023C, line  190
        eor     x30, x19, x23                                  ; 0x00000240, line  191
        add     v31.2d, v27.2d, v27.2d                         ; 0x00000244, line  192
        eor     x19, x20, x23                                  ; 0x00000248, line  193
        sri     v31.2d, v27.2d, #0x3f                          ; 0x0000024C, line  194
        eor     x20, x17, x23                                  ; 0x00000250, line  195
        eor     v29.16b, v31.16b, v29.16b                      ; 0x00000254, line  196
        eor     x17, x12, x0                                   ; 0x00000258, line  197
        eor     x0, x2, x27                                    ; 0x0000025C, line  198
        add     v31.2d, v30.2d, v30.2d                         ; 0x00000260, line  199
        eor     x2, x6, x29                                    ; 0x00000264, line  200
        sri     v31.2d, v30.2d, #0x3f                          ; 0x00000268, line  201
        eor     x6, x8, x29                                    ; 0x0000026C, line  202
        eor     v27.16b, v31.16b, v27.16b                      ; 0x00000270, line  203
        bic     x8, x28, x13, ror #47                          ; 0x00000274, line  204
        eor     x12, x3, x27                                   ; 0x00000278, line  205
        eor     v30.16b, v0.16b, v26.16b                       ; 0x0000027C, line  206
        bic     x3, x13, x17, ror #19                          ; 0x00000280, line  207
        eor     v31.16b, v2.16b, v29.16b                       ; 0x00000284, line  208
        eor     x5, x5, x27                                    ; 0x00000288, line  209
        ldr     x27, [sp, #0xd0]                               ; 0x0000028C, line  210
        shl     v0.2d, v31.2d, #0x3e                           ; 0x00000290, line  211
        bic     x25, x17, x2, ror #5                           ; 0x00000294, line  212
        sri     v0.2d, v31.2d, #0x2                            ; 0x00000298, line  213
        eor     x9, x9, x29                                    ; 0x0000029C, line  214
        eor     v31.16b, v12.16b, v29.16b                      ; 0x000002A0, line  215
        eor     x23, x25, x5, ror #52                          ; 0x000002A4, line  216
        eor     x3, x3, x2, ror #24                            ; 0x000002A8, line  217
        shl     v2.2d, v31.2d, #0x2b                           ; 0x000002AC, line  218
        eor     x8, x8, x17, ror #2                            ; 0x000002B0, line  219
        sri     v2.2d, v31.2d, #0x15                           ; 0x000002B4, line  220
        eor     x17, x10, x29                                  ; 0x000002B8, line  221
        eor     v31.16b, v13.16b, v28.16b                      ; 0x000002BC, line  222
        bic     x25, x12, x22, ror #47                         ; 0x000002C0, line  223
        eor     x29, x7, x29                                   ; 0x000002C4, line  224
        shl     v12.2d, v31.2d, #0x19                          ; 0x000002C8, line  225
        bic     x10, x4, x27, ror #2                           ; 0x000002CC, line  226
        sri     v12.2d, v31.2d, #0x27                          ; 0x000002D0, line  227
        bic     x7, x5, x28, ror #10                           ; 0x000002D4, line  228
        eor     v31.16b, v19.16b, v27.16b                      ; 0x000002D8, line  229
        eor     x10, x10, x20, ror #50                         ; 0x000002DC, line  230
        eor     x13, x7, x13, ror #57                          ; 0x000002E0, line  231
        shl     v13.2d, v31.2d, #0x8                           ; 0x000002E4, line  232
        bic     x7, x2, x5, ror #47                            ; 0x000002E8, line  233
        sri     v13.2d, v31.2d, #0x38                          ; 0x000002EC, line  234
        eor     x2, x25, x24, ror #39                          ; 0x000002F0, line  235
        eor     v31.16b, v23.16b, v28.16b                      ; 0x000002F4, line  236
        bic     x25, x20, x11, ror #57                         ; 0x000002F8, line  237
        bic     x5, x17, x4, ror #25                           ; 0x000002FC, line  238
        shl     v19.2d, v31.2d, #0x38                          ; 0x00000300, line  239
        eor     x25, x25, x17, ror #53                         ; 0x00000304, line  240
        sri     v19.2d, v31.2d, #0x8                           ; 0x00000308, line  241
        bic     x17, x11, x17, ror #60                         ; 0x0000030C, line  242
        eor     v31.16b, v15.16b, v26.16b                      ; 0x00000310, line  243
        eor     x28, x7, x28, ror #57                          ; 0x00000314, line  244
        bic     x7, x9, x12, ror #42                           ; 0x00000318, line  245
        shl     v23.2d, v31.2d, #0x29                          ; 0x0000031C, line  246
        eor     x7, x7, x22, ror #25                           ; 0x00000320, line  247
        sri     v23.2d, v31.2d, #0x17                          ; 0x00000324, line  248
        bic     x22, x22, x24, ror #56                         ; 0x00000328, line  249
        bic     x24, x24, x15, ror #31                         ; 0x0000032C, line  250
        eor     v31.16b, v1.16b, v25.16b                       ; 0x00000330, line  251
        eor     x22, x22, x15, ror #23                         ; 0x00000334, line  252
        shl     v15.2d, v31.2d, #0x1                           ; 0x00000338, line  253
        bic     x20, x27, x20, ror #48                         ; 0x0000033C, line  254
        sri     v15.2d, v31.2d, #0x3f                          ; 0x00000340, line  255
        bic     x15, x15, x9, ror #16                          ; 0x00000344, line  256
        eor     x12, x15, x12, ror #58                         ; 0x00000348, line  257
        eor     v31.16b, v8.16b, v28.16b                       ; 0x0000034C, line  258
        eor     x15, x5, x27, ror #27                          ; 0x00000350, line  259
        shl     v1.2d, v31.2d, #0x37                           ; 0x00000354, line  260
        eor     x5, x20, x11, ror #41                          ; 0x00000358, line  261
        sri     v1.2d, v31.2d, #0x9                            ; 0x0000035C, line  262
        ldr     x11, [sp, #0x8]                                ; 0x00000360, line  263
        eor     x20, x17, x4, ror #21                          ; 0x00000364, line  264
        eor     v31.16b, v16.16b, v25.16b                      ; 0x00000368, line  265
        eor     x17, x24, x9, ror #47                          ; 0x0000036C, line  266
        shl     v8.2d, v31.2d, #0x2d                           ; 0x00000370, line  267
        mov     x24, #0x1                                      ; 0x00000374, line  268
        sri     v8.2d, v31.2d, #0x13                           ; 0x00000378, line  269
        bic     x9, x0, x16, ror #9                            ; 0x0000037C, line  270
        str     x24, [sp, #0x18]                               ; 0x00000380, line  271
        eor     v31.16b, v7.16b, v29.16b                       ; 0x00000384, line  272
        bic     x24, x29, x1, ror #44                          ; 0x00000388, line  273
        shl     v16.2d, v31.2d, #0x6                           ; 0x0000038C, line  274
        bic     x27, x1, x21, ror #50                          ; 0x00000390, line  275
        sri     v16.2d, v31.2d, #0x3a                          ; 0x00000394, line  276
        bic     x4, x26, x29, ror #63                          ; 0x00000398, line  277
        eor     x1, x1, x4, ror #21                            ; 0x0000039C, line  278
        eor     v31.16b, v10.16b, v26.16b                      ; 0x000003A0, line  279
        ldr     x11, [x11]                                     ; 0x000003A4, line  280
        shl     v7.2d, v31.2d, #0x3                            ; 0x000003A8, line  281
        bic     x4, x21, x30, ror #57                          ; 0x000003AC, line  282
        sri     v7.2d, v31.2d, #0x3d                           ; 0x000003B0, line  283
        eor     x21, x24, x21, ror #30                         ; 0x000003B4, line  284
        eor     x24, x9, x19, ror #44                          ; 0x000003B8, line  285
        eor     v31.16b, v3.16b, v28.16b                       ; 0x000003BC, line  286
        bic     x9, x14, x6, ror #5                            ; 0x000003C0, line  287
        shl     v10.2d, v31.2d, #0x1c                          ; 0x000003C4, line  288
        eor     x9, x9, x0, ror #43                            ; 0x000003C8, line  289
        sri     v10.2d, v31.2d, #0x24                          ; 0x000003CC, line  290
        bic     x0, x6, x0, ror #38                            ; 0x000003D0, line  291
        eor     x1, x1, x11                                    ; 0x000003D4, line  292
        eor     v31.16b, v18.16b, v28.16b                      ; 0x000003D8, line  293
        eor     x11, x4, x26, ror #35                          ; 0x000003DC, line  294
        shl     v3.2d, v31.2d, #0x15                           ; 0x000003E0, line  295
        eor     x4, x0, x16, ror #47                           ; 0x000003E4, line  296
        bic     x0, x16, x19, ror #35                          ; 0x000003E8, line  297
        sri     v3.2d, v31.2d, #0x2b                           ; 0x000003EC, line  298
        eor     x16, x27, x30, ror #43                         ; 0x000003F0, line  299
        eor     v31.16b, v17.16b, v29.16b                      ; 0x000003F4, line  300
        bic     x27, x30, x26, ror #42                         ; 0x000003F8, line  301
        shl     v18.2d, v31.2d, #0xf                           ; 0x000003FC, line  302
        bic     x26, x19, x14, ror #41                         ; 0x00000400, line  303
        eor     x19, x0, x14, ror #12                          ; 0x00000404, line  304
        sri     v18.2d, v31.2d, #0x31                          ; 0x00000408, line  305
        eor     x14, x26, x6, ror #46                          ; 0x0000040C, line  306
        eor     v31.16b, v11.16b, v25.16b                      ; 0x00000410, line  307
        eor     x6, x27, x29, ror #41                          ; 0x00000414, line  308
        shl     v17.2d, v31.2d, #0xa                           ; 0x00000418, line  309
        eor     x0, x15, x11, ror #52                          ; 0x0000041C, line  310
        eor     x0, x0, x13, ror #48                           ; 0x00000420, line  311
        sri     v17.2d, v31.2d, #0x36                          ; 0x00000424, line  312
        eor     x26, x8, x9, ror #57                           ; 0x00000428, line  313
        eor     v31.16b, v9.16b, v27.16b                       ; 0x0000042C, line  314
        eor     x27, x0, x14, ror #10                          ; 0x00000430, line  315
        shl     v11.2d, v31.2d, #0x14                          ; 0x00000434, line  316
        eor     x29, x16, x28, ror #63                         ; 0x00000438, line  317
        eor     x26, x26, x6, ror #51                          ; 0x0000043C, line  318
        sri     v11.2d, v31.2d, #0x2c                          ; 0x00000440, line  319
        eor     x30, x23, x22, ror #50                         ; 0x00000444, line  320
        eor     v31.16b, v22.16b, v29.16b                      ; 0x00000448, line  321
        eor     x0, x26, x10, ror #31                          ; 0x0000044C, line  322
        shl     v9.2d, v31.2d, #0x3d                           ; 0x00000450, line  323
        eor     x29, x29, x19, ror #37                         ; 0x00000454, line  324
        eor     x27, x27, x12, ror #5                          ; 0x00000458, line  325
        sri     v9.2d, v31.2d, #0x3                            ; 0x0000045C, line  326
        eor     x30, x30, x24, ror #34                         ; 0x00000460, line  327
        eor     v31.16b, v14.16b, v27.16b                      ; 0x00000464, line  328
        eor     x0, x0, x7, ror #27                            ; 0x00000468, line  329
        shl     v22.2d, v31.2d, #0x27                          ; 0x0000046C, line  330
        eor     x26, x30, x21, ror #26                         ; 0x00000470, line  331
        eor     x26, x26, x25, ror #15                         ; 0x00000474, line  332
        sri     v22.2d, v31.2d, #0x19                          ; 0x00000478, line  333
        ror     x30, x27, #0x3e                                ; 0x0000047C, line  334
        eor     v31.16b, v20.16b, v26.16b                      ; 0x00000480, line  335
        eor     x30, x30, x26, ror #57                         ; 0x00000484, line  336
        ror     x26, x26, #0x3a                                ; 0x00000488, line  337
        shl     v14.2d, v31.2d, #0x12                          ; 0x0000048C, line  338
        eor     x16, x30, x16                                  ; 0x00000490, line  339
        sri     v14.2d, v31.2d, #0x2e                          ; 0x00000494, line  340
        eor     x28, x30, x28, ror #63                         ; 0x00000498, line  341
        eor     v31.16b, v4.16b, v27.16b                       ; 0x0000049C, line  342
        str     x28, [sp, #0xd0]                               ; 0x000004A0, line  343
        eor     x29, x29, x17, ror #36                         ; 0x000004A4, line  344
        shl     v20.2d, v31.2d, #0x1b                          ; 0x000004A8, line  345
        eor     x28, x1, x2, ror #61                           ; 0x000004AC, line  346
        sri     v20.2d, v31.2d, #0x25                          ; 0x000004B0, line  347
        eor     x19, x30, x19, ror #37                         ; 0x000004B4, line  348
        eor     v31.16b, v24.16b, v27.16b                      ; 0x000004B8, line  349
        eor     x29, x29, x20, ror #2                          ; 0x000004BC, line  350
        eor     x28, x28, x4, ror #54                          ; 0x000004C0, line  351
        shl     v4.2d, v31.2d, #0xe                            ; 0x000004C4, line  352
        eor     x26, x26, x0, ror #55                          ; 0x000004C8, line  353
        sri     v4.2d, v31.2d, #0x32                           ; 0x000004CC, line  354
        eor     x28, x28, x3, ror #39                          ; 0x000004D0, line  355
        eor     v31.16b, v21.16b, v25.16b                      ; 0x000004D4, line  356
        eor     x28, x28, x5, ror #25                          ; 0x000004D8, line  357
        ror     x0, x0, #0x38                                  ; 0x000004DC, line  358
        shl     v24.2d, v31.2d, #0x2                           ; 0x000004E0, line  359
        eor     x0, x0, x29, ror #63                           ; 0x000004E4, line  360
        sri     v24.2d, v31.2d, #0x3e                          ; 0x000004E8, line  361
        eor     x27, x28, x27, ror #61                         ; 0x000004EC, line  362
        eor     v31.16b, v5.16b, v26.16b                       ; 0x000004F0, line  363
        eor     x13, x0, x13, ror #46                          ; 0x000004F4, line  364
        eor     x28, x29, x28, ror #63                         ; 0x000004F8, line  365
        shl     v21.2d, v31.2d, #0x24                          ; 0x000004FC, line  366
        eor     x29, x30, x20, ror #2                          ; 0x00000500, line  367
        sri     v21.2d, v31.2d, #0x1c                          ; 0x00000504, line  368
        eor     x20, x26, x3, ror #39                          ; 0x00000508, line  369
        eor     v31.16b, v6.16b, v25.16b                       ; 0x0000050C, line  370
        eor     x11, x0, x11, ror #50                          ; 0x00000510, line  371
        eor     x25, x28, x25, ror #9                          ; 0x00000514, line  372
        shl     v27.2d, v31.2d, #0x2c                          ; 0x00000518, line  373
        eor     x3, x28, x21, ror #20                          ; 0x0000051C, line  374
        sri     v27.2d, v31.2d, #0x14                          ; 0x00000520, line  375
        eor     x21, x26, x1                                   ; 0x00000524, line  376
        eor     x9, x27, x9, ror #49                           ; 0x00000528, line  377
        bic     v31.16b, v7.16b, v11.16b                       ; 0x0000052C, line  378
        eor     x24, x28, x24, ror #28                         ; 0x00000530, line  379
        eor     v5.16b, v31.16b, v10.16b                       ; 0x00000534, line  380
        eor     x1, x30, x17, ror #36                          ; 0x00000538, line  381
        bic     v31.16b, v8.16b, v7.16b                        ; 0x0000053C, line  382
        eor     x14, x0, x14, ror #8                           ; 0x00000540, line  383
        eor     x22, x28, x22, ror #44                         ; 0x00000544, line  384
        eor     v6.16b, v31.16b, v11.16b                       ; 0x00000548, line  385
        eor     x8, x27, x8, ror #56                           ; 0x0000054C, line  386
        bic     v31.16b, v9.16b, v8.16b                        ; 0x00000550, line  387
        eor     x17, x27, x7, ror #19                          ; 0x00000554, line  388
        eor     v7.16b, v31.16b, v7.16b                        ; 0x00000558, line  389
        eor     x15, x0, x15, ror #62                          ; 0x0000055C, line  390
        bic     x7, x20, x22, ror #47                          ; 0x00000560, line  391
        bic     v31.16b, v10.16b, v9.16b                       ; 0x00000564, line  392
        eor     x4, x26, x4, ror #54                           ; 0x00000568, line  393
        eor     v8.16b, v31.16b, v8.16b                        ; 0x0000056C, line  394
        eor     x0, x0, x12, ror #3                            ; 0x00000570, line  395
        bic     v31.16b, v11.16b, v10.16b                      ; 0x00000574, line  396
        eor     x28, x28, x23, ror #58                         ; 0x00000578, line  397
        eor     x23, x26, x2, ror #61                          ; 0x0000057C, line  398
        eor     v9.16b, v31.16b, v9.16b                        ; 0x00000580, line  399
        eor     x26, x26, x5, ror #25                          ; 0x00000584, line  400
        bic     v31.16b, v12.16b, v16.16b                      ; 0x00000588, line  401
        eor     x2, x7, x16, ror #39                           ; 0x0000058C, line  402
        eor     v10.16b, v31.16b, v15.16b                      ; 0x00000590, line  403
        bic     x7, x9, x20, ror #42                           ; 0x00000594, line  404
        bic     x30, x15, x9, ror #16                          ; 0x00000598, line  405
        bic     v31.16b, v13.16b, v12.16b                      ; 0x0000059C, line  406
        eor     x7, x7, x22, ror #25                           ; 0x000005A0, line  407
        eor     v11.16b, v31.16b, v16.16b                      ; 0x000005A4, line  408
        eor     x12, x30, x20, ror #58                         ; 0x000005A8, line  409
        bic     v31.16b, v14.16b, v13.16b                      ; 0x000005AC, line  410
        bic     x20, x22, x16, ror #56                         ; 0x000005B0, line  411
        eor     x30, x27, x6, ror #43                          ; 0x000005B4, line  412
        eor     v12.16b, v31.16b, v12.16b                      ; 0x000005B8, line  413
        eor     x22, x20, x15, ror #23                         ; 0x000005BC, line  414
        bic     v31.16b, v15.16b, v14.16b                      ; 0x000005C0, line  415
        bic     x6, x19, x13, ror #42                          ; 0x000005C4, line  416
        eor     v13.16b, v31.16b, v13.16b                      ; 0x000005C8, line  417
        eor     x6, x6, x17, ror #41                           ; 0x000005CC, line  418
        bic     x5, x13, x17, ror #63                          ; 0x000005D0, line  419
        bic     v31.16b, v16.16b, v15.16b                      ; 0x000005D4, line  420
        eor     x5, x21, x5, ror #21                           ; 0x000005D8, line  421
        eor     v14.16b, v31.16b, v14.16b                      ; 0x000005DC, line  422
        bic     x17, x17, x21, ror #44                         ; 0x000005E0, line  423
        eor     x27, x27, x10, ror #23                         ; 0x000005E4, line  424
        bic     v31.16b, v17.16b, v21.16b                      ; 0x000005E8, line  425
        bic     x21, x21, x25, ror #50                         ; 0x000005EC, line  426
        eor     v15.16b, v31.16b, v20.16b                      ; 0x000005F0, line  427
        bic     x20, x27, x4, ror #25                          ; 0x000005F4, line  428
        bic     v31.16b, v18.16b, v17.16b                      ; 0x000005F8, line  429
        bic     x10, x16, x15, ror #31                         ; 0x000005FC, line  430
        eor     x16, x21, x19, ror #43                         ; 0x00000600, line  431
        eor     v16.16b, v31.16b, v21.16b                      ; 0x00000604, line  432
        eor     x21, x17, x25, ror #30                         ; 0x00000608, line  433
        bic     v31.16b, v19.16b, v18.16b                      ; 0x0000060C, line  434
        bic     x19, x25, x19, ror #57                         ; 0x00000610, line  435
        eor     v17.16b, v31.16b, v17.16b                      ; 0x00000614, line  436
        ldr     x25, [sp, #0x18]                               ; 0x00000618, line  437
        eor     x17, x10, x9, ror #47                          ; 0x0000061C, line  438
        bic     v31.16b, v20.16b, v19.16b                      ; 0x00000620, line  439
        ldr     x9, [sp, #0x8]                                 ; 0x00000624, line  440
        eor     v18.16b, v31.16b, v18.16b                      ; 0x00000628, line  441
        eor     x15, x20, x28, ror #27                         ; 0x0000062C, line  442
        bic     v31.16b, v21.16b, v20.16b                      ; 0x00000630, line  443
        bic     x20, x4, x28, ror #2                           ; 0x00000634, line  444
        eor     x10, x20, x1, ror #50                          ; 0x00000638, line  445
        eor     v19.16b, v31.16b, v19.16b                      ; 0x0000063C, line  446
        bic     x20, x11, x27, ror #60                         ; 0x00000640, line  447
        bic     v31.16b, v22.16b, v1.16b                       ; 0x00000644, line  448
        eor     x20, x20, x4, ror #21                          ; 0x00000648, line  449
        eor     v20.16b, v31.16b, v0.16b                       ; 0x0000064C, line  450
        bic     x4, x28, x1, ror #48                           ; 0x00000650, line  451
        bic     x1, x1, x11, ror #57                           ; 0x00000654, line  452
        bic     v31.16b, v23.16b, v22.16b                      ; 0x00000658, line  453
        ldr     x28, [x9, x25, lsl #3]                         ; 0x0000065C, line  454
        eor     v21.16b, v31.16b, v1.16b                       ; 0x00000660, line  455
        ldr     x9, [sp, #0xd0]                                ; 0x00000664, line  456
        bic     v31.16b, v24.16b, v23.16b                      ; 0x00000668, line  457
        add     x25, x25, #0x1                                 ; 0x0000066C, line  458
        str     x25, [sp, #0x18]                               ; 0x00000670, line  459
        eor     v22.16b, v31.16b, v22.16b                      ; 0x00000674, line  460
        cmp     x25, #0x17                                     ; 0x00000678, line  461
        bic     v31.16b, v0.16b, v24.16b                       ; 0x0000067C, line  462
        eor     x25, x1, x27, ror #53                          ; 0x00000680, line  463
        bic     x27, x30, x26, ror #47                         ; 0x00000684, line  464
        eor     v23.16b, v31.16b, v23.16b                      ; 0x00000688, line  465
        eor     x1, x5, x28                                    ; 0x0000068C, line  466
        bic     v31.16b, v1.16b, v0.16b                        ; 0x00000690, line  467
        eor     x5, x4, x11, ror #41                           ; 0x00000694, line  468
        eor     v24.16b, v31.16b, v24.16b                      ; 0x00000698, line  469
        eor     x11, x19, x13, ror #35                         ; 0x0000069C, line  470
        bic     x13, x26, x24, ror #10                         ; 0x000006A0, line  471
        bic     v31.16b, v2.16b, v27.16b                       ; 0x000006A4, line  472
        eor     x28, x27, x24, ror #57                         ; 0x000006A8, line  473
        eor     v0.16b, v31.16b, v30.16b                       ; 0x000006AC, line  474
        bic     x27, x24, x9, ror #47                          ; 0x000006B0, line  475
        bic     v31.16b, v3.16b, v2.16b                        ; 0x000006B4, line  476
        bic     x19, x23, x3, ror #9                           ; 0x000006B8, line  477
        bic     x4, x29, x14, ror #41                          ; 0x000006BC, line  478
        eor     v1.16b, v31.16b, v27.16b                       ; 0x000006C0, line  479
        eor     x24, x19, x29, ror #44                         ; 0x000006C4, line  480
        bic     v31.16b, v4.16b, v3.16b                        ; 0x000006C8, line  481
        bic     x29, x3, x29, ror #35                          ; 0x000006CC, line  482
        eor     v2.16b, v31.16b, v2.16b                        ; 0x000006D0, line  483
        eor     x13, x13, x9, ror #57                          ; 0x000006D4, line  484
        eor     x19, x29, x14, ror #12                         ; 0x000006D8, line  485
        bic     v31.16b, v30.16b, v4.16b                       ; 0x000006DC, line  486
        bic     x29, x9, x0, ror #19                           ; 0x000006E0, line  487
        eor     v3.16b, v31.16b, v3.16b                        ; 0x000006E4, line  488
        bic     x14, x14, x8, ror #5                           ; 0x000006E8, line  489
        bic     v31.16b, v27.16b, v30.16b                      ; 0x000006EC, line  490
        eor     x9, x14, x23, ror #43                          ; 0x000006F0, line  491
        eor     x14, x4, x8, ror #46                           ; 0x000006F4, line  492
        eor     v4.16b, v31.16b, v4.16b                        ; 0x000006F8, line  493
        bic     x23, x8, x23, ror #38                          ; 0x000006FC, line  494
        eor     x8, x27, x0, ror #2                            ; 0x00000700, line  495
        eor     x4, x23, x3, ror #47                           ; 0x00000704, line  496
        bic     x3, x0, x30, ror #5                            ; 0x00000708, line  497
        eor     x23, x3, x26, ror #52                          ; 0x0000070C, line  498
        eor     x3, x29, x30, ror #24                          ; 0x00000710, line  499
        ldr     x30, [sp, #0x10]                               ; 0x00000714, line  500
        ld1r    { v28.2d }, [x30], #8                          ; 0x00000718, line  501
        str     x30, [sp, #0x10]                               ; 0x0000071C, line  502
        eor     v0.16b, v0.16b, v28.16b                        ; 0x00000720, line  503
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x4_v8a_scalar_hybrid_loop

        eor     x0, x15, x11, ror #52                          ; 0x00000730, line  506
        eor     x0, x0, x13, ror #48                           ; 0x00000734, line  507
        eor     v30.16b, v0.16b, v5.16b                        ; 0x00000738, line  508
        eor     v30.16b, v30.16b, v10.16b                      ; 0x0000073C, line  509
        eor     x26, x8, x9, ror #57                           ; 0x00000740, line  510
        eor     v30.16b, v30.16b, v15.16b                      ; 0x00000744, line  511
        eor     x27, x0, x14, ror #10                          ; 0x00000748, line  512
        eor     x29, x16, x28, ror #63                         ; 0x0000074C, line  513
        eor     v30.16b, v30.16b, v20.16b                      ; 0x00000750, line  514
        eor     x26, x26, x6, ror #51                          ; 0x00000754, line  515
        eor     v29.16b, v1.16b, v6.16b                        ; 0x00000758, line  516
        eor     x30, x23, x22, ror #50                         ; 0x0000075C, line  517
        eor     v29.16b, v29.16b, v11.16b                      ; 0x00000760, line  518
        eor     x0, x26, x10, ror #31                          ; 0x00000764, line  519
        eor     x29, x29, x19, ror #37                         ; 0x00000768, line  520
        eor     v29.16b, v29.16b, v16.16b                      ; 0x0000076C, line  521
        eor     x27, x27, x12, ror #5                          ; 0x00000770, line  522
        eor     v29.16b, v29.16b, v21.16b                      ; 0x00000774, line  523
        eor     x30, x30, x24, ror #34                         ; 0x00000778, line  524
        eor     x0, x0, x7, ror #27                            ; 0x0000077C, line  525
        eor     v28.16b, v2.16b, v7.16b                        ; 0x00000780, line  526
        eor     x26, x30, x21, ror #26                         ; 0x00000784, line  527
        eor     v28.16b, v28.16b, v12.16b                      ; 0x00000788, line  528
        eor     x26, x26, x25, ror #15                         ; 0x0000078C, line  529
        eor     v28.16b, v28.16b, v17.16b                      ; 0x00000790, line  530
        ror     x30, x27, #0x3e                                ; 0x00000794, line  531
        eor     x30, x30, x26, ror #57                         ; 0x00000798, line  532
        eor     v28.16b, v28.16b, v22.16b                      ; 0x0000079C, line  533
        ror     x26, x26, #0x3a                                ; 0x000007A0, line  534
        eor     v27.16b, v3.16b, v8.16b                        ; 0x000007A4, line  535
        eor     x16, x30, x16                                  ; 0x000007A8, line  536
        eor     v27.16b, v27.16b, v13.16b                      ; 0x000007AC, line  537
        eor     x28, x30, x28, ror #63                         ; 0x000007B0, line  538
        str     x28, [sp, #0xd0]                               ; 0x000007B4, line  539
        eor     v27.16b, v27.16b, v18.16b                      ; 0x000007B8, line  540
        eor     x29, x29, x17, ror #36                         ; 0x000007BC, line  541
        eor     v27.16b, v27.16b, v23.16b                      ; 0x000007C0, line  542
        eor     x28, x1, x2, ror #61                           ; 0x000007C4, line  543
        eor     x19, x30, x19, ror #37                         ; 0x000007C8, line  544
        eor     v26.16b, v4.16b, v9.16b                        ; 0x000007CC, line  545
        eor     x29, x29, x20, ror #2                          ; 0x000007D0, line  546
        eor     v26.16b, v26.16b, v14.16b                      ; 0x000007D4, line  547
        eor     x28, x28, x4, ror #54                          ; 0x000007D8, line  548
        eor     v26.16b, v26.16b, v19.16b                      ; 0x000007DC, line  549
        eor     x26, x26, x0, ror #55                          ; 0x000007E0, line  550
        eor     x28, x28, x3, ror #39                          ; 0x000007E4, line  551
        eor     v26.16b, v26.16b, v24.16b                      ; 0x000007E8, line  552
        eor     x28, x28, x5, ror #25                          ; 0x000007EC, line  553
        add     v31.2d, v28.2d, v28.2d                         ; 0x000007F0, line  554
        ror     x0, x0, #0x38                                  ; 0x000007F4, line  555
        eor     x0, x0, x29, ror #63                           ; 0x000007F8, line  556
        sri     v31.2d, v28.2d, #0x3f                          ; 0x000007FC, line  557
        eor     x27, x28, x27, ror #61                         ; 0x00000800, line  558
        eor     v25.16b, v31.16b, v30.16b                      ; 0x00000804, line  559
        eor     x13, x0, x13, ror #46                          ; 0x00000808, line  560
        add     v31.2d, v26.2d, v26.2d                         ; 0x0000080C, line  561
        eor     x28, x29, x28, ror #63                         ; 0x00000810, line  562
        eor     x29, x30, x20, ror #2                          ; 0x00000814, line  563
        sri     v31.2d, v26.2d, #0x3f                          ; 0x00000818, line  564
        eor     x20, x26, x3, ror #39                          ; 0x0000081C, line  565
        eor     v28.16b, v31.16b, v28.16b                      ; 0x00000820, line  566
        eor     x11, x0, x11, ror #50                          ; 0x00000824, line  567
        add     v31.2d, v29.2d, v29.2d                         ; 0x00000828, line  568
        eor     x25, x28, x25, ror #9                          ; 0x0000082C, line  569
        eor     x3, x28, x21, ror #20                          ; 0x00000830, line  570
        sri     v31.2d, v29.2d, #0x3f                          ; 0x00000834, line  571
        eor     x21, x26, x1                                   ; 0x00000838, line  572
        eor     v26.16b, v31.16b, v26.16b                      ; 0x0000083C, line  573
        eor     x9, x27, x9, ror #49                           ; 0x00000840, line  574
        eor     x24, x28, x24, ror #28                         ; 0x00000844, line  575
        add     v31.2d, v27.2d, v27.2d                         ; 0x00000848, line  576
        eor     x1, x30, x17, ror #36                          ; 0x0000084C, line  577
        sri     v31.2d, v27.2d, #0x3f                          ; 0x00000850, line  578
        eor     x14, x0, x14, ror #8                           ; 0x00000854, line  579
        eor     v29.16b, v31.16b, v29.16b                      ; 0x00000858, line  580
        eor     x22, x28, x22, ror #44                         ; 0x0000085C, line  581
        eor     x8, x27, x8, ror #56                           ; 0x00000860, line  582
        add     v31.2d, v30.2d, v30.2d                         ; 0x00000864, line  583
        eor     x17, x27, x7, ror #19                          ; 0x00000868, line  584
        sri     v31.2d, v30.2d, #0x3f                          ; 0x0000086C, line  585
        eor     x15, x0, x15, ror #62                          ; 0x00000870, line  586
        bic     x7, x20, x22, ror #47                          ; 0x00000874, line  587
        eor     v27.16b, v31.16b, v27.16b                      ; 0x00000878, line  588
        eor     x4, x26, x4, ror #54                           ; 0x0000087C, line  589
        eor     v30.16b, v0.16b, v26.16b                       ; 0x00000880, line  590
        eor     x0, x0, x12, ror #3                            ; 0x00000884, line  591
        eor     v31.16b, v2.16b, v29.16b                       ; 0x00000888, line  592
        eor     x28, x28, x23, ror #58                         ; 0x0000088C, line  593
        eor     x23, x26, x2, ror #61                          ; 0x00000890, line  594
        shl     v0.2d, v31.2d, #0x3e                           ; 0x00000894, line  595
        eor     x26, x26, x5, ror #25                          ; 0x00000898, line  596
        sri     v0.2d, v31.2d, #0x2                            ; 0x0000089C, line  597
        eor     x2, x7, x16, ror #39                           ; 0x000008A0, line  598
        eor     v31.16b, v12.16b, v29.16b                      ; 0x000008A4, line  599
        bic     x7, x9, x20, ror #42                           ; 0x000008A8, line  600
        bic     x30, x15, x9, ror #16                          ; 0x000008AC, line  601
        shl     v2.2d, v31.2d, #0x2b                           ; 0x000008B0, line  602
        eor     x7, x7, x22, ror #25                           ; 0x000008B4, line  603
        sri     v2.2d, v31.2d, #0x15                           ; 0x000008B8, line  604
        eor     x12, x30, x20, ror #58                         ; 0x000008BC, line  605
        bic     x20, x22, x16, ror #56                         ; 0x000008C0, line  606
        eor     v31.16b, v13.16b, v28.16b                      ; 0x000008C4, line  607
        eor     x30, x27, x6, ror #43                          ; 0x000008C8, line  608
        shl     v12.2d, v31.2d, #0x19                          ; 0x000008CC, line  609
        eor     x22, x20, x15, ror #23                         ; 0x000008D0, line  610
        sri     v12.2d, v31.2d, #0x27                          ; 0x000008D4, line  611
        bic     x6, x19, x13, ror #42                          ; 0x000008D8, line  612
        eor     x6, x6, x17, ror #41                           ; 0x000008DC, line  613
        eor     v31.16b, v19.16b, v27.16b                      ; 0x000008E0, line  614
        bic     x5, x13, x17, ror #63                          ; 0x000008E4, line  615
        shl     v13.2d, v31.2d, #0x8                           ; 0x000008E8, line  616
        eor     x5, x21, x5, ror #21                           ; 0x000008EC, line  617
        sri     v13.2d, v31.2d, #0x38                          ; 0x000008F0, line  618
        bic     x17, x17, x21, ror #44                         ; 0x000008F4, line  619
        eor     x27, x27, x10, ror #23                         ; 0x000008F8, line  620
        eor     v31.16b, v23.16b, v28.16b                      ; 0x000008FC, line  621
        bic     x21, x21, x25, ror #50                         ; 0x00000900, line  622
        shl     v19.2d, v31.2d, #0x38                          ; 0x00000904, line  623
        bic     x20, x27, x4, ror #25                          ; 0x00000908, line  624
        bic     x10, x16, x15, ror #31                         ; 0x0000090C, line  625
        sri     v19.2d, v31.2d, #0x8                           ; 0x00000910, line  626
        eor     x16, x21, x19, ror #43                         ; 0x00000914, line  627
        eor     v31.16b, v15.16b, v26.16b                      ; 0x00000918, line  628
        eor     x21, x17, x25, ror #30                         ; 0x0000091C, line  629
        shl     v23.2d, v31.2d, #0x29                          ; 0x00000920, line  630
        bic     x19, x25, x19, ror #57                         ; 0x00000924, line  631
        ldr     x25, [sp, #0x18]                               ; 0x00000928, line  632
        sri     v23.2d, v31.2d, #0x17                          ; 0x0000092C, line  633
        eor     x17, x10, x9, ror #47                          ; 0x00000930, line  634
        eor     v31.16b, v1.16b, v25.16b                       ; 0x00000934, line  635
        ldr     x9, [sp, #0x8]                                 ; 0x00000938, line  636
        eor     x15, x20, x28, ror #27                         ; 0x0000093C, line  637
        shl     v15.2d, v31.2d, #0x1                           ; 0x00000940, line  638
        bic     x20, x4, x28, ror #2                           ; 0x00000944, line  639
        sri     v15.2d, v31.2d, #0x3f                          ; 0x00000948, line  640
        eor     x10, x20, x1, ror #50                          ; 0x0000094C, line  641
        eor     v31.16b, v8.16b, v28.16b                       ; 0x00000950, line  642
        bic     x20, x11, x27, ror #60                         ; 0x00000954, line  643
        eor     x20, x20, x4, ror #21                          ; 0x00000958, line  644
        shl     v1.2d, v31.2d, #0x37                           ; 0x0000095C, line  645
        bic     x4, x28, x1, ror #48                           ; 0x00000960, line  646
        sri     v1.2d, v31.2d, #0x9                            ; 0x00000964, line  647
        bic     x1, x1, x11, ror #57                           ; 0x00000968, line  648
        eor     v31.16b, v16.16b, v25.16b                      ; 0x0000096C, line  649
        ldr     x28, [x9, x25, lsl #3]                         ; 0x00000970, line  650
        ldr     x9, [sp, #0xd0]                                ; 0x00000974, line  651
        shl     v8.2d, v31.2d, #0x2d                           ; 0x00000978, line  652
        add     x25, x25, #0x1                                 ; 0x0000097C, line  653
        sri     v8.2d, v31.2d, #0x13                           ; 0x00000980, line  654
        str     x25, [sp, #0x18]                               ; 0x00000984, line  655
        cmp     x25, #0x17                                     ; 0x00000988, line  656
        eor     v31.16b, v7.16b, v29.16b                       ; 0x0000098C, line  657
        eor     x25, x1, x27, ror #53                          ; 0x00000990, line  658
        shl     v16.2d, v31.2d, #0x6                           ; 0x00000994, line  659
        bic     x27, x30, x26, ror #47                         ; 0x00000998, line  660
        sri     v16.2d, v31.2d, #0x3a                          ; 0x0000099C, line  661
        eor     x1, x5, x28                                    ; 0x000009A0, line  662
        eor     x5, x4, x11, ror #41                           ; 0x000009A4, line  663
        eor     v31.16b, v10.16b, v26.16b                      ; 0x000009A8, line  664
        eor     x11, x19, x13, ror #35                         ; 0x000009AC, line  665
        shl     v7.2d, v31.2d, #0x3                            ; 0x000009B0, line  666
        bic     x13, x26, x24, ror #10                         ; 0x000009B4, line  667
        eor     x28, x27, x24, ror #57                         ; 0x000009B8, line  668
        sri     v7.2d, v31.2d, #0x3d                           ; 0x000009BC, line  669
        bic     x27, x24, x9, ror #47                          ; 0x000009C0, line  670
        eor     v31.16b, v3.16b, v28.16b                       ; 0x000009C4, line  671
        bic     x19, x23, x3, ror #9                           ; 0x000009C8, line  672
        shl     v10.2d, v31.2d, #0x1c                          ; 0x000009CC, line  673
        bic     x4, x29, x14, ror #41                          ; 0x000009D0, line  674
        eor     x24, x19, x29, ror #44                         ; 0x000009D4, line  675
        sri     v10.2d, v31.2d, #0x24                          ; 0x000009D8, line  676
        bic     x29, x3, x29, ror #35                          ; 0x000009DC, line  677
        eor     v31.16b, v18.16b, v28.16b                      ; 0x000009E0, line  678
        eor     x13, x13, x9, ror #57                          ; 0x000009E4, line  679
        shl     v3.2d, v31.2d, #0x15                           ; 0x000009E8, line  680
        eor     x19, x29, x14, ror #12                         ; 0x000009EC, line  681
        bic     x29, x9, x0, ror #19                           ; 0x000009F0, line  682
        sri     v3.2d, v31.2d, #0x2b                           ; 0x000009F4, line  683
        bic     x14, x14, x8, ror #5                           ; 0x000009F8, line  684
        eor     v31.16b, v17.16b, v29.16b                      ; 0x000009FC, line  685
        eor     x9, x14, x23, ror #43                          ; 0x00000A00, line  686
        eor     x14, x4, x8, ror #46                           ; 0x00000A04, line  687
        shl     v18.2d, v31.2d, #0xf                           ; 0x00000A08, line  688
        bic     x23, x8, x23, ror #38                          ; 0x00000A0C, line  689
        sri     v18.2d, v31.2d, #0x31                          ; 0x00000A10, line  690
        eor     x8, x27, x0, ror #2                            ; 0x00000A14, line  691
        eor     v31.16b, v11.16b, v25.16b                      ; 0x00000A18, line  692
        eor     x4, x23, x3, ror #47                           ; 0x00000A1C, line  693
        bic     x3, x0, x30, ror #5                            ; 0x00000A20, line  694
        shl     v17.2d, v31.2d, #0xa                           ; 0x00000A24, line  695
        eor     x23, x3, x26, ror #52                          ; 0x00000A28, line  696
        sri     v17.2d, v31.2d, #0x36                          ; 0x00000A2C, line  697
        eor     x3, x29, x30, ror #24                          ; 0x00000A30, line  698
        eor     x0, x15, x11, ror #52                          ; 0x00000A34, line  699
        eor     v31.16b, v9.16b, v27.16b                       ; 0x00000A38, line  700
        eor     x0, x0, x13, ror #48                           ; 0x00000A3C, line  701
        shl     v11.2d, v31.2d, #0x14                          ; 0x00000A40, line  702
        eor     x26, x8, x9, ror #57                           ; 0x00000A44, line  703
        sri     v11.2d, v31.2d, #0x2c                          ; 0x00000A48, line  704
        eor     x27, x0, x14, ror #10                          ; 0x00000A4C, line  705
        eor     x29, x16, x28, ror #63                         ; 0x00000A50, line  706
        eor     v31.16b, v22.16b, v29.16b                      ; 0x00000A54, line  707
        eor     x26, x26, x6, ror #51                          ; 0x00000A58, line  708
        shl     v9.2d, v31.2d, #0x3d                           ; 0x00000A5C, line  709
        eor     x30, x23, x22, ror #50                         ; 0x00000A60, line  710
        sri     v9.2d, v31.2d, #0x3                            ; 0x00000A64, line  711
        eor     x0, x26, x10, ror #31                          ; 0x00000A68, line  712
        eor     x29, x29, x19, ror #37                         ; 0x00000A6C, line  713
        eor     v31.16b, v14.16b, v27.16b                      ; 0x00000A70, line  714
        eor     x27, x27, x12, ror #5                          ; 0x00000A74, line  715
        shl     v22.2d, v31.2d, #0x27                          ; 0x00000A78, line  716
        eor     x30, x30, x24, ror #34                         ; 0x00000A7C, line  717
        eor     x0, x0, x7, ror #27                            ; 0x00000A80, line  718
        sri     v22.2d, v31.2d, #0x19                          ; 0x00000A84, line  719
        eor     x26, x30, x21, ror #26                         ; 0x00000A88, line  720
        eor     v31.16b, v20.16b, v26.16b                      ; 0x00000A8C, line  721
        eor     x26, x26, x25, ror #15                         ; 0x00000A90, line  722
        shl     v14.2d, v31.2d, #0x12                          ; 0x00000A94, line  723
        ror     x30, x27, #0x3e                                ; 0x00000A98, line  724
        eor     x30, x30, x26, ror #57                         ; 0x00000A9C, line  725
        sri     v14.2d, v31.2d, #0x2e                          ; 0x00000AA0, line  726
        ror     x26, x26, #0x3a                                ; 0x00000AA4, line  727
        eor     v31.16b, v4.16b, v27.16b                       ; 0x00000AA8, line  728
        eor     x16, x30, x16                                  ; 0x00000AAC, line  729
        shl     v20.2d, v31.2d, #0x1b                          ; 0x00000AB0, line  730
        eor     x28, x30, x28, ror #63                         ; 0x00000AB4, line  731
        str     x28, [sp, #0xd0]                               ; 0x00000AB8, line  732
        sri     v20.2d, v31.2d, #0x25                          ; 0x00000ABC, line  733
        eor     x29, x29, x17, ror #36                         ; 0x00000AC0, line  734
        eor     v31.16b, v24.16b, v27.16b                      ; 0x00000AC4, line  735
        eor     x28, x1, x2, ror #61                           ; 0x00000AC8, line  736
        eor     x19, x30, x19, ror #37                         ; 0x00000ACC, line  737
        shl     v4.2d, v31.2d, #0xe                            ; 0x00000AD0, line  738
        eor     x29, x29, x20, ror #2                          ; 0x00000AD4, line  739
        sri     v4.2d, v31.2d, #0x32                           ; 0x00000AD8, line  740
        eor     x28, x28, x4, ror #54                          ; 0x00000ADC, line  741
        eor     v31.16b, v21.16b, v25.16b                      ; 0x00000AE0, line  742
        eor     x26, x26, x0, ror #55                          ; 0x00000AE4, line  743
        eor     x28, x28, x3, ror #39                          ; 0x00000AE8, line  744
        shl     v24.2d, v31.2d, #0x2                           ; 0x00000AEC, line  745
        eor     x28, x28, x5, ror #25                          ; 0x00000AF0, line  746
        sri     v24.2d, v31.2d, #0x3e                          ; 0x00000AF4, line  747
        ror     x0, x0, #0x38                                  ; 0x00000AF8, line  748
        eor     x0, x0, x29, ror #63                           ; 0x00000AFC, line  749
        eor     v31.16b, v5.16b, v26.16b                       ; 0x00000B00, line  750
        eor     x27, x28, x27, ror #61                         ; 0x00000B04, line  751
        shl     v21.2d, v31.2d, #0x24                          ; 0x00000B08, line  752
        eor     x13, x0, x13, ror #46                          ; 0x00000B0C, line  753
        sri     v21.2d, v31.2d, #0x1c                          ; 0x00000B10, line  754
        eor     x28, x29, x28, ror #63                         ; 0x00000B14, line  755
        eor     x29, x30, x20, ror #2                          ; 0x00000B18, line  756
        eor     v31.16b, v6.16b, v25.16b                       ; 0x00000B1C, line  757
        eor     x20, x26, x3, ror #39                          ; 0x00000B20, line  758
        shl     v27.2d, v31.2d, #0x2c                          ; 0x00000B24, line  759
        eor     x11, x0, x11, ror #50                          ; 0x00000B28, line  760
        sri     v27.2d, v31.2d, #0x14                          ; 0x00000B2C, line  761
        eor     x25, x28, x25, ror #9                          ; 0x00000B30, line  762
        eor     x3, x28, x21, ror #20                          ; 0x00000B34, line  763
        bic     v31.16b, v7.16b, v11.16b                       ; 0x00000B38, line  764
        eor     x21, x26, x1                                   ; 0x00000B3C, line  765
        eor     v5.16b, v31.16b, v10.16b                       ; 0x00000B40, line  766
        eor     x9, x27, x9, ror #49                           ; 0x00000B44, line  767
        eor     x24, x28, x24, ror #28                         ; 0x00000B48, line  768
        bic     v31.16b, v8.16b, v7.16b                        ; 0x00000B4C, line  769
        eor     x1, x30, x17, ror #36                          ; 0x00000B50, line  770
        eor     v6.16b, v31.16b, v11.16b                       ; 0x00000B54, line  771
        eor     x14, x0, x14, ror #8                           ; 0x00000B58, line  772
        bic     v31.16b, v9.16b, v8.16b                        ; 0x00000B5C, line  773
        eor     x22, x28, x22, ror #44                         ; 0x00000B60, line  774
        eor     x8, x27, x8, ror #56                           ; 0x00000B64, line  775
        eor     v7.16b, v31.16b, v7.16b                        ; 0x00000B68, line  776
        eor     x17, x27, x7, ror #19                          ; 0x00000B6C, line  777
        bic     v31.16b, v10.16b, v9.16b                       ; 0x00000B70, line  778
        eor     x15, x0, x15, ror #62                          ; 0x00000B74, line  779
        bic     x7, x20, x22, ror #47                          ; 0x00000B78, line  780
        eor     v8.16b, v31.16b, v8.16b                        ; 0x00000B7C, line  781
        eor     x4, x26, x4, ror #54                           ; 0x00000B80, line  782
        bic     v31.16b, v11.16b, v10.16b                      ; 0x00000B84, line  783
        eor     x0, x0, x12, ror #3                            ; 0x00000B88, line  784
        eor     v9.16b, v31.16b, v9.16b                        ; 0x00000B8C, line  785
        eor     x28, x28, x23, ror #58                         ; 0x00000B90, line  786
        eor     x23, x26, x2, ror #61                          ; 0x00000B94, line  787
        bic     v31.16b, v12.16b, v16.16b                      ; 0x00000B98, line  788
        eor     x26, x26, x5, ror #25                          ; 0x00000B9C, line  789
        eor     v10.16b, v31.16b, v15.16b                      ; 0x00000BA0, line  790
        eor     x2, x7, x16, ror #39                           ; 0x00000BA4, line  791
        bic     v31.16b, v13.16b, v12.16b                      ; 0x00000BA8, line  792
        bic     x7, x9, x20, ror #42                           ; 0x00000BAC, line  793
        bic     x30, x15, x9, ror #16                          ; 0x00000BB0, line  794
        eor     v11.16b, v31.16b, v16.16b                      ; 0x00000BB4, line  795
        eor     x7, x7, x22, ror #25                           ; 0x00000BB8, line  796
        bic     v31.16b, v14.16b, v13.16b                      ; 0x00000BBC, line  797
        eor     x12, x30, x20, ror #58                         ; 0x00000BC0, line  798
        bic     x20, x22, x16, ror #56                         ; 0x00000BC4, line  799
        eor     v12.16b, v31.16b, v12.16b                      ; 0x00000BC8, line  800
        eor     x30, x27, x6, ror #43                          ; 0x00000BCC, line  801
        bic     v31.16b, v15.16b, v14.16b                      ; 0x00000BD0, line  802
        eor     x22, x20, x15, ror #23                         ; 0x00000BD4, line  803
        eor     v13.16b, v31.16b, v13.16b                      ; 0x00000BD8, line  804
        bic     x6, x19, x13, ror #42                          ; 0x00000BDC, line  805
        eor     x6, x6, x17, ror #41                           ; 0x00000BE0, line  806
        bic     v31.16b, v16.16b, v15.16b                      ; 0x00000BE4, line  807
        bic     x5, x13, x17, ror #63                          ; 0x00000BE8, line  808
        eor     v14.16b, v31.16b, v14.16b                      ; 0x00000BEC, line  809
        eor     x5, x21, x5, ror #21                           ; 0x00000BF0, line  810
        bic     v31.16b, v17.16b, v21.16b                      ; 0x00000BF4, line  811
        bic     x17, x17, x21, ror #44                         ; 0x00000BF8, line  812
        eor     x27, x27, x10, ror #23                         ; 0x00000BFC, line  813
        eor     v15.16b, v31.16b, v20.16b                      ; 0x00000C00, line  814
        bic     x21, x21, x25, ror #50                         ; 0x00000C04, line  815
        bic     v31.16b, v18.16b, v17.16b                      ; 0x00000C08, line  816
        bic     x20, x27, x4, ror #25                          ; 0x00000C0C, line  817
        bic     x10, x16, x15, ror #31                         ; 0x00000C10, line  818
        eor     v16.16b, v31.16b, v21.16b                      ; 0x00000C14, line  819
        eor     x16, x21, x19, ror #43                         ; 0x00000C18, line  820
        bic     v31.16b, v19.16b, v18.16b                      ; 0x00000C1C, line  821
        eor     x21, x17, x25, ror #30                         ; 0x00000C20, line  822
        eor     v17.16b, v31.16b, v17.16b                      ; 0x00000C24, line  823
        bic     x19, x25, x19, ror #57                         ; 0x00000C28, line  824
        ldr     x25, [sp, #0x18]                               ; 0x00000C2C, line  825
        bic     v31.16b, v20.16b, v19.16b                      ; 0x00000C30, line  826
        eor     x17, x10, x9, ror #47                          ; 0x00000C34, line  827
        eor     v18.16b, v31.16b, v18.16b                      ; 0x00000C38, line  828
        ldr     x9, [sp, #0x8]                                 ; 0x00000C3C, line  829
        eor     x15, x20, x28, ror #27                         ; 0x00000C40, line  830
        bic     v31.16b, v21.16b, v20.16b                      ; 0x00000C44, line  831
        bic     x20, x4, x28, ror #2                           ; 0x00000C48, line  832
        eor     v19.16b, v31.16b, v19.16b                      ; 0x00000C4C, line  833
        eor     x10, x20, x1, ror #50                          ; 0x00000C50, line  834
        bic     v31.16b, v22.16b, v1.16b                       ; 0x00000C54, line  835
        bic     x20, x11, x27, ror #60                         ; 0x00000C58, line  836
        eor     x20, x20, x4, ror #21                          ; 0x00000C5C, line  837
        eor     v20.16b, v31.16b, v0.16b                       ; 0x00000C60, line  838
        bic     x4, x28, x1, ror #48                           ; 0x00000C64, line  839
        bic     v31.16b, v23.16b, v22.16b                      ; 0x00000C68, line  840
        bic     x1, x1, x11, ror #57                           ; 0x00000C6C, line  841
        eor     v21.16b, v31.16b, v1.16b                       ; 0x00000C70, line  842
        ldr     x28, [x9, x25, lsl #3]                         ; 0x00000C74, line  843
        ldr     x9, [sp, #0xd0]                                ; 0x00000C78, line  844
        bic     v31.16b, v24.16b, v23.16b                      ; 0x00000C7C, line  845
        add     x25, x25, #0x1                                 ; 0x00000C80, line  846
        eor     v22.16b, v31.16b, v22.16b                      ; 0x00000C84, line  847
        str     x25, [sp, #0x18]                               ; 0x00000C88, line  848
        cmp     x25, #0x17                                     ; 0x00000C8C, line  849
        bic     v31.16b, v0.16b, v24.16b                       ; 0x00000C90, line  850
        eor     x25, x1, x27, ror #53                          ; 0x00000C94, line  851
        eor     v23.16b, v31.16b, v23.16b                      ; 0x00000C98, line  852
        bic     x27, x30, x26, ror #47                         ; 0x00000C9C, line  853
        bic     v31.16b, v1.16b, v0.16b                        ; 0x00000CA0, line  854
        eor     x1, x5, x28                                    ; 0x00000CA4, line  855
        eor     x5, x4, x11, ror #41                           ; 0x00000CA8, line  856
        eor     v24.16b, v31.16b, v24.16b                      ; 0x00000CAC, line  857
        eor     x11, x19, x13, ror #35                         ; 0x00000CB0, line  858
        bic     v31.16b, v2.16b, v27.16b                       ; 0x00000CB4, line  859
        bic     x13, x26, x24, ror #10                         ; 0x00000CB8, line  860
        eor     x28, x27, x24, ror #57                         ; 0x00000CBC, line  861
        eor     v0.16b, v31.16b, v30.16b                       ; 0x00000CC0, line  862
        bic     x27, x24, x9, ror #47                          ; 0x00000CC4, line  863
        bic     v31.16b, v3.16b, v2.16b                        ; 0x00000CC8, line  864
        bic     x19, x23, x3, ror #9                           ; 0x00000CCC, line  865
        eor     v1.16b, v31.16b, v27.16b                       ; 0x00000CD0, line  866
        bic     x4, x29, x14, ror #41                          ; 0x00000CD4, line  867
        eor     x24, x19, x29, ror #44                         ; 0x00000CD8, line  868
        bic     v31.16b, v4.16b, v3.16b                        ; 0x00000CDC, line  869
        bic     x29, x3, x29, ror #35                          ; 0x00000CE0, line  870
        eor     v2.16b, v31.16b, v2.16b                        ; 0x00000CE4, line  871
        eor     x13, x13, x9, ror #57                          ; 0x00000CE8, line  872
        bic     v31.16b, v30.16b, v4.16b                       ; 0x00000CEC, line  873
        eor     x19, x29, x14, ror #12                         ; 0x00000CF0, line  874
        bic     x29, x9, x0, ror #19                           ; 0x00000CF4, line  875
        eor     v3.16b, v31.16b, v3.16b                        ; 0x00000CF8, line  876
        bic     x14, x14, x8, ror #5                           ; 0x00000CFC, line  877
        bic     v31.16b, v27.16b, v30.16b                      ; 0x00000D00, line  878
        eor     x9, x14, x23, ror #43                          ; 0x00000D04, line  879
        eor     x14, x4, x8, ror #46                           ; 0x00000D08, line  880
        eor     v4.16b, v31.16b, v4.16b                        ; 0x00000D0C, line  881
        bic     x23, x8, x23, ror #38                          ; 0x00000D10, line  882
        eor     x8, x27, x0, ror #2                            ; 0x00000D14, line  883
        eor     x4, x23, x3, ror #47                           ; 0x00000D18, line  884
        bic     x3, x0, x30, ror #5                            ; 0x00000D1C, line  885
        eor     x23, x3, x26, ror #52                          ; 0x00000D20, line  886
        eor     x3, x29, x30, ror #24                          ; 0x00000D24, line  887
        ldr     x30, [sp, #0x10]                               ; 0x00000D28, line  888
        ld1r    { v28.2d }, [x30], #8                          ; 0x00000D2C, line  889
        str     x30, [sp, #0x10]                               ; 0x00000D30, line  890
        eor     v0.16b, v0.16b, v28.16b                        ; 0x00000D34, line  891
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x4_v8a_scalar_hybrid_loop_end

        b.le    Lmld_keccak_f1600_x4_v8a_scalar_hybrid_loop    ; 0x00000D40, line  894
        ror     x2, x2, #0x3d                                  ; 0x00000D44, line  895
        ror     x3, x3, #0x27                                  ; 0x00000D48, line  896
        ror     x4, x4, #0x36                                  ; 0x00000D4C, line  897
        ror     x5, x5, #0x19                                  ; 0x00000D50, line  898
        ror     x6, x6, #0x2b                                  ; 0x00000D54, line  899
        ror     x7, x7, #0x13                                  ; 0x00000D58, line  900
        ror     x8, x8, #0x38                                  ; 0x00000D5C, line  901
        ror     x9, x9, #0x31                                  ; 0x00000D60, line  902
        ror     x10, x10, #0x17                                ; 0x00000D64, line  903
        ror     x11, x11, #0x32                                ; 0x00000D68, line  904
        ror     x12, x12, #0x3                                 ; 0x00000D6C, line  905
        ror     x13, x13, #0x2e                                ; 0x00000D70, line  906
        ror     x14, x14, #0x8                                 ; 0x00000D74, line  907
        ror     x15, x15, #0x3e                                ; 0x00000D78, line  908
        ror     x17, x17, #0x24                                ; 0x00000D7C, line  909
        ror     x28, x28, #0x3f                                ; 0x00000D80, line  910
        ror     x19, x19, #0x25                                ; 0x00000D84, line  911
        ror     x20, x20, #0x2                                 ; 0x00000D88, line  912
        ror     x21, x21, #0x14                                ; 0x00000D8C, line  913
        ror     x22, x22, #0x2c                                ; 0x00000D90, line  914
        ror     x23, x23, #0x3a                                ; 0x00000D94, line  915
        ror     x24, x24, #0x1c                                ; 0x00000D98, line  916
        ror     x25, x25, #0x9                                 ; 0x00000D9C, line  917
        ldr     x30, [sp, #0x20]                               ; 0x00000DA0, line  918
        cmp     x30, #0x1                                      ; 0x00000DA4, line  919
        b.eq    Lmld_keccak_f1600_x4_v8a_scalar_hybrid_done    ; 0x00000DA8, line  920
        mov     x30, #0x1                                      ; 0x00000DAC, line  921
        str     x30, [sp, #0x20]                               ; 0x00000DB0, line  922
        ldr     x0, [sp]                                       ; 0x00000DB4, line  923
        add     x0, x0, #0x190                                 ; 0x00000DB8, line  924
        stp     x1, x6, [x0]                                   ; 0x00000DBC, line  925
        stp     x11, x16, [x0, #0x10]                          ; 0x00000DC0, line  926
        stp     x21, x2, [x0, #0x20]                           ; 0x00000DC4, line  927
        stp     x7, x12, [x0, #0x30]                           ; 0x00000DC8, line  928
        stp     x17, x22, [x0, #0x40]                          ; 0x00000DCC, line  929
        stp     x3, x8, [x0, #0x50]                            ; 0x00000DD0, line  930
        stp     x13, x28, [x0, #0x60]                          ; 0x00000DD4, line  931
        stp     x23, x4, [x0, #0x70]                           ; 0x00000DD8, line  932
        stp     x9, x14, [x0, #0x80]                           ; 0x00000DDC, line  933
        stp     x19, x24, [x0, #0x90]                          ; 0x00000DE0, line  934
        stp     x5, x10, [x0, #0xa0]                           ; 0x00000DE4, line  935
        stp     x15, x20, [x0, #0xb0]                          ; 0x00000DE8, line  936
        str     x25, [x0, #0xc0]                               ; 0x00000DEC, line  937
        sub     x0, x0, #0x190                                 ; 0x00000DF0, line  938
        add     x0, x0, #0x258                                 ; 0x00000DF4, line  939
        ldp     x1, x6, [x0]                                   ; 0x00000DF8, line  940
        ldp     x11, x16, [x0, #0x10]                          ; 0x00000DFC, line  941
        ldp     x21, x2, [x0, #0x20]                           ; 0x00000E00, line  942
        ldp     x7, x12, [x0, #0x30]                           ; 0x00000E04, line  943
        ldp     x17, x22, [x0, #0x40]                          ; 0x00000E08, line  944
        ldp     x3, x8, [x0, #0x50]                            ; 0x00000E0C, line  945
        ldp     x13, x28, [x0, #0x60]                          ; 0x00000E10, line  946
        ldp     x23, x4, [x0, #0x70]                           ; 0x00000E14, line  947
        ldp     x9, x14, [x0, #0x80]                           ; 0x00000E18, line  948
        ldp     x19, x24, [x0, #0x90]                          ; 0x00000E1C, line  949
        ldp     x5, x10, [x0, #0xa0]                           ; 0x00000E20, line  950
        ldp     x15, x20, [x0, #0xb0]                          ; 0x00000E24, line  951
        ldr     x25, [x0, #0xc0]                               ; 0x00000E28, line  952
        sub     x0, x0, #0x258                                 ; 0x00000E2C, line  953
        b       Lmld_keccak_f1600_x4_v8a_scalar_hybrid_initial ; 0x00000E30, line  954
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                           ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x4_v8a_scalar_hybrid_done

        ldr     x0, [sp]                                       ; 0x00000E40, line  957
        add     x0, x0, #0x258                                 ; 0x00000E44, line  958
        stp     x1, x6, [x0]                                   ; 0x00000E48, line  959
        stp     x11, x16, [x0, #0x10]                          ; 0x00000E4C, line  960
        stp     x21, x2, [x0, #0x20]                           ; 0x00000E50, line  961
        stp     x7, x12, [x0, #0x30]                           ; 0x00000E54, line  962
        stp     x17, x22, [x0, #0x40]                          ; 0x00000E58, line  963
        stp     x3, x8, [x0, #0x50]                            ; 0x00000E5C, line  964
        stp     x13, x28, [x0, #0x60]                          ; 0x00000E60, line  965
        stp     x23, x4, [x0, #0x70]                           ; 0x00000E64, line  966
        stp     x9, x14, [x0, #0x80]                           ; 0x00000E68, line  967
        stp     x19, x24, [x0, #0x90]                          ; 0x00000E6C, line  968
        stp     x5, x10, [x0, #0xa0]                           ; 0x00000E70, line  969
        stp     x15, x20, [x0, #0xb0]                          ; 0x00000E74, line  970
        str     x25, [x0, #0xc0]                               ; 0x00000E78, line  971
        sub     x0, x0, #0x258                                 ; 0x00000E7C, line  972
        add     x4, x0, #0xc8                                  ; 0x00000E80, line  973
        trn1    v25.2d, v0.2d, v1.2d                           ; 0x00000E84, line  974
        trn1    v26.2d, v2.2d, v3.2d                           ; 0x00000E88, line  975
        stp     q25, q26, [x0], #0x20                          ; 0x00000E8C, line  976
        trn2    v27.2d, v0.2d, v1.2d                           ; 0x00000E90, line  977
        trn2    v28.2d, v2.2d, v3.2d                           ; 0x00000E94, line  978
        st1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000E98, line  979
        trn1    v25.2d, v4.2d, v5.2d                           ; 0x00000E9C, line  980
        trn1    v26.2d, v6.2d, v7.2d                           ; 0x00000EA0, line  981
        stp     q25, q26, [x0], #0x20                          ; 0x00000EA4, line  982
        trn2    v27.2d, v4.2d, v5.2d                           ; 0x00000EA8, line  983
        trn2    v28.2d, v6.2d, v7.2d                           ; 0x00000EAC, line  984
        st1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000EB0, line  985
        trn1    v25.2d, v8.2d, v9.2d                           ; 0x00000EB4, line  986
        trn1    v26.2d, v10.2d, v11.2d                         ; 0x00000EB8, line  987
        stp     q25, q26, [x0], #0x20                          ; 0x00000EBC, line  988
        trn2    v27.2d, v8.2d, v9.2d                           ; 0x00000EC0, line  989
        trn2    v28.2d, v10.2d, v11.2d                         ; 0x00000EC4, line  990
        st1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000EC8, line  991
        trn1    v25.2d, v12.2d, v13.2d                         ; 0x00000ECC, line  992
        trn1    v26.2d, v14.2d, v15.2d                         ; 0x00000ED0, line  993
        stp     q25, q26, [x0], #0x20                          ; 0x00000ED4, line  994
        trn2    v27.2d, v12.2d, v13.2d                         ; 0x00000ED8, line  995
        trn2    v28.2d, v14.2d, v15.2d                         ; 0x00000EDC, line  996
        st1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000EE0, line  997
        trn1    v25.2d, v16.2d, v17.2d                         ; 0x00000EE4, line  998
        trn1    v26.2d, v18.2d, v19.2d                         ; 0x00000EE8, line  999
        stp     q25, q26, [x0], #0x20                          ; 0x00000EEC, line 1000
        trn2    v27.2d, v16.2d, v17.2d                         ; 0x00000EF0, line 1001
        trn2    v28.2d, v18.2d, v19.2d                         ; 0x00000EF4, line 1002
        st1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000EF8, line 1003
        trn1    v25.2d, v20.2d, v21.2d                         ; 0x00000EFC, line 1004
        trn1    v26.2d, v22.2d, v23.2d                         ; 0x00000F00, line 1005
        stp     q25, q26, [x0], #0x20                          ; 0x00000F04, line 1006
        trn2    v27.2d, v20.2d, v21.2d                         ; 0x00000F08, line 1007
        trn2    v28.2d, v22.2d, v23.2d                         ; 0x00000F0C, line 1008
        st1     { v27.2d, v28.2d }, [x4], #32                  ; 0x00000F10, line 1009
        str     d24, [x0]                                      ; 0x00000F14, line 1010
        trn2    v25.2d, v24.2d, v24.2d                         ; 0x00000F18, line 1011
        str     d25, [x4]                                      ; 0x00000F1C, line 1012
        ldp     d8, d9, [sp, #0x90]                            ; 0x00000F20, line 1013
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp     d10, d11, [sp, #0xa0]                          ; 0x00000F24, line 1016
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp     d12, d13, [sp, #0xb0]                          ; 0x00000F28, line 1019
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp     d14, d15, [sp, #0xc0]                          ; 0x00000F2C, line 1022
        ; .cfi_restore d14
        ; .cfi_restore d15
        ldp     x19, x20, [sp, #0x30]                          ; 0x00000F30, line 1025
        ; .cfi_restore x19
        ; .cfi_restore x20
        ldp     x21, x22, [sp, #0x40]                          ; 0x00000F34, line 1028
        ; .cfi_restore x21
        ; .cfi_restore x22
        ldp     x23, x24, [sp, #0x50]                          ; 0x00000F38, line 1031
        ; .cfi_restore x23
        ; .cfi_restore x24
        ldp     x25, x26, [sp, #0x60]                          ; 0x00000F3C, line 1034
        ; .cfi_restore x25
        ; .cfi_restore x26
        ldp     x27, x28, [sp, #0x70]                          ; 0x00000F40, line 1037
        ; .cfi_restore x27
        ; .cfi_restore x28
        ldp     x29, x30, [sp, #0x80]                          ; 0x00000F44, line 1040
        ; .cfi_restore x29
        ; .cfi_restore x30
        add     sp, sp, #0xe0                                  ; 0x00000F48, line 1043
        ; .cfi_adjust_cfa_offset -0xE0
        ret                                                    ; 0x00000F4C, line 1045
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000F50 byte(s)

        AREA    |.xdata|, DATA, READONLY

XDATA_$FUNC_NAME

        DCD     0x302003D4                                     ; header dword
        DCB     0xD9, 0x98                                     ; unwind code 'save_fregp', registers d14,d15 at stack offset 0x00C0
        DCB     0xD9, 0x16                                     ; unwind code 'save_fregp', registers d12,d13 at stack offset 0x00B0
        DCB     0xD8, 0x94                                     ; unwind code 'save_fregp', registers d10,d11 at stack offset 0x00A0
        DCB     0xD8, 0x12                                     ; unwind code 'save_fregp', registers d8,d9 at stack offset 0x0090
        DCB     0xCA, 0x90                                     ; unwind code 'save_regp', registers x29,x30 at stack offset 0x0080
        DCB     0xCA, 0x0E                                     ; unwind code 'save_regp', registers x27,x28 at stack offset 0x0070
        DCB     0xC9, 0x8C                                     ; unwind code 'save_regp', registers x25,x26 at stack offset 0x0060
        DCB     0xC9, 0x0A                                     ; unwind code 'save_regp', registers x23,x24 at stack offset 0x0050
        DCB     0xC8, 0x88                                     ; unwind code 'save_regp', registers x21,x22 at stack offset 0x0040
        DCB     0xC8, 0x06                                     ; unwind code 'save_regp', registers x19,x20 at stack offset 0x0030
        DCB     0x0E                                           ; unwind code 'alloc_s', stack space 0x00E0
        DCB     0xE4                                           ; unwind code 'end'
        DCB     0x00, 0x00                                     ; unwind code padding

        AREA    |.pdata|, DATA, READONLY

        DCD     $FUNC_NAME                                     ; function start RVA
        RELOC   0x0002                                         ; IMAGE_REL_ARM64_ADDR32NB (currently ignored by armasm64.exe)
        DCD     XDATA_$FUNC_NAME                               ; pointer in XDATA section
        RELOC   0x0002                                         ; IMAGE_REL_ARM64_ADDR32NB (currently ignored by armasm64.exe)

        END
