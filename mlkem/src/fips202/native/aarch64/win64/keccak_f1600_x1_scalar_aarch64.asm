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
; Name: keccak_f1600_x1_scalar_aarch64_asm
; Description: AArch64 scalar implementation of Keccak-f[1600] permutation for single state
; Signature: void mld_keccak_f1600_x1_scalar_aarch64_asm(uint64_t state[25], const uint64_t rc[24])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   x0:
;     type: buffer
;     size_bytes: 200
;     permissions: read/write
;     c_parameter: uint64_t state[25]
;     description: Keccak state (25 x uint64_t)
;   x1:
;     type: buffer
;     size_bytes: 192
;     permissions: read-only
;     c_parameter: uint64_t const *rc
;     description: Round constants (24 x uint64_t)
; Stack:
;   bytes: 128
;   description: register preservation and temporary storage
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mldsa_keccak_f1600_x1_scalar_aarch64_asm"
        ENDIF

        AREA    |.drectve|, DRECTVE

        EXPORT  $FUNC_NAME

        AREA    |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN   16

$FUNC_NAME PROC

        ; .cfi_startproc
        sub     sp, sp, #0x80                           ; 0x00000000, line   26
        ; .cfi_adjust_cfa_offset 0x80
        stp     x19, x20, [sp, #0x20]                   ; 0x00000004, line   28
        ; .cfi_rel_offset x19, 0x20
        ; .cfi_rel_offset x20, 0x28
        stp     x21, x22, [sp, #0x30]                   ; 0x00000008, line   31
        ; .cfi_rel_offset x21, 0x30
        ; .cfi_rel_offset x22, 0x38
        stp     x23, x24, [sp, #0x40]                   ; 0x0000000C, line   34
        ; .cfi_rel_offset x23, 0x40
        ; .cfi_rel_offset x24, 0x48
        stp     x25, x26, [sp, #0x50]                   ; 0x00000010, line   37
        ; .cfi_rel_offset x25, 0x50
        ; .cfi_rel_offset x26, 0x58
        stp     x27, x28, [sp, #0x60]                   ; 0x00000014, line   40
        ; .cfi_rel_offset x27, 0x60
        ; .cfi_rel_offset x28, 0x68
        stp     x29, x30, [sp, #0x70]                   ; 0x00000018, line   43
        ; .cfi_rel_offset x29, 0x70
        ; .cfi_rel_offset x30, 0x78
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x1_scalar_initial

        mov     x26, x1                                 ; 0x00000020, line   48
        str     x1, [sp, #0x8]                          ; 0x00000024, line   49
        ldp     x1, x6, [x0]                            ; 0x00000028, line   50
        ldp     x11, x16, [x0, #0x10]                   ; 0x0000002C, line   51
        ldp     x21, x2, [x0, #0x20]                    ; 0x00000030, line   52
        ldp     x7, x12, [x0, #0x30]                    ; 0x00000034, line   53
        ldp     x17, x22, [x0, #0x40]                   ; 0x00000038, line   54
        ldp     x3, x8, [x0, #0x50]                     ; 0x0000003C, line   55
        ldp     x13, x28, [x0, #0x60]                   ; 0x00000040, line   56
        ldp     x23, x4, [x0, #0x70]                    ; 0x00000044, line   57
        ldp     x9, x14, [x0, #0x80]                    ; 0x00000048, line   58
        ldp     x19, x24, [x0, #0x90]                   ; 0x0000004C, line   59
        ldp     x5, x10, [x0, #0xa0]                    ; 0x00000050, line   60
        ldp     x15, x20, [x0, #0xb0]                   ; 0x00000054, line   61
        ldr     x25, [x0, #0xc0]                        ; 0x00000058, line   62
        str     x0, [sp]                                ; 0x0000005C, line   63
        eor     x30, x24, x25                           ; 0x00000060, line   64
        eor     x27, x9, x10                            ; 0x00000064, line   65
        eor     x0, x30, x21                            ; 0x00000068, line   66
        eor     x26, x27, x6                            ; 0x0000006C, line   67
        eor     x27, x26, x7                            ; 0x00000070, line   68
        eor     x29, x0, x22                            ; 0x00000074, line   69
        eor     x26, x29, x23                           ; 0x00000078, line   70
        eor     x29, x4, x5                             ; 0x0000007C, line   71
        eor     x30, x29, x1                            ; 0x00000080, line   72
        eor     x0, x27, x8                             ; 0x00000084, line   73
        eor     x29, x30, x2                            ; 0x00000088, line   74
        eor     x30, x19, x20                           ; 0x0000008C, line   75
        eor     x30, x30, x16                           ; 0x00000090, line   76
        eor     x27, x26, x0, ror #63                   ; 0x00000094, line   77
        eor     x4, x4, x27                             ; 0x00000098, line   78
        eor     x30, x30, x17                           ; 0x0000009C, line   79
        eor     x30, x30, x28                           ; 0x000000A0, line   80
        eor     x29, x29, x3                            ; 0x000000A4, line   81
        eor     x0, x0, x30, ror #63                    ; 0x000000A8, line   82
        eor     x30, x30, x29, ror #63                  ; 0x000000AC, line   83
        eor     x22, x22, x30                           ; 0x000000B0, line   84
        eor     x23, x23, x30                           ; 0x000000B4, line   85
        str     x23, [sp, #0x18]                        ; 0x000000B8, line   86
        eor     x23, x14, x15                           ; 0x000000BC, line   87
        eor     x14, x14, x0                            ; 0x000000C0, line   88
        eor     x23, x23, x11                           ; 0x000000C4, line   89
        eor     x15, x15, x0                            ; 0x000000C8, line   90
        eor     x1, x1, x27                             ; 0x000000CC, line   91
        eor     x23, x23, x12                           ; 0x000000D0, line   92
        eor     x23, x23, x13                           ; 0x000000D4, line   93
        eor     x11, x11, x0                            ; 0x000000D8, line   94
        eor     x29, x29, x23, ror #63                  ; 0x000000DC, line   95
        eor     x23, x23, x26, ror #63                  ; 0x000000E0, line   96
        eor     x26, x13, x0                            ; 0x000000E4, line   97
        eor     x13, x28, x23                           ; 0x000000E8, line   98
        eor     x28, x24, x30                           ; 0x000000EC, line   99
        eor     x24, x16, x23                           ; 0x000000F0, line  100
        eor     x16, x21, x30                           ; 0x000000F4, line  101
        eor     x21, x25, x30                           ; 0x000000F8, line  102
        eor     x30, x19, x23                           ; 0x000000FC, line  103
        eor     x19, x20, x23                           ; 0x00000100, line  104
        eor     x20, x17, x23                           ; 0x00000104, line  105
        eor     x17, x12, x0                            ; 0x00000108, line  106
        eor     x0, x2, x27                             ; 0x0000010C, line  107
        eor     x2, x6, x29                             ; 0x00000110, line  108
        eor     x6, x8, x29                             ; 0x00000114, line  109
        bic     x8, x28, x13, ror #47                   ; 0x00000118, line  110
        eor     x12, x3, x27                            ; 0x0000011C, line  111
        bic     x3, x13, x17, ror #19                   ; 0x00000120, line  112
        eor     x5, x5, x27                             ; 0x00000124, line  113
        ldr     x27, [sp, #0x18]                        ; 0x00000128, line  114
        bic     x25, x17, x2, ror #5                    ; 0x0000012C, line  115
        eor     x9, x9, x29                             ; 0x00000130, line  116
        eor     x23, x25, x5, ror #52                   ; 0x00000134, line  117
        eor     x3, x3, x2, ror #24                     ; 0x00000138, line  118
        eor     x8, x8, x17, ror #2                     ; 0x0000013C, line  119
        eor     x17, x10, x29                           ; 0x00000140, line  120
        bic     x25, x12, x22, ror #47                  ; 0x00000144, line  121
        eor     x29, x7, x29                            ; 0x00000148, line  122
        bic     x10, x4, x27, ror #2                    ; 0x0000014C, line  123
        bic     x7, x5, x28, ror #10                    ; 0x00000150, line  124
        eor     x10, x10, x20, ror #50                  ; 0x00000154, line  125
        eor     x13, x7, x13, ror #57                   ; 0x00000158, line  126
        bic     x7, x2, x5, ror #47                     ; 0x0000015C, line  127
        eor     x2, x25, x24, ror #39                   ; 0x00000160, line  128
        bic     x25, x20, x11, ror #57                  ; 0x00000164, line  129
        bic     x5, x17, x4, ror #25                    ; 0x00000168, line  130
        eor     x25, x25, x17, ror #53                  ; 0x0000016C, line  131
        bic     x17, x11, x17, ror #60                  ; 0x00000170, line  132
        eor     x28, x7, x28, ror #57                   ; 0x00000174, line  133
        bic     x7, x9, x12, ror #42                    ; 0x00000178, line  134
        eor     x7, x7, x22, ror #25                    ; 0x0000017C, line  135
        bic     x22, x22, x24, ror #56                  ; 0x00000180, line  136
        bic     x24, x24, x15, ror #31                  ; 0x00000184, line  137
        eor     x22, x22, x15, ror #23                  ; 0x00000188, line  138
        bic     x20, x27, x20, ror #48                  ; 0x0000018C, line  139
        bic     x15, x15, x9, ror #16                   ; 0x00000190, line  140
        eor     x12, x15, x12, ror #58                  ; 0x00000194, line  141
        eor     x15, x5, x27, ror #27                   ; 0x00000198, line  142
        eor     x5, x20, x11, ror #41                   ; 0x0000019C, line  143
        ldr     x11, [sp, #0x8]                         ; 0x000001A0, line  144
        eor     x20, x17, x4, ror #21                   ; 0x000001A4, line  145
        eor     x17, x24, x9, ror #47                   ; 0x000001A8, line  146
        mov     x24, #0x1                               ; 0x000001AC, line  147
        bic     x9, x0, x16, ror #9                     ; 0x000001B0, line  148
        str     x24, [sp, #0x10]                        ; 0x000001B4, line  149
        bic     x24, x29, x1, ror #44                   ; 0x000001B8, line  150
        bic     x27, x1, x21, ror #50                   ; 0x000001BC, line  151
        bic     x4, x26, x29, ror #63                   ; 0x000001C0, line  152
        eor     x1, x1, x4, ror #21                     ; 0x000001C4, line  153
        ldr     x11, [x11]                              ; 0x000001C8, line  154
        bic     x4, x21, x30, ror #57                   ; 0x000001CC, line  155
        eor     x21, x24, x21, ror #30                  ; 0x000001D0, line  156
        eor     x24, x9, x19, ror #44                   ; 0x000001D4, line  157
        bic     x9, x14, x6, ror #5                     ; 0x000001D8, line  158
        eor     x9, x9, x0, ror #43                     ; 0x000001DC, line  159
        bic     x0, x6, x0, ror #38                     ; 0x000001E0, line  160
        eor     x1, x1, x11                             ; 0x000001E4, line  161
        eor     x11, x4, x26, ror #35                   ; 0x000001E8, line  162
        eor     x4, x0, x16, ror #47                    ; 0x000001EC, line  163
        bic     x0, x16, x19, ror #35                   ; 0x000001F0, line  164
        eor     x16, x27, x30, ror #43                  ; 0x000001F4, line  165
        bic     x27, x30, x26, ror #42                  ; 0x000001F8, line  166
        bic     x26, x19, x14, ror #41                  ; 0x000001FC, line  167
        eor     x19, x0, x14, ror #12                   ; 0x00000200, line  168
        eor     x14, x26, x6, ror #46                   ; 0x00000204, line  169
        eor     x6, x27, x29, ror #41                   ; 0x00000208, line  170
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x1_scalar_loop

        eor     x0, x15, x11, ror #52                   ; 0x00000210, line  173
        eor     x0, x0, x13, ror #48                    ; 0x00000214, line  174
        eor     x26, x8, x9, ror #57                    ; 0x00000218, line  175
        eor     x27, x0, x14, ror #10                   ; 0x0000021C, line  176
        eor     x29, x16, x28, ror #63                  ; 0x00000220, line  177
        eor     x26, x26, x6, ror #51                   ; 0x00000224, line  178
        eor     x30, x23, x22, ror #50                  ; 0x00000228, line  179
        eor     x0, x26, x10, ror #31                   ; 0x0000022C, line  180
        eor     x29, x29, x19, ror #37                  ; 0x00000230, line  181
        eor     x27, x27, x12, ror #5                   ; 0x00000234, line  182
        eor     x30, x30, x24, ror #34                  ; 0x00000238, line  183
        eor     x0, x0, x7, ror #27                     ; 0x0000023C, line  184
        eor     x26, x30, x21, ror #26                  ; 0x00000240, line  185
        eor     x26, x26, x25, ror #15                  ; 0x00000244, line  186
        ror     x30, x27, #0x3e                         ; 0x00000248, line  187
        eor     x30, x30, x26, ror #57                  ; 0x0000024C, line  188
        ror     x26, x26, #0x3a                         ; 0x00000250, line  189
        eor     x16, x30, x16                           ; 0x00000254, line  190
        eor     x28, x30, x28, ror #63                  ; 0x00000258, line  191
        str     x28, [sp, #0x18]                        ; 0x0000025C, line  192
        eor     x29, x29, x17, ror #36                  ; 0x00000260, line  193
        eor     x28, x1, x2, ror #61                    ; 0x00000264, line  194
        eor     x19, x30, x19, ror #37                  ; 0x00000268, line  195
        eor     x29, x29, x20, ror #2                   ; 0x0000026C, line  196
        eor     x28, x28, x4, ror #54                   ; 0x00000270, line  197
        eor     x26, x26, x0, ror #55                   ; 0x00000274, line  198
        eor     x28, x28, x3, ror #39                   ; 0x00000278, line  199
        eor     x28, x28, x5, ror #25                   ; 0x0000027C, line  200
        ror     x0, x0, #0x38                           ; 0x00000280, line  201
        eor     x0, x0, x29, ror #63                    ; 0x00000284, line  202
        eor     x27, x28, x27, ror #61                  ; 0x00000288, line  203
        eor     x13, x0, x13, ror #46                   ; 0x0000028C, line  204
        eor     x28, x29, x28, ror #63                  ; 0x00000290, line  205
        eor     x29, x30, x20, ror #2                   ; 0x00000294, line  206
        eor     x20, x26, x3, ror #39                   ; 0x00000298, line  207
        eor     x11, x0, x11, ror #50                   ; 0x0000029C, line  208
        eor     x25, x28, x25, ror #9                   ; 0x000002A0, line  209
        eor     x3, x28, x21, ror #20                   ; 0x000002A4, line  210
        eor     x21, x26, x1                            ; 0x000002A8, line  211
        eor     x9, x27, x9, ror #49                    ; 0x000002AC, line  212
        eor     x24, x28, x24, ror #28                  ; 0x000002B0, line  213
        eor     x1, x30, x17, ror #36                   ; 0x000002B4, line  214
        eor     x14, x0, x14, ror #8                    ; 0x000002B8, line  215
        eor     x22, x28, x22, ror #44                  ; 0x000002BC, line  216
        eor     x8, x27, x8, ror #56                    ; 0x000002C0, line  217
        eor     x17, x27, x7, ror #19                   ; 0x000002C4, line  218
        eor     x15, x0, x15, ror #62                   ; 0x000002C8, line  219
        bic     x7, x20, x22, ror #47                   ; 0x000002CC, line  220
        eor     x4, x26, x4, ror #54                    ; 0x000002D0, line  221
        eor     x0, x0, x12, ror #3                     ; 0x000002D4, line  222
        eor     x28, x28, x23, ror #58                  ; 0x000002D8, line  223
        eor     x23, x26, x2, ror #61                   ; 0x000002DC, line  224
        eor     x26, x26, x5, ror #25                   ; 0x000002E0, line  225
        eor     x2, x7, x16, ror #39                    ; 0x000002E4, line  226
        bic     x7, x9, x20, ror #42                    ; 0x000002E8, line  227
        bic     x30, x15, x9, ror #16                   ; 0x000002EC, line  228
        eor     x7, x7, x22, ror #25                    ; 0x000002F0, line  229
        eor     x12, x30, x20, ror #58                  ; 0x000002F4, line  230
        bic     x20, x22, x16, ror #56                  ; 0x000002F8, line  231
        eor     x30, x27, x6, ror #43                   ; 0x000002FC, line  232
        eor     x22, x20, x15, ror #23                  ; 0x00000300, line  233
        bic     x6, x19, x13, ror #42                   ; 0x00000304, line  234
        eor     x6, x6, x17, ror #41                    ; 0x00000308, line  235
        bic     x5, x13, x17, ror #63                   ; 0x0000030C, line  236
        eor     x5, x21, x5, ror #21                    ; 0x00000310, line  237
        bic     x17, x17, x21, ror #44                  ; 0x00000314, line  238
        eor     x27, x27, x10, ror #23                  ; 0x00000318, line  239
        bic     x21, x21, x25, ror #50                  ; 0x0000031C, line  240
        bic     x20, x27, x4, ror #25                   ; 0x00000320, line  241
        bic     x10, x16, x15, ror #31                  ; 0x00000324, line  242
        eor     x16, x21, x19, ror #43                  ; 0x00000328, line  243
        eor     x21, x17, x25, ror #30                  ; 0x0000032C, line  244
        bic     x19, x25, x19, ror #57                  ; 0x00000330, line  245
        ldr     x25, [sp, #0x10]                        ; 0x00000334, line  246
        eor     x17, x10, x9, ror #47                   ; 0x00000338, line  247
        ldr     x9, [sp, #0x8]                          ; 0x0000033C, line  248
        eor     x15, x20, x28, ror #27                  ; 0x00000340, line  249
        bic     x20, x4, x28, ror #2                    ; 0x00000344, line  250
        eor     x10, x20, x1, ror #50                   ; 0x00000348, line  251
        bic     x20, x11, x27, ror #60                  ; 0x0000034C, line  252
        eor     x20, x20, x4, ror #21                   ; 0x00000350, line  253
        bic     x4, x28, x1, ror #48                    ; 0x00000354, line  254
        bic     x1, x1, x11, ror #57                    ; 0x00000358, line  255
        ldr     x28, [x9, x25, lsl #3]                  ; 0x0000035C, line  256
        ldr     x9, [sp, #0x18]                         ; 0x00000360, line  257
        add     x25, x25, #0x1                          ; 0x00000364, line  258
        str     x25, [sp, #0x10]                        ; 0x00000368, line  259
        cmp     x25, #0x17                              ; 0x0000036C, line  260
        eor     x25, x1, x27, ror #53                   ; 0x00000370, line  261
        bic     x27, x30, x26, ror #47                  ; 0x00000374, line  262
        eor     x1, x5, x28                             ; 0x00000378, line  263
        eor     x5, x4, x11, ror #41                    ; 0x0000037C, line  264
        eor     x11, x19, x13, ror #35                  ; 0x00000380, line  265
        bic     x13, x26, x24, ror #10                  ; 0x00000384, line  266
        eor     x28, x27, x24, ror #57                  ; 0x00000388, line  267
        bic     x27, x24, x9, ror #47                   ; 0x0000038C, line  268
        bic     x19, x23, x3, ror #9                    ; 0x00000390, line  269
        bic     x4, x29, x14, ror #41                   ; 0x00000394, line  270
        eor     x24, x19, x29, ror #44                  ; 0x00000398, line  271
        bic     x29, x3, x29, ror #35                   ; 0x0000039C, line  272
        eor     x13, x13, x9, ror #57                   ; 0x000003A0, line  273
        eor     x19, x29, x14, ror #12                  ; 0x000003A4, line  274
        bic     x29, x9, x0, ror #19                    ; 0x000003A8, line  275
        bic     x14, x14, x8, ror #5                    ; 0x000003AC, line  276
        eor     x9, x14, x23, ror #43                   ; 0x000003B0, line  277
        eor     x14, x4, x8, ror #46                    ; 0x000003B4, line  278
        bic     x23, x8, x23, ror #38                   ; 0x000003B8, line  279
        eor     x8, x27, x0, ror #2                     ; 0x000003BC, line  280
        eor     x4, x23, x3, ror #47                    ; 0x000003C0, line  281
        bic     x3, x0, x30, ror #5                     ; 0x000003C4, line  282
        eor     x23, x3, x26, ror #52                   ; 0x000003C8, line  283
        eor     x3, x29, x30, ror #24                   ; 0x000003CC, line  284
        b.le    Lmld_keccak_f1600_x1_scalar_loop        ; 0x000003D0, line  285
        ror     x6, x6, #0x2b                           ; 0x000003D4, line  286
        ror     x11, x11, #0x32                         ; 0x000003D8, line  287
        ror     x21, x21, #0x14                         ; 0x000003DC, line  288
        ror     x2, x2, #0x3d                           ; 0x000003E0, line  289
        ror     x7, x7, #0x13                           ; 0x000003E4, line  290
        ror     x12, x12, #0x3                          ; 0x000003E8, line  291
        ror     x17, x17, #0x24                         ; 0x000003EC, line  292
        ror     x22, x22, #0x2c                         ; 0x000003F0, line  293
        ror     x3, x3, #0x27                           ; 0x000003F4, line  294
        ror     x8, x8, #0x38                           ; 0x000003F8, line  295
        ror     x13, x13, #0x2e                         ; 0x000003FC, line  296
        ror     x28, x28, #0x3f                         ; 0x00000400, line  297
        ror     x23, x23, #0x3a                         ; 0x00000404, line  298
        ror     x4, x4, #0x36                           ; 0x00000408, line  299
        ror     x9, x9, #0x31                           ; 0x0000040C, line  300
        ror     x14, x14, #0x8                          ; 0x00000410, line  301
        ror     x19, x19, #0x25                         ; 0x00000414, line  302
        ror     x24, x24, #0x1c                         ; 0x00000418, line  303
        ror     x5, x5, #0x19                           ; 0x0000041C, line  304
        ror     x10, x10, #0x17                         ; 0x00000420, line  305
        ror     x15, x15, #0x3e                         ; 0x00000424, line  306
        ror     x20, x20, #0x2                          ; 0x00000428, line  307
        ror     x25, x25, #0x9                          ; 0x0000042C, line  308
        ldr     x0, [sp]                                ; 0x00000430, line  309
        stp     x1, x6, [x0]                            ; 0x00000434, line  310
        stp     x11, x16, [x0, #0x10]                   ; 0x00000438, line  311
        stp     x21, x2, [x0, #0x20]                    ; 0x0000043C, line  312
        stp     x7, x12, [x0, #0x30]                    ; 0x00000440, line  313
        stp     x17, x22, [x0, #0x40]                   ; 0x00000444, line  314
        stp     x3, x8, [x0, #0x50]                     ; 0x00000448, line  315
        stp     x13, x28, [x0, #0x60]                   ; 0x0000044C, line  316
        stp     x23, x4, [x0, #0x70]                    ; 0x00000450, line  317
        stp     x9, x14, [x0, #0x80]                    ; 0x00000454, line  318
        stp     x19, x24, [x0, #0x90]                   ; 0x00000458, line  319
        stp     x5, x10, [x0, #0xa0]                    ; 0x0000045C, line  320
        stp     x15, x20, [x0, #0xb0]                   ; 0x00000460, line  321
        str     x25, [x0, #0xc0]                        ; 0x00000464, line  322
        ldp     x19, x20, [sp, #0x20]                   ; 0x00000468, line  323
        ; .cfi_restore x19
        ; .cfi_restore x20
        ldp     x21, x22, [sp, #0x30]                   ; 0x0000046C, line  326
        ; .cfi_restore x21
        ; .cfi_restore x22
        ldp     x23, x24, [sp, #0x40]                   ; 0x00000470, line  329
        ; .cfi_restore x23
        ; .cfi_restore x24
        ldp     x25, x26, [sp, #0x50]                   ; 0x00000474, line  332
        ; .cfi_restore x25
        ; .cfi_restore x26
        ldp     x27, x28, [sp, #0x60]                   ; 0x00000478, line  335
        ; .cfi_restore x27
        ; .cfi_restore x28
        ldp     x29, x30, [sp, #0x70]                   ; 0x0000047C, line  338
        ; .cfi_restore x29
        ; .cfi_restore x30
        add     sp, sp, #0x80                           ; 0x00000480, line  341
        ; .cfi_adjust_cfa_offset -0x80
        ret                                             ; 0x00000484, line  343
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000488 byte(s)

        AREA    |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD     0x20200122                              ; header dword
        DCB     0xCA, 0x8E                              ; unwind code 'save_regp', registers x29,x30 at stack offset 0x0070
        DCB     0xCA, 0x0C                              ; unwind code 'save_regp', registers x27,x28 at stack offset 0x0060
        DCB     0xC9, 0x8A                              ; unwind code 'save_regp', registers x25,x26 at stack offset 0x0050
        DCB     0xC9, 0x08                              ; unwind code 'save_regp', registers x23,x24 at stack offset 0x0040
        DCB     0xC8, 0x86                              ; unwind code 'save_regp', registers x21,x22 at stack offset 0x0030
        DCB     0xC8, 0x04                              ; unwind code 'save_regp', registers x19,x20 at stack offset 0x0020
        DCB     0x08                                    ; unwind code 'alloc_s', stack space 0x0080
        DCB     0xE4                                    ; unwind code 'end'
        DCB     0x00, 0x00                              ; unwind code padding

        AREA    |.pdata|, DATA, READONLY, ALIGN=4

        DCD     $FUNC_NAME                              ; function start RVA
        DCD     XDATA_$FUNC_NAME                        ; pointer in XDATA section

        END
