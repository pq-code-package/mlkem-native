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
; Name: polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm
; Description: Re-implementation of asymmetric base multiplication following @[NeonNTT] for k=2
; Signature: void mlk_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm(int16_t r[256], const int16_t a[512], const int16_t b[512], const int16_t b_cache[256])
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
;     size_bytes: 1024
;     permissions: read-only
;     c_parameter: const int16_t a[512]
;     description: Input polynomial vector a
;   x2:
;     type: buffer
;     size_bytes: 1024
;     permissions: read-only
;     c_parameter: const int16_t b[512]
;     description: Input polynomial vector b
;   x3:
;     type: buffer
;     size_bytes: 512
;     permissions: read-only
;     c_parameter: const int16_t b_cache[256]
;     description: Cached values for b
; Stack:
;   bytes: 64
;   description: saving callee-saved Neon registers
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "mlkem_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm"
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
        mov     x13, #0x10                                                    ; 0x00000030, line   60
        ldr     q12, [x1], #0x20                                              ; 0x00000034, line   61
        ldur    q9, [x1, #-0x10]                                              ; 0x00000038, line   62
        ldr     q22, [x2], #0x20                                              ; 0x0000003C, line   63
        ldur    q30, [x2, #-0x10]                                             ; 0x00000040, line   64
        ldr     q6, [x5], #0x20                                               ; 0x00000044, line   65
        ldr     q7, [x4, #0x10]                                               ; 0x00000048, line   66
        ldr     q8, [x4], #0x20                                               ; 0x0000004C, line   67
        ldur    q23, [x5, #-0x10]                                             ; 0x00000050, line   68
        uzp1    v16.8h, v12.8h, v9.8h                                         ; 0x00000054, line   69
        uzp2    v14.8h, v12.8h, v9.8h                                         ; 0x00000058, line   70
        uzp2    v13.8h, v22.8h, v30.8h                                        ; 0x0000005C, line   71
        uzp1    v18.8h, v22.8h, v30.8h                                        ; 0x00000060, line   72
        ld1     { v27.8h }, [x3], #16                                         ; 0x00000064, line   73
        ld1     { v17.8h }, [x6], #16                                         ; 0x00000068, line   74
        smull2  v4.4s, v16.8h, v18.8h                                         ; 0x0000006C, line   75
        ldr     q31, [x1, #0x10]                                              ; 0x00000070, line   76
        smull   v19.4s, v16.4h, v13.4h                                        ; 0x00000074, line   77
        ldr     q24, [x1], #0x20                                              ; 0x00000078, line   78
        smlal   v19.4s, v14.4h, v18.4h                                        ; 0x0000007C, line   79
        ldr     q22, [x2], #0x20                                              ; 0x00000080, line   80
        smlal2  v4.4s, v14.8h, v27.8h                                         ; 0x00000084, line   81
        uzp2    v5.8h, v6.8h, v23.8h                                          ; 0x00000088, line   82
        smull2  v29.4s, v16.8h, v13.8h                                        ; 0x0000008C, line   83
        uzp2    v26.8h, v8.8h, v7.8h                                          ; 0x00000090, line   84
        smlal2  v29.4s, v14.8h, v18.8h                                        ; 0x00000094, line   85
        uzp1    v30.8h, v24.8h, v31.8h                                        ; 0x00000098, line   86
        uzp1    v8.8h, v8.8h, v7.8h                                           ; 0x0000009C, line   87
        smull   v11.4s, v16.4h, v18.4h                                        ; 0x000000A0, line   88
        smlal   v11.4s, v14.4h, v27.4h                                        ; 0x000000A4, line   89
        ldur    q1, [x2, #-0x10]                                              ; 0x000000A8, line   90
        uzp1    v28.8h, v6.8h, v23.8h                                         ; 0x000000AC, line   91
        smlal2  v29.4s, v8.8h, v5.8h                                          ; 0x000000B0, line   92
        ldr     q25, [x5], #0x20                                              ; 0x000000B4, line   93
        smlal   v19.4s, v8.4h, v5.4h                                          ; 0x000000B8, line   94
        ldr     q3, [x4, #0x10]                                               ; 0x000000BC, line   95
        smlal2  v29.4s, v26.8h, v28.8h                                        ; 0x000000C0, line   96
        uzp1    v27.8h, v22.8h, v1.8h                                         ; 0x000000C4, line   97
        smlal   v19.4s, v26.4h, v28.4h                                        ; 0x000000C8, line   98
        ldr     q12, [x4], #0x20                                              ; 0x000000CC, line   99
        smlal2  v4.4s, v8.8h, v28.8h                                          ; 0x000000D0, line  100
        ldur    q21, [x5, #-0x10]                                             ; 0x000000D4, line  101
        smlal2  v4.4s, v26.8h, v17.8h                                         ; 0x000000D8, line  102
        smlal   v11.4s, v8.4h, v28.4h                                         ; 0x000000DC, line  103
        ld1     { v15.8h }, [x6], #16                                         ; 0x000000E0, line  104
        smlal   v11.4s, v26.4h, v17.4h                                        ; 0x000000E4, line  105
        ld1     { v20.8h }, [x3], #16                                         ; 0x000000E8, line  106
        uzp1    v28.8h, v19.8h, v29.8h                                        ; 0x000000EC, line  107
        smull2  v23.4s, v30.8h, v27.8h                                        ; 0x000000F0, line  108
        smull   v26.4s, v30.4h, v27.4h                                        ; 0x000000F4, line  109
        uzp2    v16.8h, v22.8h, v1.8h                                         ; 0x000000F8, line  110
        mul     v28.8h, v28.8h, v2.8h                                         ; 0x000000FC, line  111
        uzp1    v10.8h, v11.8h, v4.8h                                         ; 0x00000100, line  112
        smull2  v8.4s, v30.8h, v16.8h                                         ; 0x00000104, line  113
        mul     v13.8h, v10.8h, v2.8h                                         ; 0x00000108, line  114
        smlal   v19.4s, v28.4h, v0.4h                                         ; 0x0000010C, line  115
        smlal2  v29.4s, v28.8h, v0.8h                                         ; 0x00000110, line  116
        smull   v18.4s, v30.4h, v16.4h                                        ; 0x00000114, line  117
        uzp1    v30.8h, v25.8h, v21.8h                                        ; 0x00000118, line  118
        smlal   v11.4s, v13.4h, v0.4h                                         ; 0x0000011C, line  119
        uzp2    v6.8h, v24.8h, v31.8h                                         ; 0x00000120, line  120
        uzp1    v16.8h, v12.8h, v3.8h                                         ; 0x00000124, line  121
        smlal2  v4.4s, v13.8h, v0.8h                                          ; 0x00000128, line  122
        uzp2    v17.8h, v25.8h, v21.8h                                        ; 0x0000012C, line  123
        smlal2  v8.4s, v6.8h, v27.8h                                          ; 0x00000130, line  124
        uzp2    v12.8h, v12.8h, v3.8h                                         ; 0x00000134, line  125
        smlal   v18.4s, v6.4h, v27.4h                                         ; 0x00000138, line  126
        uzp2    v9.8h, v19.8h, v29.8h                                         ; 0x0000013C, line  127
        smlal2  v8.4s, v16.8h, v17.8h                                         ; 0x00000140, line  128
        smlal2  v8.4s, v12.8h, v30.8h                                         ; 0x00000144, line  129
        uzp2    v19.8h, v11.8h, v4.8h                                         ; 0x00000148, line  130
        sub     x13, x13, #0x2                                                ; 0x0000014C, line  131

Lmlk_polyvec_basemul_acc_montgomery_cached_k2_loop_start

        smlal   v18.4s, v16.4h, v17.4h                                        ; 0x00000150, line  134
        ldr     q7, [x4], #0x20                                               ; 0x00000154, line  135
        ldr     q10, [x2, #0x10]                                              ; 0x00000158, line  136
        smlal   v18.4s, v12.4h, v30.4h                                        ; 0x0000015C, line  137
        smlal2  v23.4s, v6.8h, v20.8h                                         ; 0x00000160, line  138
        ldr     q14, [x2], #0x20                                              ; 0x00000164, line  139
        smlal2  v23.4s, v16.8h, v30.8h                                        ; 0x00000168, line  140
        zip1    v25.8h, v19.8h, v9.8h                                         ; 0x0000016C, line  141
        zip2    v3.8h, v19.8h, v9.8h                                          ; 0x00000170, line  142
        smlal2  v23.4s, v12.8h, v15.8h                                        ; 0x00000174, line  143
        smlal   v26.4s, v6.4h, v20.4h                                         ; 0x00000178, line  144
        uzp1    v5.8h, v18.8h, v8.8h                                          ; 0x0000017C, line  145
        uzp2    v21.8h, v14.8h, v10.8h                                        ; 0x00000180, line  146
        smlal   v26.4s, v16.4h, v30.4h                                        ; 0x00000184, line  147
        str     q25, [x0], #0x20                                              ; 0x00000188, line  148
        mul     v29.8h, v5.8h, v2.8h                                          ; 0x0000018C, line  149
        uzp1    v24.8h, v14.8h, v10.8h                                        ; 0x00000190, line  150
        stur    q3, [x0, #-0x10]                                              ; 0x00000194, line  151
        smlal   v26.4s, v12.4h, v15.4h                                        ; 0x00000198, line  152
        ld1     { v15.8h }, [x6], #16                                         ; 0x0000019C, line  153
        ldr     q28, [x1, #0x10]                                              ; 0x000001A0, line  154
        ldr     q11, [x1], #0x20                                              ; 0x000001A4, line  155
        ldr     q13, [x5], #0x20                                              ; 0x000001A8, line  156
        ldur    q27, [x4, #-0x10]                                             ; 0x000001AC, line  157
        smlal2  v8.4s, v29.8h, v0.8h                                          ; 0x000001B0, line  158
        ldur    q22, [x5, #-0x10]                                             ; 0x000001B4, line  159
        smlal   v18.4s, v29.4h, v0.4h                                         ; 0x000001B8, line  160
        uzp1    v4.8h, v26.8h, v23.8h                                         ; 0x000001BC, line  161
        uzp1    v1.8h, v11.8h, v28.8h                                         ; 0x000001C0, line  162
        uzp2    v6.8h, v11.8h, v28.8h                                         ; 0x000001C4, line  163
        uzp1    v16.8h, v7.8h, v27.8h                                         ; 0x000001C8, line  164
        mul     v31.8h, v4.8h, v2.8h                                          ; 0x000001CC, line  165
        uzp2    v17.8h, v13.8h, v22.8h                                        ; 0x000001D0, line  166
        ld1     { v20.8h }, [x3], #16                                         ; 0x000001D4, line  167
        uzp2    v9.8h, v18.8h, v8.8h                                          ; 0x000001D8, line  168
        smull2  v8.4s, v1.8h, v21.8h                                          ; 0x000001DC, line  169
        uzp1    v30.8h, v13.8h, v22.8h                                        ; 0x000001E0, line  170
        smlal2  v8.4s, v6.8h, v24.8h                                          ; 0x000001E4, line  171
        smlal2  v8.4s, v16.8h, v17.8h                                         ; 0x000001E8, line  172
        uzp2    v12.8h, v7.8h, v27.8h                                         ; 0x000001EC, line  173
        smlal   v26.4s, v31.4h, v0.4h                                         ; 0x000001F0, line  174
        smlal2  v23.4s, v31.8h, v0.8h                                         ; 0x000001F4, line  175
        smull   v18.4s, v1.4h, v21.4h                                         ; 0x000001F8, line  176
        smlal   v18.4s, v6.4h, v24.4h                                         ; 0x000001FC, line  177
        smlal2  v8.4s, v12.8h, v30.8h                                         ; 0x00000200, line  178
        uzp2    v19.8h, v26.8h, v23.8h                                        ; 0x00000204, line  179
        smull2  v23.4s, v1.8h, v24.8h                                         ; 0x00000208, line  180
        smull   v26.4s, v1.4h, v24.4h                                         ; 0x0000020C, line  181
        subs    x13, x13, #0x1                                                ; 0x00000210, line  182
        cbnz    x13, Lmlk_polyvec_basemul_acc_montgomery_cached_k2_loop_start ; 0x00000214, line  183
        smlal   v26.4s, v6.4h, v20.4h                                         ; 0x00000218, line  184
        smlal2  v23.4s, v6.8h, v20.8h                                         ; 0x0000021C, line  185
        smlal   v26.4s, v16.4h, v30.4h                                        ; 0x00000220, line  186
        smlal2  v23.4s, v16.8h, v30.8h                                        ; 0x00000224, line  187
        smlal   v26.4s, v12.4h, v15.4h                                        ; 0x00000228, line  188
        smlal2  v23.4s, v12.8h, v15.8h                                        ; 0x0000022C, line  189
        smlal   v18.4s, v16.4h, v17.4h                                        ; 0x00000230, line  190
        smlal   v18.4s, v12.4h, v30.4h                                        ; 0x00000234, line  191
        zip1    v12.8h, v19.8h, v9.8h                                         ; 0x00000238, line  192
        str     q12, [x0], #0x20                                              ; 0x0000023C, line  193
        uzp1    v12.8h, v26.8h, v23.8h                                        ; 0x00000240, line  194
        mul     v6.8h, v12.8h, v2.8h                                          ; 0x00000244, line  195
        uzp1    v12.8h, v18.8h, v8.8h                                         ; 0x00000248, line  196
        mul     v12.8h, v12.8h, v2.8h                                         ; 0x0000024C, line  197
        smlal   v26.4s, v6.4h, v0.4h                                          ; 0x00000250, line  198
        smlal2  v23.4s, v6.8h, v0.8h                                          ; 0x00000254, line  199
        smlal2  v8.4s, v12.8h, v0.8h                                          ; 0x00000258, line  200
        smlal   v18.4s, v12.4h, v0.4h                                         ; 0x0000025C, line  201
        zip2    v12.8h, v19.8h, v9.8h                                         ; 0x00000260, line  202
        uzp2    v6.8h, v26.8h, v23.8h                                         ; 0x00000264, line  203
        stur    q12, [x0, #-0x10]                                             ; 0x00000268, line  204
        uzp2    v12.8h, v18.8h, v8.8h                                         ; 0x0000026C, line  205
        zip2    v1.8h, v6.8h, v12.8h                                          ; 0x00000270, line  206
        zip1    v12.8h, v6.8h, v12.8h                                         ; 0x00000274, line  207
        str     q1, [x0, #0x10]                                               ; 0x00000278, line  208
        str     q12, [x0], #0x20                                              ; 0x0000027C, line  209
        ldp     d8, d9, [sp]                                                  ; 0x00000280, line  210
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp     d10, d11, [sp, #0x10]                                         ; 0x00000284, line  213
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp     d12, d13, [sp, #0x20]                                         ; 0x00000288, line  216
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp     d14, d15, [sp, #0x30]                                         ; 0x0000028C, line  219
        ; .cfi_restore d14
        ; .cfi_restore d15
        add     sp, sp, #0x40                                                 ; 0x00000290, line  222
        ; .cfi_adjust_cfa_offset -0x40
        ret                                                                   ; 0x00000294, line  224
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000298 byte(s)

        AREA    |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD     0x182000A6                                                    ; header dword
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
