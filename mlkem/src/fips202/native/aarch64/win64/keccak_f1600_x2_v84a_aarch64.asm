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
; Name: keccak_f1600_x2_v84a_aarch64_asm
; Description: AArch64 ARMv8.4-A implementation of Keccak-f[1600] permutation for two sequential states
; Signature: void mld_keccak_f1600_x2_v84a_aarch64_asm(uint64_t state[50], const uint64_t rc[24])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON, SHA3]
;   x0:
;     type: buffer
;     size_bytes: 400
;     permissions: read/write
;     c_parameter: uint64_t state[50]
;     description: Two sequential Keccak states (state0[25], state1[25])
;   x1:
;     type: buffer
;     size_bytes: 192
;     permissions: read-only
;     c_parameter: uint64_t const *rc
;     description: Round constants (24 x uint64_t)
; Stack:
;   bytes: 64
;   description: register preservation
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "keccak_f1600_x2_v84a_aarch64_asm"
        ENDIF

        AREA    |.drectve|, DRECTVE

        EXPORT  $FUNC_NAME

        AREA    |.text|, CODE, ARM64, READONLY, ALIGN=4

        ALIGN   16

$FUNC_NAME PROC

        ; .cfi_startproc
        sub     sp, sp, #0x40                           ; 0x00000000, line   27
        ; .cfi_adjust_cfa_offset 0x40
        stp     d8, d9, [sp]                            ; 0x00000004, line   29
        ; .cfi_rel_offset d8, 0x0
        ; .cfi_rel_offset d9, 0x8
        stp     d10, d11, [sp, #0x10]                   ; 0x00000008, line   32
        ; .cfi_rel_offset d10, 0x10
        ; .cfi_rel_offset d11, 0x18
        stp     d12, d13, [sp, #0x20]                   ; 0x0000000C, line   35
        ; .cfi_rel_offset d12, 0x20
        ; .cfi_rel_offset d13, 0x28
        stp     d14, d15, [sp, #0x30]                   ; 0x00000010, line   38
        ; .cfi_rel_offset d14, 0x30
        ; .cfi_rel_offset d15, 0x38
        add     x2, x0, #0xc8                           ; 0x00000014, line   41
        ldp     q25, q26, [x0], #0x20                   ; 0x00000018, line   42
        ld1     { v27.2d, v28.2d }, [x2], #32           ; 0x0000001C, line   43
        trn1    v0.2d, v25.2d, v27.2d                   ; 0x00000020, line   44
        trn2    v1.2d, v25.2d, v27.2d                   ; 0x00000024, line   45
        trn1    v2.2d, v26.2d, v28.2d                   ; 0x00000028, line   46
        trn2    v3.2d, v26.2d, v28.2d                   ; 0x0000002C, line   47
        ldp     q25, q26, [x0], #0x20                   ; 0x00000030, line   48
        ld1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000034, line   49
        trn1    v4.2d, v25.2d, v27.2d                   ; 0x00000038, line   50
        trn2    v5.2d, v25.2d, v27.2d                   ; 0x0000003C, line   51
        trn1    v6.2d, v26.2d, v28.2d                   ; 0x00000040, line   52
        trn2    v7.2d, v26.2d, v28.2d                   ; 0x00000044, line   53
        ldp     q25, q26, [x0], #0x20                   ; 0x00000048, line   54
        ld1     { v27.2d, v28.2d }, [x2], #32           ; 0x0000004C, line   55
        trn1    v8.2d, v25.2d, v27.2d                   ; 0x00000050, line   56
        trn2    v9.2d, v25.2d, v27.2d                   ; 0x00000054, line   57
        trn1    v10.2d, v26.2d, v28.2d                  ; 0x00000058, line   58
        trn2    v11.2d, v26.2d, v28.2d                  ; 0x0000005C, line   59
        ldp     q25, q26, [x0], #0x20                   ; 0x00000060, line   60
        ld1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000064, line   61
        trn1    v12.2d, v25.2d, v27.2d                  ; 0x00000068, line   62
        trn2    v13.2d, v25.2d, v27.2d                  ; 0x0000006C, line   63
        trn1    v14.2d, v26.2d, v28.2d                  ; 0x00000070, line   64
        trn2    v15.2d, v26.2d, v28.2d                  ; 0x00000074, line   65
        ldp     q25, q26, [x0], #0x20                   ; 0x00000078, line   66
        ld1     { v27.2d, v28.2d }, [x2], #32           ; 0x0000007C, line   67
        trn1    v16.2d, v25.2d, v27.2d                  ; 0x00000080, line   68
        trn2    v17.2d, v25.2d, v27.2d                  ; 0x00000084, line   69
        trn1    v18.2d, v26.2d, v28.2d                  ; 0x00000088, line   70
        trn2    v19.2d, v26.2d, v28.2d                  ; 0x0000008C, line   71
        ldp     q25, q26, [x0], #0x20                   ; 0x00000090, line   72
        ld1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000094, line   73
        trn1    v20.2d, v25.2d, v27.2d                  ; 0x00000098, line   74
        trn2    v21.2d, v25.2d, v27.2d                  ; 0x0000009C, line   75
        trn1    v22.2d, v26.2d, v28.2d                  ; 0x000000A0, line   76
        trn2    v23.2d, v26.2d, v28.2d                  ; 0x000000A4, line   77
        ldr     d25, [x0]                               ; 0x000000A8, line   78
        ldr     d27, [x2]                               ; 0x000000AC, line   79
        trn1    v24.2d, v25.2d, v27.2d                  ; 0x000000B0, line   80
        mov     x2, #0x18                               ; 0x000000B4, line   81
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x2_v84a_loop

        eor3    v30.16b, v0.16b, v5.16b, v10.16b        ; 0x000000C0, line   84
        eor3    v29.16b, v1.16b, v6.16b, v11.16b        ; 0x000000C4, line   85
        eor3    v28.16b, v2.16b, v7.16b, v12.16b        ; 0x000000C8, line   86
        eor3    v27.16b, v3.16b, v8.16b, v13.16b        ; 0x000000CC, line   87
        eor3    v26.16b, v4.16b, v9.16b, v14.16b        ; 0x000000D0, line   88
        eor3    v30.16b, v30.16b, v15.16b, v20.16b      ; 0x000000D4, line   89
        eor3    v29.16b, v29.16b, v16.16b, v21.16b      ; 0x000000D8, line   90
        eor3    v28.16b, v28.16b, v17.16b, v22.16b      ; 0x000000DC, line   91
        eor3    v27.16b, v27.16b, v18.16b, v23.16b      ; 0x000000E0, line   92
        eor3    v26.16b, v26.16b, v19.16b, v24.16b      ; 0x000000E4, line   93
        rax1    v25.2d, v30.2d, v28.2d                  ; 0x000000E8, line   94
        rax1    v28.2d, v28.2d, v26.2d                  ; 0x000000EC, line   95
        rax1    v26.2d, v26.2d, v29.2d                  ; 0x000000F0, line   96
        rax1    v29.2d, v29.2d, v27.2d                  ; 0x000000F4, line   97
        rax1    v27.2d, v27.2d, v30.2d                  ; 0x000000F8, line   98
        eor     v30.16b, v0.16b, v26.16b                ; 0x000000FC, line   99
        xar     v0.2d, v2.2d, v29.2d, #0x2              ; 0x00000100, line  100
        xar     v2.2d, v12.2d, v29.2d, #0x15            ; 0x00000104, line  101
        xar     v12.2d, v13.2d, v28.2d, #0x27           ; 0x00000108, line  102
        xar     v13.2d, v19.2d, v27.2d, #0x38           ; 0x0000010C, line  103
        xar     v19.2d, v23.2d, v28.2d, #0x8            ; 0x00000110, line  104
        xar     v23.2d, v15.2d, v26.2d, #0x17           ; 0x00000114, line  105
        xar     v15.2d, v1.2d, v25.2d, #0x3f            ; 0x00000118, line  106
        xar     v1.2d, v8.2d, v28.2d, #0x9              ; 0x0000011C, line  107
        xar     v8.2d, v16.2d, v25.2d, #0x13            ; 0x00000120, line  108
        xar     v16.2d, v7.2d, v29.2d, #0x3a            ; 0x00000124, line  109
        xar     v7.2d, v10.2d, v26.2d, #0x3d            ; 0x00000128, line  110
        xar     v10.2d, v3.2d, v28.2d, #0x24            ; 0x0000012C, line  111
        xar     v3.2d, v18.2d, v28.2d, #0x2b            ; 0x00000130, line  112
        xar     v18.2d, v17.2d, v29.2d, #0x31           ; 0x00000134, line  113
        xar     v17.2d, v11.2d, v25.2d, #0x36           ; 0x00000138, line  114
        xar     v11.2d, v9.2d, v27.2d, #0x2c            ; 0x0000013C, line  115
        xar     v9.2d, v22.2d, v29.2d, #0x3             ; 0x00000140, line  116
        xar     v22.2d, v14.2d, v27.2d, #0x19           ; 0x00000144, line  117
        xar     v14.2d, v20.2d, v26.2d, #0x2e           ; 0x00000148, line  118
        xar     v20.2d, v4.2d, v27.2d, #0x25            ; 0x0000014C, line  119
        xar     v4.2d, v24.2d, v27.2d, #0x32            ; 0x00000150, line  120
        xar     v24.2d, v21.2d, v25.2d, #0x3e           ; 0x00000154, line  121
        xar     v21.2d, v5.2d, v26.2d, #0x1c            ; 0x00000158, line  122
        xar     v27.2d, v6.2d, v25.2d, #0x14            ; 0x0000015C, line  123
        ld1r    { v31.2d }, [x1], #8                    ; 0x00000160, line  124
        bcax    v5.16b, v10.16b, v7.16b, v11.16b        ; 0x00000164, line  125
        bcax    v6.16b, v11.16b, v8.16b, v7.16b         ; 0x00000168, line  126
        bcax    v7.16b, v7.16b, v9.16b, v8.16b          ; 0x0000016C, line  127
        bcax    v8.16b, v8.16b, v10.16b, v9.16b         ; 0x00000170, line  128
        bcax    v9.16b, v9.16b, v11.16b, v10.16b        ; 0x00000174, line  129
        bcax    v10.16b, v15.16b, v12.16b, v16.16b      ; 0x00000178, line  130
        bcax    v11.16b, v16.16b, v13.16b, v12.16b      ; 0x0000017C, line  131
        bcax    v12.16b, v12.16b, v14.16b, v13.16b      ; 0x00000180, line  132
        bcax    v13.16b, v13.16b, v15.16b, v14.16b      ; 0x00000184, line  133
        bcax    v14.16b, v14.16b, v16.16b, v15.16b      ; 0x00000188, line  134
        bcax    v15.16b, v20.16b, v17.16b, v21.16b      ; 0x0000018C, line  135
        bcax    v16.16b, v21.16b, v18.16b, v17.16b      ; 0x00000190, line  136
        bcax    v17.16b, v17.16b, v19.16b, v18.16b      ; 0x00000194, line  137
        bcax    v18.16b, v18.16b, v20.16b, v19.16b      ; 0x00000198, line  138
        bcax    v19.16b, v19.16b, v21.16b, v20.16b      ; 0x0000019C, line  139
        bcax    v20.16b, v0.16b, v22.16b, v1.16b        ; 0x000001A0, line  140
        bcax    v21.16b, v1.16b, v23.16b, v22.16b       ; 0x000001A4, line  141
        bcax    v22.16b, v22.16b, v24.16b, v23.16b      ; 0x000001A8, line  142
        bcax    v23.16b, v23.16b, v0.16b, v24.16b       ; 0x000001AC, line  143
        bcax    v24.16b, v24.16b, v1.16b, v0.16b        ; 0x000001B0, line  144
        bcax    v0.16b, v30.16b, v2.16b, v27.16b        ; 0x000001B4, line  145
        bcax    v1.16b, v27.16b, v3.16b, v2.16b         ; 0x000001B8, line  146
        bcax    v2.16b, v2.16b, v4.16b, v3.16b          ; 0x000001BC, line  147
        bcax    v3.16b, v3.16b, v30.16b, v4.16b         ; 0x000001C0, line  148
        bcax    v4.16b, v4.16b, v27.16b, v30.16b        ; 0x000001C4, line  149
        eor     v0.16b, v0.16b, v31.16b                 ; 0x000001C8, line  150
        sub     x2, x2, #0x1                            ; 0x000001CC, line  151
        cbnz    x2, Lmld_keccak_f1600_x2_v84a_loop      ; 0x000001D0, line  152
        sub     x0, x0, #0xc0                           ; 0x000001D4, line  153
        add     x2, x0, #0xc8                           ; 0x000001D8, line  154
        trn1    v25.2d, v0.2d, v1.2d                    ; 0x000001DC, line  155
        trn1    v26.2d, v2.2d, v3.2d                    ; 0x000001E0, line  156
        stp     q25, q26, [x0], #0x20                   ; 0x000001E4, line  157
        trn2    v27.2d, v0.2d, v1.2d                    ; 0x000001E8, line  158
        trn2    v28.2d, v2.2d, v3.2d                    ; 0x000001EC, line  159
        st1     { v27.2d, v28.2d }, [x2], #32           ; 0x000001F0, line  160
        trn1    v25.2d, v4.2d, v5.2d                    ; 0x000001F4, line  161
        trn1    v26.2d, v6.2d, v7.2d                    ; 0x000001F8, line  162
        stp     q25, q26, [x0], #0x20                   ; 0x000001FC, line  163
        trn2    v27.2d, v4.2d, v5.2d                    ; 0x00000200, line  164
        trn2    v28.2d, v6.2d, v7.2d                    ; 0x00000204, line  165
        st1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000208, line  166
        trn1    v25.2d, v8.2d, v9.2d                    ; 0x0000020C, line  167
        trn1    v26.2d, v10.2d, v11.2d                  ; 0x00000210, line  168
        stp     q25, q26, [x0], #0x20                   ; 0x00000214, line  169
        trn2    v27.2d, v8.2d, v9.2d                    ; 0x00000218, line  170
        trn2    v28.2d, v10.2d, v11.2d                  ; 0x0000021C, line  171
        st1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000220, line  172
        trn1    v25.2d, v12.2d, v13.2d                  ; 0x00000224, line  173
        trn1    v26.2d, v14.2d, v15.2d                  ; 0x00000228, line  174
        stp     q25, q26, [x0], #0x20                   ; 0x0000022C, line  175
        trn2    v27.2d, v12.2d, v13.2d                  ; 0x00000230, line  176
        trn2    v28.2d, v14.2d, v15.2d                  ; 0x00000234, line  177
        st1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000238, line  178
        trn1    v25.2d, v16.2d, v17.2d                  ; 0x0000023C, line  179
        trn1    v26.2d, v18.2d, v19.2d                  ; 0x00000240, line  180
        stp     q25, q26, [x0], #0x20                   ; 0x00000244, line  181
        trn2    v27.2d, v16.2d, v17.2d                  ; 0x00000248, line  182
        trn2    v28.2d, v18.2d, v19.2d                  ; 0x0000024C, line  183
        st1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000250, line  184
        trn1    v25.2d, v20.2d, v21.2d                  ; 0x00000254, line  185
        trn1    v26.2d, v22.2d, v23.2d                  ; 0x00000258, line  186
        stp     q25, q26, [x0], #0x20                   ; 0x0000025C, line  187
        trn2    v27.2d, v20.2d, v21.2d                  ; 0x00000260, line  188
        trn2    v28.2d, v22.2d, v23.2d                  ; 0x00000264, line  189
        st1     { v27.2d, v28.2d }, [x2], #32           ; 0x00000268, line  190
        str     d24, [x0]                               ; 0x0000026C, line  191
        trn2    v25.2d, v24.2d, v24.2d                  ; 0x00000270, line  192
        str     d25, [x2]                               ; 0x00000274, line  193
        ldp     d8, d9, [sp]                            ; 0x00000278, line  194
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp     d10, d11, [sp, #0x10]                   ; 0x0000027C, line  197
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp     d12, d13, [sp, #0x20]                   ; 0x00000280, line  200
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp     d14, d15, [sp, #0x30]                   ; 0x00000284, line  203
        ; .cfi_restore d14
        ; .cfi_restore d15
        add     sp, sp, #0x40                           ; 0x00000288, line  206
        ; .cfi_adjust_cfa_offset -0x40
        ret                                             ; 0x0000028C, line  208
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x00000290 byte(s)

        AREA    |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD     0x182000A4                              ; header dword
        DCB     0xD9, 0x86                              ; unwind code 'save_fregp', registers d14,d15 at stack offset 0x0030
        DCB     0xD9, 0x04                              ; unwind code 'save_fregp', registers d12,d13 at stack offset 0x0020
        DCB     0xD8, 0x82                              ; unwind code 'save_fregp', registers d10,d11 at stack offset 0x0010
        DCB     0xD8, 0x00                              ; unwind code 'save_fregp', registers d8,d9 at stack offset 0x0000
        DCB     0x04                                    ; unwind code 'alloc_s', stack space 0x0040
        DCB     0xE4                                    ; unwind code 'end'
        DCB     0x00, 0x00                              ; unwind code padding

        AREA    |.pdata|, DATA, READONLY, ALIGN=4

        DCD     $FUNC_NAME                              ; function start RVA
        DCD     XDATA_$FUNC_NAME                        ; pointer in XDATA section

        END
