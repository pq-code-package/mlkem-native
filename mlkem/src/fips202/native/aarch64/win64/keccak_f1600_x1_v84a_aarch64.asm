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
; Name: keccak_f1600_x1_v84a_aarch64_asm
; Description: AArch64 ARMv8.4-A implementation of Keccak-f[1600] permutation for single state
; Signature: void mld_keccak_f1600_x1_v84a_aarch64_asm(uint64_t state[25], const uint64_t rc[24])
; ABI:
;   Architecture: aarch64
;   CallingConvention: AAPCS64
;   Features: [NEON, SHA3]
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
;   bytes: 64
;   description: register preservation
;

        IF :LNOT: :DEF:FUNC_NAME
        GBLS      FUNC_NAME
FUNC_NAME SETS    "keccak_f1600_x1_v84a_aarch64_asm"
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
        ldp     d0, d1, [x0]                            ; 0x00000014, line   41
        ldp     d2, d3, [x0, #0x10]                     ; 0x00000018, line   42
        ldp     d4, d5, [x0, #0x20]                     ; 0x0000001C, line   43
        ldp     d6, d7, [x0, #0x30]                     ; 0x00000020, line   44
        ldp     d8, d9, [x0, #0x40]                     ; 0x00000024, line   45
        ldp     d10, d11, [x0, #0x50]                   ; 0x00000028, line   46
        ldp     d12, d13, [x0, #0x60]                   ; 0x0000002C, line   47
        ldp     d14, d15, [x0, #0x70]                   ; 0x00000030, line   48
        ldp     d16, d17, [x0, #0x80]                   ; 0x00000034, line   49
        ldp     d18, d19, [x0, #0x90]                   ; 0x00000038, line   50
        ldp     d20, d21, [x0, #0xa0]                   ; 0x0000003C, line   51
        ldp     d22, d23, [x0, #0xb0]                   ; 0x00000040, line   52
        ldr     d24, [x0, #0xc0]                        ; 0x00000044, line   53
        mov     x2, #0x18                               ; 0x00000048, line   54
        HINT    #0x0                                    ; ALIGN 16; bug in armasm64.exe requires 'HINT' mnemonics

Lmld_keccak_f1600_x1_v84a_loop

        eor3    v30.16b, v0.16b, v5.16b, v10.16b        ; 0x00000050, line   57
        eor3    v29.16b, v1.16b, v6.16b, v11.16b        ; 0x00000054, line   58
        eor3    v28.16b, v2.16b, v7.16b, v12.16b        ; 0x00000058, line   59
        eor3    v27.16b, v3.16b, v8.16b, v13.16b        ; 0x0000005C, line   60
        eor3    v26.16b, v4.16b, v9.16b, v14.16b        ; 0x00000060, line   61
        eor3    v30.16b, v30.16b, v15.16b, v20.16b      ; 0x00000064, line   62
        eor3    v29.16b, v29.16b, v16.16b, v21.16b      ; 0x00000068, line   63
        eor3    v28.16b, v28.16b, v17.16b, v22.16b      ; 0x0000006C, line   64
        eor3    v27.16b, v27.16b, v18.16b, v23.16b      ; 0x00000070, line   65
        eor3    v26.16b, v26.16b, v19.16b, v24.16b      ; 0x00000074, line   66
        rax1    v25.2d, v30.2d, v28.2d                  ; 0x00000078, line   67
        rax1    v28.2d, v28.2d, v26.2d                  ; 0x0000007C, line   68
        rax1    v26.2d, v26.2d, v29.2d                  ; 0x00000080, line   69
        rax1    v29.2d, v29.2d, v27.2d                  ; 0x00000084, line   70
        rax1    v27.2d, v27.2d, v30.2d                  ; 0x00000088, line   71
        eor     v30.16b, v0.16b, v26.16b                ; 0x0000008C, line   72
        xar     v0.2d, v2.2d, v29.2d, #0x2              ; 0x00000090, line   73
        xar     v2.2d, v12.2d, v29.2d, #0x15            ; 0x00000094, line   74
        xar     v12.2d, v13.2d, v28.2d, #0x27           ; 0x00000098, line   75
        xar     v13.2d, v19.2d, v27.2d, #0x38           ; 0x0000009C, line   76
        xar     v19.2d, v23.2d, v28.2d, #0x8            ; 0x000000A0, line   77
        xar     v23.2d, v15.2d, v26.2d, #0x17           ; 0x000000A4, line   78
        xar     v15.2d, v1.2d, v25.2d, #0x3f            ; 0x000000A8, line   79
        xar     v1.2d, v8.2d, v28.2d, #0x9              ; 0x000000AC, line   80
        xar     v8.2d, v16.2d, v25.2d, #0x13            ; 0x000000B0, line   81
        xar     v16.2d, v7.2d, v29.2d, #0x3a            ; 0x000000B4, line   82
        xar     v7.2d, v10.2d, v26.2d, #0x3d            ; 0x000000B8, line   83
        xar     v10.2d, v3.2d, v28.2d, #0x24            ; 0x000000BC, line   84
        xar     v3.2d, v18.2d, v28.2d, #0x2b            ; 0x000000C0, line   85
        xar     v18.2d, v17.2d, v29.2d, #0x31           ; 0x000000C4, line   86
        xar     v17.2d, v11.2d, v25.2d, #0x36           ; 0x000000C8, line   87
        xar     v11.2d, v9.2d, v27.2d, #0x2c            ; 0x000000CC, line   88
        xar     v9.2d, v22.2d, v29.2d, #0x3             ; 0x000000D0, line   89
        xar     v22.2d, v14.2d, v27.2d, #0x19           ; 0x000000D4, line   90
        xar     v14.2d, v20.2d, v26.2d, #0x2e           ; 0x000000D8, line   91
        xar     v20.2d, v4.2d, v27.2d, #0x25            ; 0x000000DC, line   92
        xar     v4.2d, v24.2d, v27.2d, #0x32            ; 0x000000E0, line   93
        xar     v24.2d, v21.2d, v25.2d, #0x3e           ; 0x000000E4, line   94
        xar     v21.2d, v5.2d, v26.2d, #0x1c            ; 0x000000E8, line   95
        xar     v27.2d, v6.2d, v25.2d, #0x14            ; 0x000000EC, line   96
        ld1r    { v31.2d }, [x1], #8                    ; 0x000000F0, line   97
        bcax    v5.16b, v10.16b, v7.16b, v11.16b        ; 0x000000F4, line   98
        bcax    v6.16b, v11.16b, v8.16b, v7.16b         ; 0x000000F8, line   99
        bcax    v7.16b, v7.16b, v9.16b, v8.16b          ; 0x000000FC, line  100
        bcax    v8.16b, v8.16b, v10.16b, v9.16b         ; 0x00000100, line  101
        bcax    v9.16b, v9.16b, v11.16b, v10.16b        ; 0x00000104, line  102
        bcax    v10.16b, v15.16b, v12.16b, v16.16b      ; 0x00000108, line  103
        bcax    v11.16b, v16.16b, v13.16b, v12.16b      ; 0x0000010C, line  104
        bcax    v12.16b, v12.16b, v14.16b, v13.16b      ; 0x00000110, line  105
        bcax    v13.16b, v13.16b, v15.16b, v14.16b      ; 0x00000114, line  106
        bcax    v14.16b, v14.16b, v16.16b, v15.16b      ; 0x00000118, line  107
        bcax    v15.16b, v20.16b, v17.16b, v21.16b      ; 0x0000011C, line  108
        bcax    v16.16b, v21.16b, v18.16b, v17.16b      ; 0x00000120, line  109
        bcax    v17.16b, v17.16b, v19.16b, v18.16b      ; 0x00000124, line  110
        bcax    v18.16b, v18.16b, v20.16b, v19.16b      ; 0x00000128, line  111
        bcax    v19.16b, v19.16b, v21.16b, v20.16b      ; 0x0000012C, line  112
        bcax    v20.16b, v0.16b, v22.16b, v1.16b        ; 0x00000130, line  113
        bcax    v21.16b, v1.16b, v23.16b, v22.16b       ; 0x00000134, line  114
        bcax    v22.16b, v22.16b, v24.16b, v23.16b      ; 0x00000138, line  115
        bcax    v23.16b, v23.16b, v0.16b, v24.16b       ; 0x0000013C, line  116
        bcax    v24.16b, v24.16b, v1.16b, v0.16b        ; 0x00000140, line  117
        bcax    v0.16b, v30.16b, v2.16b, v27.16b        ; 0x00000144, line  118
        bcax    v1.16b, v27.16b, v3.16b, v2.16b         ; 0x00000148, line  119
        bcax    v2.16b, v2.16b, v4.16b, v3.16b          ; 0x0000014C, line  120
        bcax    v3.16b, v3.16b, v30.16b, v4.16b         ; 0x00000150, line  121
        bcax    v4.16b, v4.16b, v27.16b, v30.16b        ; 0x00000154, line  122
        eor     v0.16b, v0.16b, v31.16b                 ; 0x00000158, line  123
        sub     x2, x2, #0x1                            ; 0x0000015C, line  124
        cbnz    x2, Lmld_keccak_f1600_x1_v84a_loop      ; 0x00000160, line  125
        stp     d0, d1, [x0]                            ; 0x00000164, line  126
        stp     d2, d3, [x0, #0x10]                     ; 0x00000168, line  127
        stp     d4, d5, [x0, #0x20]                     ; 0x0000016C, line  128
        stp     d6, d7, [x0, #0x30]                     ; 0x00000170, line  129
        stp     d8, d9, [x0, #0x40]                     ; 0x00000174, line  130
        stp     d10, d11, [x0, #0x50]                   ; 0x00000178, line  131
        stp     d12, d13, [x0, #0x60]                   ; 0x0000017C, line  132
        stp     d14, d15, [x0, #0x70]                   ; 0x00000180, line  133
        stp     d16, d17, [x0, #0x80]                   ; 0x00000184, line  134
        stp     d18, d19, [x0, #0x90]                   ; 0x00000188, line  135
        stp     d20, d21, [x0, #0xa0]                   ; 0x0000018C, line  136
        stp     d22, d23, [x0, #0xb0]                   ; 0x00000190, line  137
        str     d24, [x0, #0xc0]                        ; 0x00000194, line  138
        ldp     d8, d9, [sp]                            ; 0x00000198, line  139
        ; .cfi_restore d8
        ; .cfi_restore d9
        ldp     d10, d11, [sp, #0x10]                   ; 0x0000019C, line  142
        ; .cfi_restore d10
        ; .cfi_restore d11
        ldp     d12, d13, [sp, #0x20]                   ; 0x000001A0, line  145
        ; .cfi_restore d12
        ; .cfi_restore d13
        ldp     d14, d15, [sp, #0x30]                   ; 0x000001A4, line  148
        ; .cfi_restore d14
        ; .cfi_restore d15
        add     sp, sp, #0x40                           ; 0x000001A8, line  151
        ; .cfi_adjust_cfa_offset -0x40
        ret                                             ; 0x000001AC, line  153
        ; .cfi_endproc

        ENDP

        ; sizeof function: 0x000001B0 byte(s)

        AREA    |.xdata|, DATA, READONLY, ALIGN=4

XDATA_$FUNC_NAME

        DCD     0x1820006C                              ; header dword
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
