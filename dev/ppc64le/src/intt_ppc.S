/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#
# Copyright 2025- IBM Corp.
#
#===================================================================================
# Written by Danny Tsen <dtsen@us.ibm.com>
#

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "consts.h"

.machine "any"
.text

# Barrett reduce constatnts
#define V20159  0
#define V_25    1
#define V_26    2
#define V_MKQ   3

# Montgomery reduce constatnts
#define V_QINV  2
#define V_NMKQ  5
#define V_Z0    7
#define V_Z1    8
#define V_Z2    9
#define V_Z3    10
#define V_ZETA  10
#define V1441   10

.macro SAVE_REGS
	stdu	1, -352(1)
	mflr	0
	std	14, 56(1)
	std	15, 64(1)
	std	16, 72(1)
	std	17, 80(1)
	std	18, 88(1)
	std	19, 96(1)
	std	20, 104(1)
	std	21, 112(1)
	li	10, 128
	li	11, 144
	li	12, 160
	li	14, 176
	li	15, 192
	li	16, 208
	stxvx	32+20, 10, 1
	stxvx	32+21, 11, 1
	stxvx	32+22, 12, 1
	stxvx	32+23, 14, 1
	stxvx	32+24, 15, 1
	stxvx	32+25, 16, 1
	li	10, 224
	li	11, 240
	li	12, 256
	li	14, 272
	li	15, 288
	li	16, 304
	stxvx	32+26, 10, 1
	stxvx	32+27, 11, 1
	stxvx	32+28, 12, 1
	stxvx	32+29, 14, 1
	stxvx	32+30, 15, 1
	stxvx	32+31, 16, 1
.endm

.macro RESTORE_REGS
	li	10, 128
	li	11, 144
	li	12, 160
	li	14, 176
	li	15, 192
	li	16, 208
	lxvx	32+20, 10, 1
	lxvx	32+21, 11, 1
	lxvx	32+22, 12, 1
	lxvx	32+23, 14, 1
	lxvx	32+24, 15, 1
	lxvx	32+25, 16, 1
	li	10, 224
	li	11, 240
	li	12, 256
	li	14, 272
	li	15, 288
	li	16, 304
	lxvx	32+26, 10, 1
	lxvx	32+27, 11, 1
	lxvx	32+28, 12, 1
	lxvx	32+29, 14, 1
	lxvx	32+30, 15, 1
	lxvx	32+31, 16, 1
	ld	14, 56(1)
	ld	15, 64(1)
	ld	16, 72(1)
	ld	17, 80(1)
	ld	18, 88(1)
	ld	19, 96(1)
	ld	20, 104(1)
	ld	21, 112(1)

	mtlr	0
	addi    1, 1, 352
.endm

.macro Compute_4Coeffs
	vsubuhm 25, 8, 21		# r[j+len] - t
	vsubuhm 26, 12, 22		# r[j+len] - t
	vsubuhm 30, 16, 23		# r[j+len] - t
	vsubuhm 31, 20, 24		# r[j+len] - t
	vadduhm 8, 8, 21		# r[j+len] + t
	vadduhm 12, 12, 22		# r[j+len] + t
	vadduhm 16, 16, 23		# r[j+len] + t
	vadduhm 20, 20, 24		# r[j+len] + t
.endm

.macro Load_4Coeffs start next step
	mr	9, \start	# j
	add	10, 7, 9	# J + len*2
	addi	16, 9, \next
	addi	17, 10, \step
	addi	18, 16, \next
	addi	19, 17, \step
	addi	20, 18, \next
	addi	21, 19, \step
	lxvd2x	32+8, 3, 10	# r[j+len]
	lxvd2x	32+12, 3, 17	# r[j+len]
	lxvd2x	32+16, 3, 19	# r[j+len]
	lxvd2x	32+20, 3, 21	# r[j+len]

	lxvd2x	32+21, 3, 9
	lxvd2x	32+22, 3, 16
	lxvd2x	32+23, 3, 18
	lxvd2x	32+24, 3, 20

	Compute_4Coeffs
.endm

#
# Load Coeffients and setup vectors
#    aj0, aj1, ajlen2, ajlen3, aj4, aj5, ajlen6, ajlen7
#    aj8, aj9, ajlen10, ajlen11, aj12, aj13, ajlen14, ajlen15
#
#  a[j]=      aj0, aj1, aj8, aj9, aj4, aj5, aj12, aj13
#  a[j+len]=  ajlen2, ajlen3, ajlen10, ajlen11, ajlen6, ajlen7, ajlen14, ajlen15
#
.macro Load_L24Coeffs
        lxvd2x     32+25, 0, 5     # a[j], r[j+len]
        lxvd2x     32+26, 10, 5    # a[j], r[j+len]
        vmrgew 8, 25, 26
        vmrgow 21, 25, 26
        lxvd2x     32+25, 11, 5    # a[j], r[j+len]
        lxvd2x     32+26, 12, 5    # a[j], r[j+len]
        vmrgew 12, 25, 26
        vmrgow 22, 25, 26
        lxvd2x     32+25, 15, 5    # a[j], r[j+len]
        lxvd2x     32+26, 16, 5    # a[j], r[j+len]
        vmrgew 16, 25, 26
        vmrgow 23, 25, 26
        lxvd2x     32+25, 17, 5    # a[j], r[j+len]
        lxvd2x     32+26, 18, 5    # a[j], r[j+len]
        vmrgew 20, 25, 26
        vmrgow 24, 25, 26
.endm

#
# Permute
#  rj0, rj1, rj2, rj3, rjlen4, rjlen5, rjlen6, rjlen7
#  rj8, rj9, rj10, rj11, rjlen12, rjlen13, rjlen14, rjlen15
#
# to
#  rjlen4 - rjlen7, rjlen12 - rjlen15
#  rj0 - rj4, rj8 - rj11
#
.macro Load_L44Coeffs
        lxvd2x     10, 0, 5       # rj0, rj1, rj2, rj3,
                                  # rjlen4, rjlen5, rjlen6, rjlen7
        lxvd2x     11, 10, 5      # rj8, rj9, rj10, rj11
                                  # rjlen12, rjlen13, rjlen14, rjlen15
        xxpermdi 32+8, 11, 10, 3  # rjlen4 - rjlen7, rjlen12 - rjlen15
        xxpermdi 32+21, 11, 10, 0 # rj0 - rj4, rj8 - rj11
        lxvd2x     10, 11, 5
        lxvd2x     11, 12, 5
        xxpermdi 32+12, 11, 10, 3
        xxpermdi 32+22, 11, 10, 0
        lxvd2x     10, 15, 5
        lxvd2x     11, 16, 5
        xxpermdi 32+16, 11, 10, 3
        xxpermdi 32+23, 11, 10, 0
        lxvd2x     10, 17, 5
        lxvd2x     11, 18, 5
        xxpermdi 32+20, 11, 10, 3
        xxpermdi 32+24, 11, 10, 0
.endm

.macro BREDUCE_4X _v0 _v1 _v2 _v3
	vxor	7, 7, 7
	xxlor	32+3, 6, 6	# V_MKQ
	xxlor	32+1, 7, 7	# V_25
	xxlor	32+2, 8, 8	# V_26
	# Multify Odd/Even signed halfword;
	#   Results word bound by 2^32 in abs value.
	vmulosh	6, 8, V20159
	vmulesh	5, 8, V20159
	vmulosh	11, 12, V20159
	vmulesh	10, 12, V20159
	vmulosh	15, 16, V20159
	vmulesh	14, 16, V20159
	vmulosh	19, 20, V20159
	vmulesh	18, 20, V20159
	xxmrglw	32+4, 32+5, 32+6
	xxmrghw	32+5, 32+5, 32+6
	xxmrglw	32+9, 32+10, 32+11
	xxmrghw	32+10, 32+10, 32+11
	xxmrglw	32+13, 32+14, 32+15
	xxmrghw	32+14, 32+14, 32+15
	xxmrglw	32+17, 32+18, 32+19
	xxmrghw	32+18, 32+18, 32+19
	vadduwm	4, 4, V_25
	vadduwm	5, 5, V_25
	vadduwm	9, 9, V_25
	vadduwm	10, 10, V_25
	vadduwm	13, 13, V_25
	vadduwm	14, 14, V_25
	vadduwm	17, 17, V_25
	vadduwm	18, 18, V_25
	# Right shift and pack lower halfword,
	#   results bond to 2^16 in abs value
	vsraw	4, 4, V_26
	vsraw	5, 5, V_26
	vsraw	9, 9, V_26
	vsraw	10, 10, V_26
	vsraw	13, 13, V_26
	vsraw	14, 14, V_26
	vsraw	17, 17, V_26
	vsraw	18, 18, V_26
	vpkuwum	4, 5, 4
	vsubuhm	4, 7, 4
	vpkuwum	9, 10, 9
	vsubuhm	9, 7, 9
	vpkuwum	13, 14, 13
	vsubuhm	13, 7, 13
	vpkuwum	17, 18, 17
	vsubuhm	17, 7, 17
	# Modulo multify-Low unsigned halfword;
	#   results bond to 2^16 * q in abs value.
	vmladduhm \_v0, 4, V_MKQ, 8
	vmladduhm \_v1, 9, V_MKQ, 12
	vmladduhm \_v2, 13, V_MKQ, 16
	vmladduhm \_v3, 17, V_MKQ, 20
.endm

#-----------------------------------
# MREDUCE_4X(_vz0, _vz1, _vz2, _vz3, _vo0, _vo1, _vo2, _vo3)
#
.macro MREDUCE_4X _vz0 _vz1 _vz2 _vz3 _vo0 _vo1 _vo2 _vo3
	# Modular multification bond by 2^16 * q in abs value
	vmladduhm 15, 25, \_vz0, 3
	vmladduhm 20, 26, \_vz1, 3
	vmladduhm 27, 30, \_vz2, 3
	vmladduhm 28, 31, \_vz3, 3

	# Signed multiply-high-round; outputs are bound by 2^15 * q in abs value
	vmhraddshs 14, 25, \_vz0, 3
	vmhraddshs 19, 26, \_vz1, 3
	vmhraddshs 24, 30, \_vz2, 3
	vmhraddshs 29, 31, \_vz3, 3

	vmladduhm 15, 15, V_QINV, 3
	vmladduhm 20, 20, V_QINV, 3
	vmladduhm 25, 27, V_QINV, 3
	vmladduhm 30, 28, V_QINV, 3

	vmhraddshs 15, 15, V_NMKQ, 14
	vmhraddshs 20, 20, V_NMKQ, 19
	vmhraddshs 25, 25, V_NMKQ, 24
	vmhraddshs 30, 30, V_NMKQ, 29

	vsrah \_vo0, 15, 4		# >> 1
	vsrah \_vo1, 20, 4		# >> 1
	vsrah \_vo2, 25, 4		# >> 1
	vsrah \_vo3, 30, 4		# >> 1
.endm

.macro Set_mont_consts
	xxlor	32+5, 0, 0	# V_NMKQ
	xxlor	32+2, 2, 2	# V_QINV
	xxlor	32+3, 3, 3	# 0
	xxlor	32+4, 4, 4	# 1
.endm

.macro Load_next_4zetas
        li      8, 16
        li      11, 32
        li      12, 48
        lxvd2x    32+V_Z0, 0, 14
        lxvd2x    32+V_Z1, 8, 14
        lxvd2x    32+V_Z2, 11, 14
        lxvd2x    32+V_Z3, 12, 14
        addi    14, 14, 64
.endm

.macro Perm_4zetas
        xxpermdi 32+V_Z0, 32+V_Z0, 32+V_Z0, 2
        xxpermdi 32+V_Z1, 32+V_Z1, 32+V_Z1, 2
        xxpermdi 32+V_Z2, 32+V_Z2, 32+V_Z2, 2
        xxpermdi 32+V_Z3, 32+V_Z3, 32+V_Z3, 2
.endm

.macro Write_B4C _vs0 _vs1 _vs2 _vs3
	stxvd2x	\_vs0, 3, 9
	stxvd2x	\_vs1, 3, 16
	stxvd2x	\_vs2, 3, 18
	stxvd2x	\_vs3, 3, 20
.endm

.macro Write_M4C _vs0 _vs1 _vs2 _vs3
	stxvd2x	\_vs0, 3, 10
	stxvd2x	\_vs1, 3, 17
	stxvd2x	\_vs2, 3, 19
	stxvd2x	\_vs3, 3, 21
.endm

.macro Reload_4coeffs
	lxvd2x	32+25, 0, 3
	lxvd2x	32+26, 10, 3
	lxvd2x	32+30, 11, 3
	lxvd2x	32+31, 12, 3
	addi	3, 3, 64
.endm

.macro MWrite_8X _vs0 _vs1 _vs2 _vs3 _vs4 _vs5 _vs6 _vs7
	addi	3, 3, -128
	stxvd2x	\_vs0, 0, 3
	stxvd2x	\_vs1, 10, 3
	stxvd2x	\_vs2, 11, 3
	stxvd2x	\_vs3, 12, 3
	stxvd2x	\_vs4, 15, 3
	stxvd2x	\_vs5, 16, 3
	stxvd2x	\_vs6, 17, 3
	stxvd2x	\_vs7, 18, 3
	addi	3, 3, 128
.endm

.macro PermWriteL44
	xxlor	32+14, 10, 10
	xxlor	32+19, 11, 11
	xxlor	32+24, 12, 12
	xxlor	32+29, 13, 13
	xxpermdi 32+10, 32+14, 32+13, 3
	xxpermdi 32+11, 32+14, 32+13, 0
	xxpermdi 32+12, 32+19, 32+18, 3
	xxpermdi 32+13, 32+19, 32+18, 0
	xxpermdi 32+14, 32+24, 32+23, 3
	xxpermdi 32+15, 32+24, 32+23, 0
	xxpermdi 32+16, 32+29, 32+28, 3
	xxpermdi 32+17, 32+29, 32+28, 0
        stxvd2x    32+10, 0, 5
        stxvd2x    32+11, 10, 5
        stxvd2x    32+12, 11, 5
        stxvd2x    32+13, 12, 5
        stxvd2x    32+14, 15, 5
        stxvd2x    32+15, 16, 5
        stxvd2x    32+16, 17, 5
        stxvd2x    32+17, 18, 5
.endm

.macro PermWriteL24
	xxlor	32+14, 10, 10
	xxlor	32+19, 11, 11
	xxlor	32+24, 12, 12
	xxlor	32+29, 13, 13
        vmrgew 10, 13, 14
        vmrgow 11, 13, 14
        vmrgew 12, 18, 19
        vmrgow 13, 18, 19
        vmrgew 14, 23, 24
        vmrgow 15, 23, 24
        vmrgew 16, 28, 29
        vmrgow 17, 28, 29
        stxvd2x    32+10, 0, 5
        stxvd2x    32+11, 10, 5
        stxvd2x    32+12, 11, 5
        stxvd2x    32+13, 12, 5
        stxvd2x    32+14, 15, 5
        stxvd2x    32+15, 16, 5
        stxvd2x    32+16, 17, 5
        stxvd2x    32+17, 18, 5
.endm

.macro INTT_REDUCE_L24
	Load_L24Coeffs
	Compute_4Coeffs
	BREDUCE_4X 4, 9, 13, 17
	xxlor	10, 32+4, 32+4
	xxlor	11, 32+9, 32+9
	xxlor	12, 32+13, 32+13
	xxlor	13, 32+17, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	PermWriteL24
.endm

.macro INTT_REDUCE_L44
	Load_L44Coeffs
	Compute_4Coeffs
	BREDUCE_4X 4, 9, 13, 17
	xxlor	10, 32+4, 32+4
	xxlor	11, 32+9, 32+9
	xxlor	12, 32+13, 32+13
	xxlor	13, 32+17, 32+17
	Set_mont_consts
	Load_next_4zetas
	Perm_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	PermWriteL44
.endm

.macro INTT_REDUCE_4X start next step
	Load_4Coeffs \start, \next, \step
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
.endm

# intt
# t = r[j];
# r[j] = barrett_reduce(t + r[j + len]);
# r[j + len] = r[j + len] - t;
# r[j + len] = fqmul(zeta, r[j + len]);

#
# mlk_intt_ppc(r)
#
.global MLK_ASM_NAMESPACE(intt_ppc)
.align 4
MLK_ASM_FN_SYMBOL(intt_ppc)

	SAVE_REGS

	# init vectors and constants
	# Setup for Montgomery reduce
	lxvx	0, 0, 4

	li	10, QINV_OFFSET
	lxvx	32+V_QINV, 10, 4       # QINV
	xxlxor	32+3, 32+3, 32+3
	vspltish 4, 1
	xxlor	2, 32+2, 32+2			# QINV
	xxlor	3, 32+3, 32+3			# 0
	xxlor	4, 32+4, 32+4			# 1

	# Setup for Barrett reduce
	li	10, Q_OFFSET
	li	11, C20159_OFFSET
	lxvx	6, 10, 4			# V_MKQ
	lxvx	32+V20159, 11, 4		# V20159

	vspltisw 8, 13
	vadduwm  8, 8, 8
	xxlor	8, 32+8, 32+8	# V_26 store at vs8

	vspltisw 9, 1
	vsubuwm	10, 8, 9	# 25
	vslw	9, 9, 10
	xxlor	7, 32+9, 32+9	# V_25 syore at vs7

        li      10, 16
        li      11, 32
        li      12, 48
        li      15, 64
        li      16, 80
        li      17, 96
        li      18, 112

        #
        # Montgomery reduce loops with constant 1441
        #
        addi    14, 4, C1441_OFFSET
        lvx     V1441, 0, 14
        li      8, 4                   # loops
        mtctr   8

        Set_mont_consts
intt_ppc__Loopf:
        Reload_4coeffs
        MREDUCE_4X V1441, V1441, V1441, V1441, 6, 7, 8, 9
        Reload_4coeffs
        MREDUCE_4X V1441, V1441, V1441, V1441, 13, 18, 23, 28
        MWrite_8X 32+6, 32+7, 32+8, 32+9, 32+13, 32+18, 32+23, 32+28
        bdnz    intt_ppc__Loopf

        addi    3, 3, -512

.align 4
	#
	# 1. len = 2, start = 0, 4, 8, 12,...244, 248, 252 
	# Update zetas vectors, each vector has 2 zetas
	addi	14, 4, ZETA_INTT_OFFSET
	li	7, 4
	li	8, 4
	mtctr	8
	mr	5, 3
intt_ppc__Loop2:
	INTT_REDUCE_L24
	addi	5, 5, 128
	bdnz	intt_ppc__Loop2

.align 4
	#
	# 2. len = 4, start = 0, 8, 16, 24,...232, 240, 248 
	mr	5, 3
	li	7, 8
	li	8, 4                   # loops
	mtctr	8
intt_ppc__Loop4:
	INTT_REDUCE_L44
	addi	5, 5, 128
	bdnz	intt_ppc__Loop4

.align 4
	# 3. len = 8, start = 0, 16, 32, 48,...208, 224, 240 
	li	7, 16
	li	5, 0
	li	15, 4                   # loops
	mtctr	15

intt_ppc__Loop8:
	INTT_REDUCE_4X 5, 32, 32
	addi	5, 5, 128
	bdnz	intt_ppc__Loop8

.align 4
	#
	# 4. len = 16, start = 0, 32, 64,,...160, 192, 224
	li	5, 0
	li	7, 32

	INTT_REDUCE_4X 5, 64, 64

        li      5, 16
	addi	14, 14, -64
	INTT_REDUCE_4X 5, 64, 64

        li      5, 256
	INTT_REDUCE_4X 5, 64, 64

        li      5, 272
	addi	14, 14, -64
	INTT_REDUCE_4X 5, 64, 64

.align 4
        #
        # 5. len = 32, start = 0, 64, 128, 192
	li	5, 0
	li	7, 64

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
        addi    14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 128

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
        addi    14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 256

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
        addi    14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 384

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
        addi    14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

.align 4
	#
	# 6. len = 64, start = 0, 128
	li	5, 0
	li	7, 128
	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 64

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 256

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 320

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

.align 4
	# 7. len = 128, start = 0
	#
	li	5, 0            # start
	li	7, 256          # len * 2

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
	xxlor	9, 32+10, 32+10
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 64

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	xxlor	32+10, 9, 9
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 128

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	xxlor	32+10, 9, 9
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 192

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	xxlor	32+10, 9, 9
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

	RESTORE_REGS
	blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V20159
#undef V_25
#undef V_26
#undef V_MKQ
#undef V_QINV
#undef V_NMKQ
#undef V_Z0
#undef V_Z1
#undef V_Z2
#undef V_Z3
#undef V_ZETA
#undef V1441

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
