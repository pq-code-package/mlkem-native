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
	xxpermdi 32+8, 32+8, 32+8, 2
	xxpermdi 32+12, 32+12, 32+12, 2
	xxpermdi 32+16, 32+16, 32+16, 2
	xxpermdi 32+20, 32+20, 32+20, 2

	lxvd2x	32+21, 3, 9
	lxvd2x	32+22, 3, 16
	lxvd2x	32+23, 3, 18
	lxvd2x	32+24, 3, 20
	xxpermdi 32+21, 32+21, 32+21, 2
	xxpermdi 32+22, 32+22, 32+22, 2
	xxpermdi 32+23, 32+23, 32+23, 2
	xxpermdi 32+24, 32+24, 32+24, 2

	vsubuhm 25, 8, 21		# r[j+len] - t
	vsubuhm 26, 12, 22		# r[j+len] - t
	vsubuhm 30, 16, 23		# r[j+len] - t
	vsubuhm 31, 20, 24		# r[j+len] - t
	vadduhm 8, 8, 21		# r[j+len] + t
	vadduhm 12, 12, 22		# r[j+len] + t
	vadduhm 16, 16, 23		# r[j+len] + t
	vadduhm 20, 20, 24		# r[j+len] + t
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
# MREDUCE_4X(len, start, _vz0, _vz1, _vz2, _vz3)
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
	lxv	32+V_Z0, 0(14)
	lxv	32+V_Z1, 16(14)
	lxv	32+V_Z2, 32(14)
	lxv	32+V_Z3, 48(14)
	addi	14, 14, 64
.endm

.macro Write_B4C _vs0 _vs1 _vs2 _vs3
	stxvx	\_vs0, 3, 9
	stxvx	\_vs1, 3, 16
	stxvx	\_vs2, 3, 18
	stxvx	\_vs3, 3, 20
.endm

.macro Write_M4C _vs0 _vs1 _vs2 _vs3
	stxvx	\_vs0, 3, 10
	stxvx	\_vs1, 3, 17
	stxvx	\_vs2, 3, 19
	stxvx	\_vs3, 3, 21
.endm

.macro Reload_4coeffs
	lxv	32+25, 0(3)
	lxv	32+26, 16(3)
	lxv	32+30, 32(3)
	lxv	32+31, 48(3)
	addi	3, 3, 64
.endm

.macro MWrite_8X _vs0 _vs1 _vs2 _vs3 _vs4 _vs5 _vs6 _vs7
	stxv	\_vs0, -128(3)
	stxv	\_vs1, -112(3)
	stxv	\_vs2, -96(3)
	stxv	\_vs3, -80(3)
	stxv	\_vs4, -64(3)
	stxv	\_vs5, -48(3)
	stxv	\_vs6, -32(3)
	stxv	\_vs7, -16(3)
.endm

.macro Write_Len2_4C _vs0 _vs1 _vs2 _vs3
        xxmrglw 32+12, \_vs0, 10
        xxmrghw 32+11, \_vs0, 10
        xxpermdi 10, 32+12, 32+11, 3
        xxmrglw 32+16, \_vs1, 11
        xxmrghw 32+15, \_vs1, 11
        xxpermdi 11, 32+16, 32+15, 3
        xxmrglw 32+12, \_vs2, 12
        xxmrghw 32+11, \_vs2, 12
        xxpermdi 12, 32+12, 32+11, 3
        xxmrglw 32+16, \_vs3, 13
        xxmrghw 32+15, \_vs3, 13
        xxpermdi 13, 32+16, 32+15, 3
        stxvd2x   10, 3, 9
        stxvd2x   11, 3, 16
        stxvd2x   12, 3, 18
        stxvd2x   13, 3, 20
.endm

.macro Write_Len4_4C _vs0 _vs1 _vs2 _vs3
	xxpermdi 10, 10, \_vs0, 3
	xxpermdi 11, 11, \_vs1, 3
	xxpermdi 12, 12, \_vs2, 3
	xxpermdi 13, 13, \_vs3, 3
        stxvd2x   10, 3, 9
        stxvd2x   11, 3, 16
        stxvd2x   12, 3, 18
        stxvd2x   13, 3, 20
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
	stxv	32+20, 128(1)
	stxv	32+21, 144(1)
	stxv	32+22, 160(1)
	stxv	32+23, 176(1)
	stxv	32+24, 192(1)
	stxv	32+25, 208(1)
	stxv	32+26, 224(1)
	stxv	32+27, 240(1)
	stxv	32+28, 256(1)
	stxv	32+29, 272(1)
	stxv	32+30, 288(1)
	stxv	32+31, 304(1)

	# init vectors and constants
	# Setup for Montgomery reduce
	lxv	0, 0(4)

	lxv	32+V_QINV, QINV_OFFSET(4)       # QINV
	xxlxor	32+3, 32+3, 32+3
	vspltish 4, 1
	xxlor	2, 32+2, 32+2			# QINV
	xxlor	3, 32+3, 32+3			# 0
	xxlor	4, 32+4, 32+4			# 1

	# Setup for Barrett reduce
	lxv	6, Q_OFFSET(4)			# V_MKQ
	lxv	32+V20159, C20159_OFFSET(4)	# V20159
	lxv	7, 0(4)	# V_25

	vspltisw 8, 13
	vadduwm  8, 8, 8
	xxlor	8, 32+8, 32+8	# V_26 store at vs8

	vspltisw 9, 1
	vsubuwm	10, 8, 9	# 25
	vslw	9, 9, 10
	xxlor	7, 32+9, 32+9	# V_25 syore at vs7

.align 4
	#
	# 1. len = 2, start = 0, 4, 8, 12,...244, 248, 252 
	# Update zetas vectors, each vector has 2 zetas
	addi	14, 4, IZETA_NTT_OFFSET127
	li	7, 4
	li	15, 4
	mtctr	15
	li	5, 0
intt_ppc__Loop2:
	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	xxlor	10, 32+4, 32+4
	xxlor	11, 32+9, 32+9
	xxlor	12, 32+13, 32+13
	xxlor	13, 32+17, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_Len2_4C 32+13, 32+18, 32+23, 32+28

	addi	5, 5, 64

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	xxlor	10, 32+4, 32+4
	xxlor	11, 32+9, 32+9
	xxlor	12, 32+13, 32+13
	xxlor	13, 32+17, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_Len2_4C 32+13, 32+18, 32+23, 32+28
	addi	5, 5, 64
	bdnz	intt_ppc__Loop2

.align 4
	#
	# 2. len = 4, start = 0, 8, 16, 24,...232, 240, 248 
	addi	14, 4, IZETA_NTT_OFFSET63
	li	5, 0
	li	7, 8
	li	15, 4                   # loops
	mtctr	15
intt_ppc__Loop4:
	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	xxlor	10, 32+4, 32+4
	xxlor	11, 32+9, 32+9
	xxlor	12, 32+13, 32+13
	xxlor	13, 32+17, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_Len4_4C 32+13, 32+18, 32+23, 32+28
	addi	5, 5, 64

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	xxlor	10, 32+4, 32+4
	xxlor	11, 32+9, 32+9
	xxlor	12, 32+13, 32+13
	xxlor	13, 32+17, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_Len4_4C 32+13, 32+18, 32+23, 32+28
	addi	5, 5, 64
	bdnz	intt_ppc__Loop4

.align 4
	# 3. len = 8, start = 0, 16, 32, 48,...208, 224, 240 
	#addi	14, 14, 512
	li	7, 16
	li	5, 0

	Load_4Coeffs 5, 32, 32
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 128

	Load_4Coeffs 5, 32, 32
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 256

	Load_4Coeffs 5, 32, 32
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 384

	Load_4Coeffs 5, 32, 32
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

.align 4
	#
	# 4. len = 16, start = 0, 32, 64,,...160, 192, 224
	#addi	14, 14, 768
	li	5, 0
	li	7, 32

	Load_4Coeffs 5, 64, 64
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
        li      5, 16
	Load_4Coeffs 5, 64, 64
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	addi	14, 14, -64
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

        li      5, 256
	Load_4Coeffs 5, 64, 64
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	Load_next_4zetas
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

        li      5, 272
	Load_4Coeffs 5, 64, 64
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	addi	14, 14, -64
	Load_next_4zetas
        MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

.align 4
        #
        # 5. len = 32, start = 0, 64, 128, 192
	#addi	14, 14, 896
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
	#addi	14, 14, 960
	li	5, 0
	li	7, 128
	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 64

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lxv	32+10, -16(14)
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 256

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28
	li	5, 320

	Load_4Coeffs 5, 16, 16
	BREDUCE_4X 4, 9, 13, 17
	Write_B4C 32+4, 32+9, 32+13, 32+17
	Set_mont_consts
	lxv	32+10, -16(14)
	MREDUCE_4X V_ZETA, V_ZETA, V_ZETA, V_ZETA, 13, 18, 23, 28
	Write_M4C 32+13, 32+18, 32+23, 32+28

.align 4
	# 7. len = 128, start = 0
	#
	#addi	14, 14, 992
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

.align 4
	#
	# Montgomery reduce loops with constant 1441
	#
	addi	14, 4, C1441_OFFSET
	lvx	V1441, 0, 14

	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 6, 7, 8, 9
	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 13, 18, 23, 28
	MWrite_8X 32+6, 32+7, 32+8, 32+9, 32+13, 32+18, 32+23, 32+28

	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 6, 7, 8, 9
	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 13, 18, 23, 28
	MWrite_8X 32+6, 32+7, 32+8, 32+9, 32+13, 32+18, 32+23, 32+28

	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 6, 7, 8, 9
	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 13, 18, 23, 28
	MWrite_8X 32+6, 32+7, 32+8, 32+9, 32+13, 32+18, 32+23, 32+28

	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 6, 7, 8, 9
	Reload_4coeffs
	MREDUCE_4X V1441, V1441, V1441, V1441, 13, 18, 23, 28
	MWrite_8X 32+6, 32+7, 32+8, 32+9, 32+13, 32+18, 32+23, 32+28

	lxv	32+20, 128(1)
	lxv	32+21, 144(1)
	lxv	32+22, 160(1)
	lxv	32+23, 176(1)
	lxv	32+24, 192(1)
	lxv	32+25, 208(1)
	lxv	32+26, 224(1)
	lxv	32+27, 240(1)
	lxv	32+28, 256(1)
	lxv	32+29, 272(1)
	lxv	32+30, 288(1)
	lxv	32+31, 304(1)
	ld	14, 56(1)
	ld	15, 64(1)
	ld	16, 72(1)
	ld	16, 72(1)
	ld	17, 80(1)
	ld	18, 88(1)
	ld	19, 96(1)
	ld	20, 104(1)
	ld	21, 112(1)

	mtlr	0
	addi    1, 1, 352
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
