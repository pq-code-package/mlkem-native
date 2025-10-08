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

#include "consts.h"

#define V_QINV  2
#define V_NMKQ  5
#define	V_Z0    7
#define	V_Z1    8
#define	V_Z2    9
#define	V_Z3    10
#define V_ZETA  10

.machine "any"
.text

.macro Load_4Coeffs start next step
	mr	9, \start
	add	10, 7, 9	# J + len*2
	addi	16, 9, \next
	addi	17, 10, \step
	addi	18, 16, \next
	addi	19, 17, \step
	addi	20, 18, \next
	addi	21, 19, \step
	lxvd2x	32+13, 3, 10	# r[j+len]
	lxvd2x	32+18, 3, 17	# r[j+len]
	lxvd2x	32+23, 3, 19	# r[j+len]
	lxvd2x	32+28, 3, 21	# r[j+len]
	xxpermdi 32+13, 32+13, 32+13, 2
	xxpermdi 32+18, 32+18, 32+18, 2
	xxpermdi 32+23, 32+23, 32+23, 2
	xxpermdi 32+28, 32+28, 32+28, 2
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
        lxv     32+25, 0(5)     # a[j], r[j+len]
        lxv     32+26, 16(5)    # a[j], r[j+len]
        vmrgew 13, 25, 26
        vmrgow 12, 25, 26
        lxv     32+25, 32(5)    # a[j], r[j+len]
        lxv     32+26, 48(5)    # a[j], r[j+len]
        vmrgew 18, 25, 26
        vmrgow 17, 25, 26
        lxv     32+25, 64(5)    # a[j], r[j+len]
        lxv     32+26, 80(5)    # a[j], r[j+len]
        vmrgew 23, 25, 26
        vmrgow 22, 25, 26
        lxv     32+25, 96(5)    # a[j], r[j+len]
        lxv     32+26, 112(5)   # a[j], r[j+len]
        vmrgew 28, 25, 26
        vmrgow 27, 25, 26
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
        lxv     1, 0(5)         # rj0, rj1, rj2, rj3,
                                # rjlen4, rjlen5, rjlen6, rjlen7
        lxv     2, 16(5)        # rj8, rj9, rj10, rj11
                                # rjlen12, rjlen13, rjlen14, rjlen15
        xxpermdi 32+13, 2, 1, 0 # rjlen4 - rjlen7, rjlen12 - rjlen15
        xxpermdi 32+12, 2, 1, 3 # rj0 - rj4, rj8 - rj11
        lxv     3, 32(5)
        lxv     4, 48(5)
        xxpermdi 32+18, 4, 3, 0
        xxpermdi 32+17, 4, 3, 3
        lxv     1, 64(5)
        lxv     2, 80(5)
        xxpermdi 32+23, 2, 1, 0
        xxpermdi 32+22, 2, 1, 3
        lxv     3, 96(5)
        lxv     4, 112(5)
        xxpermdi 32+28, 4, 3, 0
        xxpermdi 32+27, 4, 3, 3
.endm

#
# montgomery_reduce
# t = a * QINV
# t = (a - (int32_t)t*_MLKEM_Q) >> 16
#
#-----------------------------------
# MREDUCE_4X(_vz0, _vz1, _vz2, _vz3)
#
.macro MREDUCE_4X _vz0 _vz1 _vz2 _vz3
	# fqmul = zeta * coefficient
	# Modular multification bond by 2^16 * q in abs value
	vmladduhm 15, 13, \_vz0, 3
	vmladduhm 20, 18, \_vz1, 3
	vmladduhm 25, 23, \_vz2, 3
	vmladduhm 30, 28, \_vz3, 3

	# Signed multiply-high-round; outputs are bound by 2^15 * q in abs value
	vmhraddshs 14, 13, \_vz0, 3
	vmhraddshs 19, 18, \_vz1, 3
	vmhraddshs 24, 23, \_vz2, 3
	vmhraddshs 29, 28, \_vz3, 3

	vmladduhm 15, 15, V_QINV, 3
	vmladduhm 20, 20, V_QINV, 3
	vmladduhm 25, 25, V_QINV, 3
	vmladduhm 30, 30, V_QINV, 3

	vmhraddshs 15, 15, V_NMKQ, 14
	vmhraddshs 20, 20, V_NMKQ, 19
	vmhraddshs 25, 25, V_NMKQ, 24
	vmhraddshs 30, 30, V_NMKQ, 29

	vsrah 13, 15, 4		# >> 1
	vsrah 18, 20, 4		# >> 1
	vsrah 23, 25, 4		# >> 1
	vsrah 28, 30, 4		# >> 1

.endm

.macro Load_4Aj
	lxvd2x	32+12, 3, 9	# r[j]
	lxvd2x	32+17, 3, 16	# r[j]
	lxvd2x	32+22, 3, 18	# r[j]
	lxvd2x	32+27, 3, 20	# r[j]
	xxpermdi 32+12, 32+12, 32+12, 2
	xxpermdi 32+17, 32+17, 32+17, 2
	xxpermdi 32+22, 32+22, 32+22, 2
	xxpermdi 32+27, 32+27, 32+27, 2
.endm

.macro Compute_4Coeffs
	# Since the result of the Montgomery multiplication is bounded
	# by q in absolute value.
	# Finally to complete the final update of the results with add/sub
	vsubuhm 16, 12, 13		# r - t
	vadduhm 15, 13, 12		# r + t
	vsubuhm 21, 17, 18		# r - t
	vadduhm 20, 18, 17		# r + t
	vsubuhm 26, 22, 23		# r - t
	vadduhm 25, 23, 22		# r + t
	vsubuhm 31, 27, 28		# r - t
	vadduhm 30, 28, 27		# r + t
.endm

.macro NTT_MREDUCE_4X start next step _vz0 _vz1 _vz2 _vz3
        Load_4Coeffs \start, \next, \step
        MREDUCE_4x \_vz0, \_vz1, \_vz2, \_vz3
        Load_4Aj
        Compute_4Coeffs
.endm

.macro Write_One
	stxvx 32+15, 3, 9
	stxvx 32+16, 3, 10
	stxvx 32+20, 3, 16
	stxvx 32+21, 3, 17
	stxvx 32+25, 3, 18
	stxvx 32+26, 3, 19
	stxvx 32+30, 3, 20
	stxvx 32+31, 3, 21
.endm

.macro PermWriteL44
	Compute_4Coeffs
	xxpermdi 0, 32+16, 32+15, 3
	xxpermdi 1, 32+16, 32+15, 0
	xxpermdi 2, 32+21, 32+20, 3
	xxpermdi 3, 32+21, 32+20, 0
	xxpermdi 4, 32+26, 32+25, 3
	xxpermdi 5, 32+26, 32+25, 0
	xxpermdi 6, 32+31, 32+30, 3
	xxpermdi 7, 32+31, 32+30, 0
	stxv	0, 0(5)
	stxv	1, 16(5)
	stxv	2, 32(5)
	stxv	3, 48(5)
	stxv	4, 64(5)
	stxv	5, 80(5)
	stxv	6, 96(5)
	stxv	7, 112(5)
.endm

.macro PermWriteL24
        Compute_4Coeffs
        vmrgew 10, 16, 15
        vmrgow 11, 16, 15
        vmrgew 12, 21, 20
        vmrgow 13, 21, 20
        vmrgew 14, 26, 25
        vmrgow 15, 26, 25
        vmrgew 16, 31, 30
        vmrgow 17, 31, 30
        stxv    32+10, 0(5)
        stxv    32+11, 16(5)
        stxv    32+12, 32(5)
        stxv    32+13, 48(5)
        stxv    32+14, 64(5)
        stxv    32+15, 80(5)
        stxv    32+16, 96(5)
        stxv    32+17, 112(5)
.endm

.macro Load_next_4zetas
	lxv	32+V_Z0, 0(14)
	lxv	32+V_Z1, 16(14)
	lxv	32+V_Z2, 32(14)
	lxv	32+V_Z3, 48(14)
	addi	14, 14, 64
.endm

#
# mlk_ntt_ppc(int16_t *r)
#
.global MLK_ASM_NAMESPACE(ntt_ppc)
.align 4
MLK_ASM_FN_SYMBOL(ntt_ppc)

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

	# get MLKEM_Q
	lvx	V_NMKQ,0,4

	# zetas array
	addi	14, 4, ZETA_NTT_OFFSET

	vxor	3, 3, 3
	vspltish 4, 1

	lxv	32+V_QINV, QINV_OFFSET(4)

.align 4
	#
	# Compute coefficients of the NTT based on the following loop.
	#   for (len = 128; len ≥ 2; len =  len/2)
	#
	# 1. len = 128, start = 0
	#
	li	5, 0		# start
	li	7, 256		# len * 2
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16

	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 64
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 128
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 192
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One

.align 4
	#
	# 2. len = 64, start = 0, 128
	# k += 2
	li	5, 0
	li	7, 128
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 64
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 256

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 320
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One

.align 4
	#
	# 3. len = 32, start = 0, 64, 128, 192
	# k += 4
	li	5, 0
	li	7, 64
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 128

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 256

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 384

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	NTT_MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One

.align 4
	#
	# 4. len = 16, start = 0, 32, 64,,...160, 192, 224
	# k += 8
	li	5, 0
	li	7, 32
	Load_next_4zetas
	NTT_MREDUCE_4X 5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 16
	NTT_MREDUCE_4X 5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One

	Load_next_4zetas
	li	5, 256
	NTT_MREDUCE_4X 5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 272
	NTT_MREDUCE_4X  5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One

.align 4
	#
	# 5. len = 8, start = 0, 16, 32, 48,...208, 224, 240 
	# k += 16
	li	5, 0
	li	7, 16
	Load_next_4zetas
	NTT_MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 128

	Load_next_4zetas
	NTT_MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 256

	Load_next_4zetas
	NTT_MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 384

	Load_next_4zetas
	NTT_MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One

	#
	# 6. len = 4, start = 0, 8, 16, 24,...232, 240, 248 
	# k += 32
	li	15, 4			# loops
	mtctr	15
        mr      5, 3
	li	7, 8
.align 4
ntt_ppc__Len4:
	Load_next_4zetas
        Load_L44Coeffs
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3
	PermWriteL44
	addi	5, 5, 128

	bdnz	ntt_ppc__Len4

	#
	# 7. len = 2, start = 0, 4, 8, 12,...244, 248, 252 
	# k += 64
	# Update zetas vectors, each vector has 2 zetas

	li	15, 4
	mtctr	15
	mr	5, 3
	li	7, 4
.align 4
ntt_ppc__Len2:
	Load_next_4zetas
        Load_L24Coeffs
	MREDUCE_4X V_Z0, V_Z1, V_Z2, V_Z3
	PermWriteL24
	addi	5, 5, 128

	bdnz	ntt_ppc__Len2

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
#undef V_QINV
#undef V_NMKQ
#undef V_ZETA

#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
