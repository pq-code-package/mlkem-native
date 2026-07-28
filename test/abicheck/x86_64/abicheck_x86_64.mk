# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# WARNING: This file is auto-generated from scripts/autogen
#          in the mlkem-native repository.
#          Do not modify it directly.
#
# Edit the YAML 'ABI.Features:' list in dev/<arch>/src/<kernel>.S
# and re-run scripts/autogen instead.
#
# For each capability declared by a kernel's ABI.Features list, this
# file appends the capability's CFLAGS to that kernel's .S object
# under mlkem/src/.

# Default each cap's file list to empty so the unconditional appends
# below are safe even when a cap has no kernels on this arch.
ABICHECK_REQ_AVX2_FILES :=

# AVX2: AVX2
ABICHECK_REQ_AVX2_FILES := \
  mlkem/src/fips202/native/x86_64/src/keccak_f1600_x4_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_intt_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_ntt_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_nttfrombytes_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_ntttobytes_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_nttunpack_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_compress_d10_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_compress_d11_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_compress_d4_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_compress_d5_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_decompress_d10_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_decompress_d11_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_decompress_d4_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_decompress_d5_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_poly_mulcache_compute_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_polyvec_basemul_acc_montgomery_cached_k2_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_polyvec_basemul_acc_montgomery_cached_k3_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_polyvec_basemul_acc_montgomery_cached_k4_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_reduce_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_rej_uniform_avx2_asm.S \
  mlkem/src/native/x86_64/src/mlkem_tomont_avx2_asm.S
ABICHECK_REQ_AVX2_OBJS := $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_REQ_AVX2_FILES))
$(ABICHECK_REQ_AVX2_OBJS): CFLAGS += -mavx2 -mbmi2
