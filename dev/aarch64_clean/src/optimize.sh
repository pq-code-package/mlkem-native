#!/usr/bin/env sh
# Copyright (c) 2024-2025 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

set -e

TARGET_NAME="Cortex-A55"
TARGET=Arm_Cortex_A55

echo "* mlk_polyvec_basemul_acc_montgomery_cached, K=2, ${TARGET_NAME}"

cp polyvec_clean.S polyvec_opt.S

slothy-cli Arm_AArch64 $TARGET \
  polyvec_opt.S -o polyvec_opt.S \
  -r mlk_polyvec_basemul_acc_montgomery_cached_asm_k2_clean,mlk_polyvec_basemul_acc_montgomery_cached_asm_k2_opt \
  -l k2_loop_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c sw_pipelining.allow_post \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo "* mlk_polyvec_basemul_acc_montgomery_cached, K=3, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  polyvec_opt.S -o polyvec_opt.S \
  -r mlk_polyvec_basemul_acc_montgomery_cached_asm_k3_clean,mlk_polyvec_basemul_acc_montgomery_cached_asm_k3_opt \
  -l k3_loop_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c sw_pipelining.allow_post \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo "* mlk_polyvec_basemul_acc_montgomery_cached, K=4, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  polyvec_opt.S -o polyvec_opt.S \
  -r mlk_polyvec_basemul_acc_montgomery_cached_asm_k4_clean,mlk_polyvec_basemul_acc_montgomery_cached_asm_k4_opt \
  -l k4_loop_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c sw_pipelining.allow_post \
  -c constraints.stalls_first_attempt=64

cp poly_clean.S poly_opt.S

echo "* mlk_poly_reduce, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  poly_opt.S -o poly_opt.S \
  -r mlk_poly_reduce_asm_clean,mlk_poly_reduce_asm_opt \
  -l loop_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp,v8--v15]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo "* mlk_poly_mulcache_compute, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  poly_opt.S -o poly_opt.S \
  -r mlk_poly_mulcache_compute_asm_clean,mlk_poly_mulcache_compute_asm_opt \
  -l mulcache_compute_loop_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp,v8--v15]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo "* mlk_poly_tomont, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  poly_opt.S -o poly_opt.S \
  -r mlk_poly_tomont_asm_clean,mlk_poly_tomont_asm_opt \
  -l poly_tomont_asm_loop \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp,v8--v15]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo " * ntt, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  ntt_clean.S -o ntt_opt.S \
  -r mlk_ntt_asm_clean,mlk_ntt_asm_opt \
  -l layer123_start \
  -l layer4567_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64

echo " * intt, ${TARGET_NAME}"

slothy-cli Arm_AArch64 $TARGET \
  intt_clean.S -o intt_opt.S \
  -r mlk_intt_asm_clean,mlk_intt_asm_opt \
  -l layer123_start \
  -l layer4567_start \
  -c sw_pipelining.enabled=true \
  -c inputs_are_outputs \
  -c reserved_regs="[x18--x30,sp]" \
  -c sw_pipelining.minimize_overlapping=False \
  -c variable_size \
  -c constraints.stalls_first_attempt=64
