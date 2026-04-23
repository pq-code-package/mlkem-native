(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "arm/proofs/base.ml";;

print_string "=== bytecode start: aarch64/mlkem/keccak_f1600_x1_v84a_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/keccak_f1600_x1_v84a_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/keccak_f1600_x1_scalar_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/keccak_f1600_x1_scalar_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/keccak_f1600_x2_v84a_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/keccak_f1600_x2_v84a_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm.o \n";;
print_literal_from_elf "aarch64/mlkem/keccak_f1600_x4_v8a_scalar_hybrid_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/intt_aarch64_asm.o ===============\n";;
print_literal_from_elf "aarch64/mlkem/intt_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/ntt_aarch64_asm.o ================\n";;
print_literal_from_elf "aarch64/mlkem/ntt_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/polyvec_basemul_acc_montgomery_cached_k3_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/polyvec_basemul_acc_montgomery_cached_k4_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/poly_mulcache_compute_aarch64_asm.o ===\n";;
print_literal_from_elf "aarch64/mlkem/poly_mulcache_compute_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/poly_reduce_aarch64_asm.o ========\n";;
print_literal_from_elf "aarch64/mlkem/poly_reduce_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/poly_tobytes_aarch64_asm.o =======\n";;
print_literal_from_elf "aarch64/mlkem/poly_tobytes_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/poly_tomont_aarch64_asm.o ========\n";;
print_literal_from_elf "aarch64/mlkem/poly_tomont_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: aarch64/mlkem/rej_uniform_aarch64_asm.o ========\n";;
print_literal_from_elf "aarch64/mlkem/rej_uniform_aarch64_asm.o";;
print_string "==== bytecode end =====================================\n\n";;
