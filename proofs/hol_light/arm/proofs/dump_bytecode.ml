(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/base.ml";;

print_string "=== bytecode start: arm/mlkem/keccak_f1600_x1_v84a.o ===\n";;
print_literal_from_elf "arm/mlkem/keccak_f1600_x1_v84a.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/keccak_f1600_x1_scalar.o ===\n";;
print_literal_from_elf "arm/mlkem/keccak_f1600_x1_scalar.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/keccak_f1600_x2_v84a.o ===\n";;
print_literal_from_elf "arm/mlkem/keccak_f1600_x2_v84a.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/keccak_f1600_x4_v8a_scalar.o \n";;
print_literal_from_elf "arm/mlkem/keccak_f1600_x4_v8a_scalar.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/keccak_f1600_x4_v8a_v84a_scalar.o ===\n";;
print_literal_from_elf "arm/mlkem/keccak_f1600_x4_v8a_v84a_scalar.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_intt.o ===============\n";;
print_literal_from_elf "arm/mlkem/mlkem_intt.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_ntt.o ================\n";;
print_literal_from_elf "arm/mlkem/mlkem_ntt.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o ===\n";;
print_literal_from_elf "arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o ===\n";;
print_literal_from_elf "arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o ===\n";;
print_literal_from_elf "arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_poly_mulcache_compute.o ===\n";;
print_literal_from_elf "arm/mlkem/mlkem_poly_mulcache_compute.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_poly_reduce.o ========\n";;
print_literal_from_elf "arm/mlkem/mlkem_poly_reduce.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_poly_tobytes.o =======\n";;
print_literal_from_elf "arm/mlkem/mlkem_poly_tobytes.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_poly_tomont.o ========\n";;
print_literal_from_elf "arm/mlkem/mlkem_poly_tomont.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: arm/mlkem/mlkem_rej_uniform.o ========\n";;
print_literal_from_elf "arm/mlkem/mlkem_rej_uniform.o";;
print_string "==== bytecode end =====================================\n\n";;
