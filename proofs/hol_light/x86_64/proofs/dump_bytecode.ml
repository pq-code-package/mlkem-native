(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_ntt.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_ntt.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_intt.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_intt.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_reduce.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_reduce.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_tobytes.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_tobytes.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_rej_uniform.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_rej_uniform.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_frombytes.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_frombytes.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_unpack.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_unpack.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_mulcache_compute.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_mulcache_compute.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_tomont.o ========\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_tomont.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d4.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d4.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d5.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d5.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d10.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d10.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d11.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d11.o";;
print_string "==== bytecode end =====================================\n\n";;
