(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

print_string "=== bytecode start: x86_64/mlkem/ntt_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/ntt_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/intt_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/intt_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/polyvec_basemul_acc_montgomery_cached_k2_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/polyvec_basemul_acc_montgomery_cached_k2_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/polyvec_basemul_acc_montgomery_cached_k3_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/polyvec_basemul_acc_montgomery_cached_k3_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/polyvec_basemul_acc_montgomery_cached_k4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/polyvec_basemul_acc_montgomery_cached_k4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/reduce_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/reduce_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/ntttobytes_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/ntttobytes_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/rej_uniform_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/rej_uniform_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/nttfrombytes_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/nttfrombytes_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/nttunpack_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/nttunpack_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_mulcache_compute_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_mulcache_compute_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/tomont_avx2_asm.o ========\n";;
print_literal_from_elf "x86_64/mlkem/tomont_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_compress_d4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_compress_d4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_decompress_d4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_decompress_d4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_compress_d5_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_compress_d5_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_decompress_d5_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_decompress_d5_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_compress_d10_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_compress_d10_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_decompress_d10_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_decompress_d10_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_compress_d11_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_compress_d11_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/poly_decompress_d11_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/poly_decompress_d11_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/keccak_f1600_x4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/keccak_f1600_x4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;
