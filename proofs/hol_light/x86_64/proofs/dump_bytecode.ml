(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "s2n_bignum/x86/proofs/base.ml";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_ntt_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_ntt_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_intt_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_intt_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_polyvec_basemul_acc_montgomery_cached_k2_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_polyvec_basemul_acc_montgomery_cached_k2_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_polyvec_basemul_acc_montgomery_cached_k3_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_polyvec_basemul_acc_montgomery_cached_k3_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_polyvec_basemul_acc_montgomery_cached_k4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_polyvec_basemul_acc_montgomery_cached_k4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_reduce_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_reduce_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_ntttobytes_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_ntttobytes_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_rej_uniform_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_rej_uniform_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_nttfrombytes_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_nttfrombytes_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_nttunpack_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_nttunpack_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_mulcache_compute_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_mulcache_compute_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_tomont_avx2_asm.o ========\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_tomont_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_compress_d4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_compress_d5_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d5_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d5_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d5_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_compress_d10_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d10_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d10_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d10_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_compress_d11_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d11_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/mlkem_poly_decompress_d11_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/mlkem_poly_decompress_d11_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: x86_64/mlkem/keccak_f1600_x4_avx2_asm.o ===\n";;
print_literal_from_elf "x86_64/mlkem/keccak_f1600_x4_avx2_asm.o";;
print_string "==== bytecode end =====================================\n\n";;
