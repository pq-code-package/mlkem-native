(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/base.ml";;

print_string "=== bytecode start: mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o ===\n";;
print_literal_from_elf "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o ===\n";;
print_literal_from_elf "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.o";;
print_string "==== bytecode end =====================================\n\n";;

print_string "=== bytecode start: /mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o ===\n";;
print_literal_from_elf "mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.o";;
print_string "==== bytecode end =====================================\n\n";;
