(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 4 bits.                         *)
(* ========================================================================= *)

(* Load base theories for x86_64 from s2n-bignum *)
needs "x86/proofs/base.ml";;

needs "common/mlkem_specs.ml";;

(* print_literal_from_elf "x86_64/mlkem/mlkem_poly_compress_d4.o";; *)

let mlkem_poly_compress_d4_mc =
  define_assert_from_elf "mlkem_poly_compress_d4_mc" "x86_64/mlkem/mlkem_poly_compress_d4.o"
(*** BYTECODE START ***)
[
];;
(*** BYTECODE END ***)
