(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 *)

(* Keccak constants for x86_64 AVX2 implementations. *)

let rho8_constant = define `rho8_constant:int64 list = [
  word 0x0605040302010007;
  word 0x0E0D0C0B0A09080F;
  word 0x1615141312111017;
  word 0x1E1D1C1B1A19181F
]`;;

let rho56_constant = define `rho56_constant:int64 list = [
  word 0x0007060504030201;
  word 0x080F0E0D0C0B0A09;
  word 0x1017161514131211;
  word 0x181F1E1D1C1B1A19
]`;;
