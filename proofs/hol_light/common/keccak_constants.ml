(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 *)

(* Keccak-f[1600] round constants RC[i] for i = 0..23. *)

let round_constants = define `round_constants:int64 list = [
  word 0x0000000000000001;
  word 0x0000000000008082;
  word 0x800000000000808A;
  word 0x8000000080008000;
  word 0x000000000000808B;
  word 0x0000000080000001;
  word 0x8000000080008081;
  word 0x8000000000008009;
  word 0x000000000000008A;
  word 0x0000000000000088;
  word 0x0000000080008009;
  word 0x000000008000000A;
  word 0x000000008000808B;
  word 0x800000000000008B;
  word 0x8000000000008089;
  word 0x8000000000008003;
  word 0x8000000000008002;
  word 0x8000000000000080;
  word 0x000000000000800A;
  word 0x800000008000000A;
  word 0x8000000080008081;
  word 0x8000000000008080;
  word 0x0000000080000001;
  word 0x8000000080008008
]`;;
