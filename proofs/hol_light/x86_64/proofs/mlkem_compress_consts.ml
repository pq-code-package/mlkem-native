(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 *)

(* Compression/decompression constants for AVX2 implementations. *)

(* shufbidx *)
let decompress_d4_data = define `decompress_d4_data:int list = [
  &0; &0; &0; &0; &1; &1; &1; &1;
  &2; &2; &2; &2; &3; &3; &3; &3;
  &4; &4; &4; &4; &5; &5; &5; &5;
  &6; &6; &6; &6; &7; &7; &7; &7
]`;;
