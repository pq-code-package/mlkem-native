(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 *)

(*
 * Constant table used in the AArch64 compression to 5 bits.
 * See autogen for details.
 *)

let mlkem_compress_d5_table = (REWRITE_RULE[MAP] o define)
  `mlkem_compress_d5_table:byte list = MAP word [
   59;   1;  59;   1;  59;   1;  59;   1;  59;   1;  59;   1;  59;   1;  59;   1;
    0;   1;   2;   3;   4;   8;   9;  10;  11;  12;   4;   8;   9;  10;  11;  12
]`;;
