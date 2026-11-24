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
 * Constant table used in the AArch64 decompression from 4 bits.
 * See autogen for details.
 *)

let mlkem_decompress_d4_table = (REWRITE_RULE[MAP] o define)
  `mlkem_decompress_d4_table:byte list = MAP word [
    0; 208; 160; 112;  64;  16; 224; 176; 129;  81;  33; 241; 193; 145;  97;  49;
    0;   0;   1;   2;   3;   4;   4;   5;   6;   7;   8;   8;   9;  10;  11;  12
]`;;
