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
 * Constant table used in the AArch64 decompression from 10 bits.
 * See autogen for details.
 *)

let mlkem_decompress_d10_table = (REWRITE_RULE[MAP] o define)
  `mlkem_decompress_d10_table:byte list = MAP word [
    0;   1;   1;   2;   2;   3;   3;   4;   5;   6;   6;   7;   7;   8;   8;   9;
    6;   7;   7;   8;   8;   9;   9;  10;  11;  12;  12;  13;  13;  14;  14;  15;
    2;   0;   0;   0; 254; 255; 252; 255;   2;   0;   0;   0; 254; 255; 252; 255;
  252;  15; 252;  15; 252;  15; 252;  15; 252;  15; 252;  15; 252;  15; 252;  15;
    8; 104;   8; 104;   8; 104;   8; 104;   8; 104;   8; 104;   8; 104;   8; 104
]`;;
