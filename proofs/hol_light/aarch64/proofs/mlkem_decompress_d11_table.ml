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
 * Constant table used in the AArch64 decompression from 11 bits.
 * See autogen for details.
 *)

let mlkem_decompress_d11_table = (REWRITE_RULE[MAP] o define)
  `mlkem_decompress_d11_table:byte list = MAP word [
    0;   1;   1;   2;   2;   3;   4;   5;   5;   6;   6;   7;   8;   9;   9;  10;
    2;   3;   3;   4;   4;   5;   6;   7;   7;   8;   8;   9;  10;  11;  11;  12;
    5;   6;   6;   7;   7;   8;   9;  10;  10;  11;  11;  12;  13;  14;  14;  15;
    7;   8;   8;   9;   9;  10;  11;  12;  12;  13;  13;  14;  15;  16;  16;  17;
    1;   0; 254; 255; 252; 255;   0;   0; 253; 255; 252; 255; 255; 255; 252; 255;
  254;  15; 254;  15; 252;  31; 254;  15; 254;  15; 248;  63; 254;  15; 254;  15;
    8; 104;   8; 104;   4;  52;   8; 104;   8; 104;   2;  26;   8; 104;   8; 104
]`;;
