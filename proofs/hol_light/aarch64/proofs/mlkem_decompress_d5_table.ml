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
 * Constant table used in the AArch64 decompression from 5 bits.
 * See autogen for details.
 *)

let mlkem_decompress_d5_table = (REWRITE_RULE[MAP] o define)
  `mlkem_decompress_d5_table:byte list = MAP word [
    0;   1;   0;   1;   1;   2;   1;   2;   2;   3;   3;   4;   3;   4;   4;   5;
    5;   6;   5;   6;   6;   7;   6;   7;   7;   8;   8;   9;   8;   9;   9;  10;
   10;  11;  10;  11;  11;  12;  11;  12;  12;  13;  13;  14;  13;  14;  14;  15;
   11;  12;  11;  12;  12;  13;  12;  13;  13;  14;  14;  15;  14;  15;  15;  16;
    7;   0;   2;   0;   5;   0;   0;   0;   3;   0;   6;   0;   1;   0;   4;   0;
  128;  15; 128;  15; 128;  15; 128;  15; 128;  15; 128;  15; 128;  15; 128;  15;
    8; 104;   8; 104;   8; 104;   8; 104;   8; 104;   8; 104;   8; 104;   8; 104
]`;;
