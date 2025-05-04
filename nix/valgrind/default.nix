# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ valgrind, ... }:
valgrind.overrideAttrs (_: {
  patches = [
    ./valgrind-varlat-patch-20240808.txt
  ];
})
