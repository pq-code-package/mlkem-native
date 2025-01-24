# SPDX-License-Identifier: Apache-2.0
{ valgrind, ... }:
valgrind.overrideAttrs (_: {
  patches = [
    ./valgrind-varlat-patch-20240808.txt
  ];
})
