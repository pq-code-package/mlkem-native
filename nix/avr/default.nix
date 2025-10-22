# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ pkgs }:

let
  # Patched simavr with increased RAM and fixed UART output
  simavr-patched = pkgs.simavr.overrideAttrs (oldAttrs: {
    patches = (oldAttrs.patches or [ ]) ++ [
      ./simavr-32kb-ram.patch
      ./simavr-uart-output-fix.patch
    ];
  });
in
{
  packages = [
    pkgs.pkgsCross.avr.buildPackages.gcc
    pkgs.avrdude
    simavr-patched
  ] ++ pkgs.lib.optionals (pkgs.stdenv.isDarwin) [ pkgs.git ];
}
