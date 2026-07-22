# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ pkgs }:

let
  # Patched simavr with increased RAM and fixed UART output
  simavr-patched = pkgs.simavr.overrideAttrs (oldAttrs: {
    patches = (oldAttrs.patches or [ ]) ++ [
      ./simavr-64kb-ram.patch
      ./simavr-uart-output-fix.patch
      ./simavr-32k-eeprom.patch
      # Exit-code commands (SIMAVR_CMD_EXIT_CODE_*), not yet in a release
      (pkgs.fetchpatch {
        url = "https://github.com/buserror/simavr/commit/c9354b32e057e409c2fbc9454e26db3b3103c26a.patch";
        hash = "sha256-JKIjBmvlIrUe/0lJ2ngVgN3sCB0UJYWtv2dNp0wcPEY=";
      })
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
