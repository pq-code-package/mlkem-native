# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# holtrace-prune: keeps only the lines of a HOLTrace trace that the named
# theorems need. A C replacement for HOLTrace's PyPy script of the same
# name, with the same output; see holtrace_prune.c.
{ stdenv }:

stdenv.mkDerivation {
  pname = "holtrace-prune";
  version = "1";
  src = ./holtrace_prune.c;
  dontUnpack = true;
  buildPhase = ''
    runHook preBuild
    $CC -O2 -Wall -Wextra -std=c99 -o holtrace-prune $src
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    install -Dm755 holtrace-prune "$out/bin/holtrace-prune"
    runHook postInstall
  '';
  meta.mainProgram = "holtrace-prune";
}
