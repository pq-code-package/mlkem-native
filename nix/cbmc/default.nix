# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ buildEnv
, cbmc
, fetchFromGitHub
, callPackage
, bitwuzla
, ninja
, z3
}:

buildEnv {
  name = "pqcp-cbmc";
  paths =
    builtins.attrValues {
      cbmc = cbmc.overrideAttrs (_: {
        version = "6.9.0";
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          hash = "sha256-SMJBnzoyTwcwJa9L2X1iX2W4Z/Mwoirf8EXfoyG0dRI=";
          tag = "cbmc-6.9.0";
        };
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.12
      z3 = z3.overrideAttrs (_: {
        version = "4.15.3";
        src = fetchFromGitHub {
          owner = "Z3Prover";
          repo = "z3";
          rev = "z3-4.15.3";
          hash = "sha256-Lw037Z0t0ySxkgMXkbjNW5CB4QQLRrrSEBsLJqiomZ4=";
        };
      });

      inherit
        bitwuzla# 0.8.2
        ninja; # 1.13.2
    };
}
