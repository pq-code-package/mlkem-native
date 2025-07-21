# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ buildEnv
, cbmc
, fetchFromGitHub
, callPackage
, bitwuzla
, ninja
, cadical
, z3
, cudd
, replaceVars
, fetchpatch
}:

buildEnv {
  name = "pqcp-cbmc";
  paths =
    builtins.attrValues {
      cbmc = cbmc.overrideAttrs (old: rec {
        version = "6.7.1";
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          hash = "sha256-GUY4Evya0GQksl0R4b01UDSvoxUEOOeq4oOIblmoF5o=";
          tag = "cbmc-6.7.1";
        };
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.11
      z3 = z3.overrideAttrs (old: rec {
        version = "4.12.6";
        src = fetchFromGitHub {
          owner = "Z3Prover";
          repo = "z3";
          rev = "z3-4.12.6";
          hash = "sha256-X4wfPWVSswENV0zXJp/5u9SQwGJWocLKJ/CNv57Bt+E=";
        };

        static-matrix-patch = fetchpatch {
          name = "gcc-15-fixes.patch";
          url = "https://github.com/Z3Prover/z3/commit/2ce89e5f491fa817d02d8fdce8c62798beab258b.patch";
          hash = "sha256-UvrUL27o/w1/sH/hO7bmvVupg3vbSjEqoIpoZh2BOhg=";
          includes = [ "src/math/lp/static_matrix.h" ];
        };

        static-matrix-def-patch = fetchpatch {
          # clang / gcc fixes. fixes typos in some member names
          name = "gcc-15-fixes.patch";
          url = "https://github.com/Z3Prover/z3/commit/2ce89e5f491fa817d02d8fdce8c62798beab258b.patch";
          includes = [ "src/math/lp/static_matrix_def.h" ];
          hash = "sha256-rEH+UzylzyhBdtx65uf8QYj5xwuXOyG6bV/4jgKkXGo=";
        };

        patches = [
          ./z3-lower-bound-typo.patch
          static-matrix-def-patch
          static-matrix-patch
        ];
      });

      inherit
        cadical#2.1.3
        bitwuzla# 0.7.0
        ninja; # 1.12.1
    };
}
