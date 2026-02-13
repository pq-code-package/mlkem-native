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
        version = "6.8.0"; # tautschnig/smt2-output-stability
        src = fetchFromGitHub {
          owner = "tautschnig";
          repo = "cbmc";
          rev = "37f2da4d6e2e2646fdd3190949bb68c28612e6d3";
          hash = "sha256-VV33r1owrA4T8oZBfhI8F95HCtl7UAP2gXH4PBrZoQA=";
        };
        srccadical = cadical.src; # 3.0.0 from nixpkgs-unstable
        patches = [
          (builtins.elemAt old.patches 0) # cudd patch from nixpkgs
          ./0002-Do-not-download-sources-in-cmake.patch # cadical 3.0.0
        ];
        env = old.env // {
          NIX_CFLAGS_COMPILE = (old.env.NIX_CFLAGS_COMPILE or "") + " -Wno-error=switch-enum";
        };
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.12
      z3 = z3.overrideAttrs (old: rec {
        version = "4.15.3";
        src = fetchFromGitHub {
          owner = "Z3Prover";
          repo = "z3";
          rev = "z3-4.15.3";
          hash = "sha256-Lw037Z0t0ySxkgMXkbjNW5CB4QQLRrrSEBsLJqiomZ4=";
        };
      });

      inherit
        cadical# 3.0.0
        bitwuzla# 0.8.2
        ninja; # 1.13.2
    };
}
