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
        version = "6.8.0";
        src = fetchFromGitHub {
          owner = "tautschnig";
          repo = "cbmc";
          hash = "sha256-ng1zjICpmoHUWkG1PuLRmLtaUBmEALpRgNEpbsrnMV8=";
          rev = "4f514dbd70c89e3bae03a59f1dc9837acf25885c";
        };
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.11
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
        cadical#2.1.3
        bitwuzla# 0.8.2
        ninja; # 1.12.1
    };
}
