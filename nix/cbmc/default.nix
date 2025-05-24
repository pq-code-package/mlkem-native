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
}:

buildEnv {
  name = "pqcp-cbmc";
  paths =
    builtins.attrValues {
      cbmc = cbmc.overrideAttrs (old: rec {
        version = "6.6.0";
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          hash = "sha256-ot0vVBgiSVru/RE7KeyTsXzDfs0CSa5vaFsON+PCZZo=";
          tag = "cbmc-6.6.0";
        };
        # TODO: Remove those once upstream has removed the third patch
        patches = [
          (replaceVars ./0001-Do-not-download-sources-in-cmake.patch {
            cudd = cudd.src;
          })
          ./0002-Do-not-download-sources-in-cmake.patch
        ];
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.11

      inherit
        cadical#2.1.3
        bitwuzla# 0.7.0
        z3# 4.15.0
        ninja; # 1.12.1
    };
}
