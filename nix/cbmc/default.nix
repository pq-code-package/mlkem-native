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

      inherit
        cadical#2.1.3
        bitwuzla# 0.7.0
        z3# 4.15.0
        ninja; # 1.12.1
    };
}
