# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ buildEnv
, cbmc
, fetchFromGitHub
, callPackage
, bitwuzla
, ninja
, cadical
, z3
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
          rev = "3c915ebe35448a20555c1ef55d51540b52c5c34a";
          hash = "sha256-ot0vVBgiSVru/RE7KeyTsXzDfs0CSa5vaFsON+PCZZo=";
        };
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.10

      inherit
        cadical#1.9.5
        bitwuzla# 0.7.0
        z3# 4.14.1
        ninja; # 1.11.1
    };
}
