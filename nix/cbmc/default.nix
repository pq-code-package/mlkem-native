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
        version = "6.7.0";
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          hash = "sha256-a2Lc4Vou+tND/d8bRw9MpjWrPgdE9gwisfT+xbHUMjY=";
          tag = "cbmc-6.7.0";
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
