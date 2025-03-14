# SPDX-License-Identifier: Apache-2.0
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
        version = "6.5.0";
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          rev = "32143ddf8ae93e6bd0f52189de509662348c2373";
          hash = "sha256-uciXv4dqESQrbNz+bQFpJcqoeWO8ZaRYjxoSUBOjlNI=";
        };
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.10

      inherit
        cadical#1.9.5
        bitwuzla# 0.7.0
        z3# 4.13.4
        ninja; # 1.11.1
    };
}
