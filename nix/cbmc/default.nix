# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ buildEnv
, cbmc
, fetchFromGitHub
, callPackage
, bitwuzla
, cvc5
, ninja
, z3
}:

buildEnv {
  name = "pqcp-cbmc";
  paths =
    builtins.attrValues {
      cbmc = cbmc.overrideAttrs (_: {
        version = "6.11.0";
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          hash = "sha256-GHpgcGBE/AAhTVxGVzTPMdZ8BkuXa7/OgMumZJ8ENRc";
          tag = "cbmc-6.11.0";
        };
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.12
      inherit
        bitwuzla# 0.9.0
        cvc5# 1.3.4 (from nixpkgs-26.05)
        ninja# 1.13.2
        z3; # 5.3.2 (from nixos-unstable, passed in via flake.nix)
    };
}
