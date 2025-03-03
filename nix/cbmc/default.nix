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
        version = "weaken-is-fresh-assert"; # remember to adjust this in ../flake.nix too
        src = fetchFromGitHub {
          owner = "remi-delmas-3000";
          repo = "cbmc";
          rev = "d4a1c6d33ab41b3ef416bb5fd812d2050ecc9fd7";
          hash = "sha256-PXCcvArTXhRWRCzlgDXFsrD+XAGL1zt+iooGM9lFF2Q=";
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
