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
        version = "e033ba1f10121e5a913991ab6fc672d34a115ec1"; # remember to adjust this in ../flake.nix too
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          rev = "e033ba1f10121e5a913991ab6fc672d34a115ec1";
          hash = "sha256-m2LhpldzBSYP9caQ2RJBl++Cx5Fx97y8E2P2SKcsmMM=";
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
