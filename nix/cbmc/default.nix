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
        version = "6.4.1"; # remember to adjust this in ../flake.nix too
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = old.pname;
          tag = "${old.pname}-${version}";
          hash = "sha256-O8aZTW+Eylshl9bmm9GzbljWB0+cj2liZHs2uScERkM=";
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
