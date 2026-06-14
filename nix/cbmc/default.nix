# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ buildEnv
, cbmc
, fetchFromGitHub
, callPackage
, bitwuzla
, ninja
, z3
}:

buildEnv {
  name = "pqcp-cbmc";
  paths =
    builtins.attrValues {
      cbmc = cbmc.overrideAttrs (_: {
        # We pin an unstable CBMC develop snapshot rather than the 6.9.0
        # release to pick up the workaround for the z3 soundness issue
        # (https://github.com/pq-code-package/mlkem-native/issues/1744,
        # https://github.com/diffblue/cbmc/pull/9011).
        # TODO: switch back to a tagged release once one ships with the fix.
        version = "6.9.0-unstable-2026-06-13";
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = "cbmc";
          hash = "sha256-2RcLAttkORSv3DqwIb1pj73aeYYY6r1RGpytTIW5NAc=";
          rev = "7750282a89dc57bb1a8e5a1ec544e8584be0cee4";
        };
        doInstallCheck = false;
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.12
      z3 = z3.overrideAttrs (_: {
        version = "4.15.3";
        src = fetchFromGitHub {
          owner = "Z3Prover";
          repo = "z3";
          rev = "z3-4.15.3";
          hash = "sha256-Lw037Z0t0ySxkgMXkbjNW5CB4QQLRrrSEBsLJqiomZ4=";
        };
      });

      inherit
        bitwuzla# 0.9.0
        ninja; # 1.13.2
    };
}
