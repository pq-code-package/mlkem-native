# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# To pin a specific upstream revision instead of nixpkgs' hol_light, comment
# out `pkgs.hol_light` below and uncomment the override, adjusting
# `version`/`rev`/`hash`.

{ pkgs }:

pkgs.hol_light

# pkgs.hol_light.overrideAttrs (old: rec {
#   version = "unstable-2026-04-17";
#   src = pkgs.fetchFromGitHub {
#     owner = "jrh13";
#     repo = "hol-light";
#     rev = "af5d20e033025a9f30a490d9c39edace632405a3";
#     hash = "sha256-R5hSHguVu7YPP7bnFJQ1Prc8Yy3L41LAB20LfEr/RUw=";
#   };
# })
