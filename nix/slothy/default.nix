# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# slothy is packaged in nixpkgs (>= 26.05) and used by default.
#
# To pin a specific upstream revision instead, comment out `pkgs.slothy`
# below and uncomment the override, adjusting `version`/`sha256`.

{ pkgs }:

pkgs.slothy

# pkgs.slothy.overrideAttrs (old: rec {
#   version = "6d35cc147a0859f53f8bfc0d0f2ea3b947c8c4eb";
#   src = pkgs.fetchFromGitHub {
#     owner = "slothy-optimizer";
#     repo = "slothy";
#     rev = version;
#     sha256 = "sha256-TplnMBjNvY7f8RTOwRWcv+cqxcRZ8KHx6toczNC5QGo=";
#   };
# })
