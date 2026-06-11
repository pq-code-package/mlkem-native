# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# slothy is packaged in nixpkgs (>= 26.05) and used by default.
#
# To pin a specific upstream revision instead, comment out `pkgs.slothy`
# below and uncomment the override, adjusting `version`/`sha256`.

{ pkgs }:

# pkgs.slothy

pkgs.slothy.overrideAttrs (old: rec {
  version = "4302933bea0d33a11df33339bfa1ea3fee6bf2e6";
  src = pkgs.fetchFromGitHub {
    owner = "slothy-optimizer";
    repo = "slothy";
    rev = version;
    sha256 = "sha256-XQ+YtaRCRtzAItQW/zLlj2wIKRz99cjttxSaEcgD8Pk=";
  };
})
