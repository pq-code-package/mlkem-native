# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "13cb1dd13989db8b94a98e74cba26dda2a71d7de";
  src = fetchFromGitHub {
    owner = "mkannwischer";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-jqF3U7J0hUwM2XJQvvGjje3noEO+snTjLCctsSPadp8=";
  };
  setupHook = writeText "setup-hook.sh" ''
    export S2N_BIGNUM_DIR="$1"
  '';
  patches = [ ];
  dontBuild = true;
  installPhase = ''
    mkdir -p $out
    cp -a . $out/
  '';
}
