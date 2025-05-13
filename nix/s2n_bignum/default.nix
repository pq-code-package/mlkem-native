# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "1fcccc89cc7762ae5c56ec660f25b5f1358ba308";
  src = fetchFromGitHub {
    owner = "jargh";
    repo = "s2n-bignum-dev";
    rev = "${version}";
    hash = "sha256-hSJ2WlrwVlTF3wSdMfdBbovBXMG5vltfPxp36hOMd5c=";
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
