# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "68a258c57901f272a3b0dda029b15031dc7d182d";
  src = fetchFromGitHub {
    owner = "jargh";
    repo = "s2n-bignum-dev";
    rev = "${version}";
    hash = "sha256-/9Hgp53t2suKDmsvtdmlE9gJxh3R27BqdAd82RSB/8E=";
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
