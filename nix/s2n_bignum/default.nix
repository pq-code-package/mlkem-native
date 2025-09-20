# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "b93469e03f0a31c7b97fcb0c2ef2f1e1ca478237";
  src = fetchFromGitHub {
    owner = "awslabs";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-O5eEKz238b+weTeVpmqnK8kvu53AXpZTm2E8Tk+FBn4=";
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
