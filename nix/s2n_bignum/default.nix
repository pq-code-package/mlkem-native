# SPDX-License-Identifier: Apache-2.0
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "90cb5e35a823efee15cde72f0237af39a9bf7371";
  src = fetchFromGitHub {
    owner = "jargh";
    repo = "s2n-bignum-dev";
    rev = "${version}";
    hash = "sha256-6uDvLG04h8IKYln612wG/aXPsCB9k8Zsh/cE2Y980tQ=";
  };
  setupHook = writeText "setup-hook.sh" ''
    export S2N_BIGNUM_DIR="$1"
  '';
  patches = [ ./0001-fix-script-path.patch ];
  dontBuild = true;
  installPhase = ''
    mkdir -p $out
    cp -a . $out/
  '';
}
