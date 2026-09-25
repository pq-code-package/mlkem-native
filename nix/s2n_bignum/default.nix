# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "bf75b6c61dae86bbb383785987bc316e20b7ebbf";
  src = fetchFromGitHub {
    owner = "awslabs";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-5e9bX6IU84D4L/RXb1EAhUmI+47A/ypnP1acLoZ0i24=";
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
