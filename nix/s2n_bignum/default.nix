# SPDX-License-Identifier: Apache-2.0
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "7c018f70667310c96ac5d6c27468104117bd51c0";
  src = fetchFromGitHub {
    owner = "jargh";
    repo = "s2n-bignum-dev";
    rev = "${version}";
    hash = "sha256-/Iyz2mnxGSbmte9lT1JbY4WcBmWWrc7tUpZ0HfAUD+4";
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
