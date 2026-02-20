# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "3048e5dac5cbbcc7fba0787db14cf12c04568c05";
  src = fetchFromGitHub {
    owner = "manastasova";
    repo = "s2n-bignum-dev";
    rev = "${version}";
    hash = "sha256-C2wXja65r7s3oN35fykbNbmG1RxDy6LIvkwid3uoGOs=";
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
