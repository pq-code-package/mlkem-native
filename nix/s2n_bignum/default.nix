# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "437824ad6a4b8760f5505db811fdd78ea07fc037";
  src = fetchFromGitHub {
    owner = "mkannwischer";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-/Mqn6H0t7Sg3QvGNKgFdmLukc8VB5nO9xpbkDVhXiZg=";
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
