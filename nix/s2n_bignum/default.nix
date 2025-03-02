# SPDX-License-Identifier: Apache-2.0
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "a7e47d3093b62625172f0e0bf4168c838ce1d955";
  src = fetchFromGitHub {
    owner = "jargh";
    repo = "s2n-bignum-dev";
    rev = "${version}";
    hash = "sha256-8pGeDR9U80wOP/PIPTJBITUt0JZu13EGwbYOD5INBa0";
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
