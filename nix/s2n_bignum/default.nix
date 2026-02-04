# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "d253084aefe7af7c5ae0db57054c09766ab97704";
  src = fetchFromGitHub {
    owner = "mkannwischer";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-KfT709dPWslQyHdjMqj3LaoWkcen+7jeG0FmgB8vcHY=";
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
