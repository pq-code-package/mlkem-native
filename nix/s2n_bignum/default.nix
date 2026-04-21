# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "b70f1349bdc930769dbe5fee070044c27395e70a";
  src = fetchFromGitHub {
    owner = "awslabs";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-zZYIOp3bL/Asr4RdDYDFH804EJoRB4CKFmjKZepKEvA=";
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
