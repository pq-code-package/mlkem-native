# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "7a894768d53ed35c84a26c3a6c93ac40dc7d4a98";
  src = fetchFromGitHub {
    owner = "mkannwischer";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-UMHpsTebRSXL/PFwoVdLK3U3fygtiptUtuuu68/mTv0=";
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
