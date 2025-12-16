# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, python3
, pkgs
, llvm
, gcc
}:

let
  pythonEnv = python3.withPackages (ps: with ps; [
    ortools
    sympy
    unicorn
  ]);
in
stdenvNoCC.mkDerivation rec {
  pname = "slothy-cli";
  version = "2ffb9c389bc85884c4dbbbdbdf328d9b09b027e9";
  src = fetchFromGitHub {
    owner = "slothy-optimizer";
    repo = "slothy";
    rev = version;
    sha256 = "sha256-7KWTJ6/pSva/2ODhrYS9WAhPZr9Q8maKd7959BzwM3g=";
  };

  nativeBuildInputs = [ pkgs.makeWrapper ];
  dontConfigure = true;

  installPhase = ''
    mkdir -p $out/bin
    cp slothy-cli $out/bin/
    cp -r slothy $out/bin
    wrapProgram $out/bin/slothy-cli \
            --set DYLD_LIBRARY_PATH ${pythonEnv}/lib \
            --set PYTHONPATH ${pythonEnv}/bin \
            --run exec
  '';

  dontStrip = true;
  noAuditTmpdir = true;
  propagatedBuildInputs = [ pythonEnv llvm gcc ];

  meta = {
    description = "Slothy: assembly-level superoptimizer";
    homepage = "https://slothy-optimizer.github.io/slothy/";
  };
}
