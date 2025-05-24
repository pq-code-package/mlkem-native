# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, python3
, pkgs
, llvm
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
  version = "5fafd8048c3ba7c5924cbd2e16e77040fa847447";

  src = fetchFromGitHub {
    owner = "slothy-optimizer";
    repo = "slothy";
    rev = version;
    sha256 = "sha256-3X8Z4Wgb+sGrDYTffBrG4hF3UAIVwab60XMiijtZlIY";
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
  propagatedBuildInputs = [ pythonEnv llvm ];

  meta = {
    description = "Slothy: assembly-level superoptimizer";
    homepage = "https://slothy-optimizer.github.io/slothy/";
  };
}
