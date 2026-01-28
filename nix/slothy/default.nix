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
  version = "0.1.10";
  src = fetchFromGitHub {
    owner = "slothy-optimizer";
    repo = "slothy";
    rev = version;
    sha256 = "sha256-zGZEH+lixwVeH+f03pC6etO2xCF1vRH/RnmyYaKf4kI=";
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
