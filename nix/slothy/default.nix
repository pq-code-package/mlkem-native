# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, python312
, pkgs
, python312Packages
, fetchPypi
, stdenv
, cmake
, pkg-config
, llvm
, gcc
}:


let

  # I have experimented with the ortools (9.12) that is packaged in nixpkgs.
  # However, it results in _much_ poorer SLOTHY performance and, we hence,
  # instead stick to the pre-built ones from pypi.
  ortools912 = python312Packages.buildPythonPackage rec {
    pname = "ortools";
    version = "9.12.4544";

    format = "wheel";

    src = fetchPypi {
      inherit pname version;
      format = "wheel";
      dist = "cp312";
      python = "cp312";
      abi = "cp312";
      platform =
        if stdenv.isDarwin then
          if stdenv.isAarch64 then "macosx_11_0_arm64"
          else "macosx_10_15_x86_64"
        else if stdenv.isLinux then
          if stdenv.isAarch64 then "manylinux_2_27_aarch64.manylinux_2_28_aarch64"
          else "manylinux_2_27_x86_64.manylinux_2_28_x86_64"
        else throw "Unsupported platform";

      hash =
        if stdenv.isDarwin then
          if stdenv.isAarch64 then "sha256-Z/4bhlMndFZ4okBm2CbbJaEBmqIH6pAXygGvLPIUVlI="
          else "sha256-FnaLGfyzBT9EvYTEYMuXjyop1046XZugYSNYn+sQrxI="
        else if stdenv.isLinux then
          if stdenv.isAarch64 then "sha256-VVD+nuVSt7jtAcrZHVimjsDkjNQN0necELGZFCmncFg="
          else "sha256-kiEh1vSPjuseuIqMZF/wC2H2CFYxkxTOK48iD6uJYIM="
        else throw "Unsupported platform";
    };

    propagatedBuildInputs = with python312Packages; [
      numpy
      pandas
      protobuf
    ];

  };

  pythonEnv = python312.withPackages (ps: with ps; [
    ortools912
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
  propagatedBuildInputs = [ pythonEnv llvm gcc ];

  meta = {
    description = "Slothy: assembly-level superoptimizer";
    homepage = "https://slothy-optimizer.github.io/slothy/";
  };
}
