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
  # TODO: switch to protobuf from nixpkgs
  # ortools 9.12 requires protobuf >= 5.29.3 - currently nixpkgs 24.11 has
  # protobuf 5.28.3
  protobuf_6_30_1 = python312Packages.buildPythonPackage rec {
    pname = "protobuf";
    version = "5.29.3";

    propagatedBuildInputs = [
      python312Packages.setuptools
    ];

    build-system = with python312Packages; [
      setuptools
    ];

    dontConfigure = true;
    nativeBuildInputs =
      [
        cmake
        pkg-config
      ];

    src = fetchPypi {
      inherit pname version;
      hash = "sha256-XaD0HtrxF73jFkBLrRpIbLTt7fjkpUiRKW9kjo4HZiA=";
    };
  };


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
      protobuf_6_30_1
    ];

  };

  # TODO: switch to unicorn from nixpkgs
  # nixpkgs 24.11 currently has 2.1.1 - we are experiencing some issues with
  # that version on MacOS. 2.1.2/2.1.3 (and also some older versions) don't
  # have that problem
  unicorn_2_1_3 = python312Packages.buildPythonPackage rec {
    pname = "unicorn";
    version = "2.1.3";

    propagatedBuildInputs = [
      python312Packages.setuptools
    ];

    build-system = with python312Packages; [
      setuptools
    ];

    dontConfigure = true;
    nativeBuildInputs =
      [
        cmake
        pkg-config
      ];

    src = fetchPypi {
      inherit pname version;
      hash = "sha256-DAZFbPVQwijyADzHA2avpK7OLm5+TDLY9LIscXumtyk=";
    };
  };

  pythonEnv = python312.withPackages (ps: with ps; [
    ortools912
    sympy
    unicorn_2_1_3
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
