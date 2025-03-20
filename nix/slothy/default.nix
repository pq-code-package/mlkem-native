# SPDX-License-Identifier: Apache-2.0

{ stdenvNoCC
, fetchFromGitHub
, python311
, pkgs
, callPackage
, python311Packages
, fetchPypi
, stdenv
, cmake
, pkg-config
, llvm
, gcc
}:


let
  ortools97 = python311Packages.buildPythonPackage rec {
    pname = "ortools";
    version = "9.7.2996";

    format = "wheel";

    src = fetchPypi {
      inherit pname version;
      format = "wheel";
      dist = "cp311";
      python = "cp311";
      abi = "cp311";
      platform =
        if stdenv.isDarwin then
          if stdenv.isAarch64 then "macosx_11_0_arm64"
          else "macosx_10_15_x86_64"
        else if stdenv.isLinux then
          if stdenv.isAarch64 then "manylinux_2_17_aarch64.manylinux2014_aarch64"
          else "manylinux_2_17_x86_64.manylinux2014_x86_64"
        else throw "Unsupported platform";

      hash =
        if stdenv.isDarwin then
          if stdenv.isAarch64 then "sha256-Oc8xz9iRuOiDyZBc85qlS57u0efP/f4cDpi2k9ZlCQI="
          else "sha256-0ax/I7604BumV+VRV7Y5fNDs0XrxkK+ocr9yU1oFMDQ="
        else if stdenv.isLinux then
          if stdenv.isAarch64 then "sha256-B8QfDoYT2OxrpoUzSQTNduRbxG2j1S8XPpMBZo/yI90="
          else "sha256-pUerlb2cykE9cYraz68MnuBKDM4V1Du0Ta3yve16K/o="
        else throw "Unsupported platform";
    };

    propagatedBuildInputs = with python311Packages; [
      numpy
      pandas
      protobuf
    ];

  };

  unicorn_2_1_3 = python311Packages.buildPythonPackage rec {
    pname = "unicorn";
    version = "2.1.3";

    propagatedBuildInputs = [
      python311Packages.setuptools
    ];

    build-system = with python311Packages; [
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

  pythonEnv = python311.withPackages (ps: with ps; [
    ortools97
    sympy
    unicorn_2_1_3
  ]);

in
stdenvNoCC.mkDerivation rec {
  pname = "slothy-cli";
  version = "9416181b5bbb61992dc1928116e84eead100838e";

  src = fetchFromGitHub {
    owner = "slothy-optimizer";
    repo = "slothy";
    rev = version;
    sha256 = "sha256-zmF2+9oUM5J8PzvyEA5lN1o4aucOqP4Db4x+H2MO4vI=";
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
