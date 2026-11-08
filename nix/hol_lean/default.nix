# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ lib
, stdenv
, fetchFromGitHub
, lean4
}:

stdenv.mkDerivation (finalAttrs: {
  pname = "hol-lean-holtrace";
  version = "0.1.0-unstable";

  src = fetchFromGitHub {
    owner = "hol-light-family";
    repo = "HolLean";
    rev = "91dff2cac719d0de458b73e1b88202f6fa59fbfd";
    hash = "sha256-Aq20XlPPT0oGi+8BimxVsmt1DM5sZL7UesgRQwyEPUg=";
  };

  nativeBuildInputs = [ lean4 ];

  dontConfigure = true;

  buildPhase = ''
    runHook preBuild
    lake build holtrace
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -Dm755 .lake/build/bin/holtrace "$out/bin/holtrace"
    runHook postInstall
  '';

  meta = {
    description = "HOLTrace replay through HolLean's HOL Light kernel";
    homepage = "https://github.com/hol-light-family/HolLean";
    license = lib.licenses.bsd3;
    mainProgram = "holtrace";
  };
})
