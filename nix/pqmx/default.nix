# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, writeText
}:

stdenvNoCC.mkDerivation {
  pname = "mlkem-native-pqmx";
  version = "main-2026-02-25";


  # Fetch platform files from pqmx
  src = fetchFromGitHub {
    owner = "slothy-optimizer";
    repo = "pqmx";
    rev = "526abcbccd022f0c384e70c7d00f2b36cd2199ab";
    hash = "sha256-BjsToEWGlykKIKRfPom84BkD5RfetUKKwRAw3PecebU=";
  };

  dontBuild = true;

  installPhase = ''
    mkdir -p $out/platform/m33-an524/src/platform/
    cp -r envs/m33-an524/src/platform/. $out/platform/m33-an524/src/platform/
    cp integration/*.c $out/platform/m33-an524/src/platform/

    mkdir -p $out/platform/m55-an547/src/platform/
    cp -r envs/m55-an547/src/platform/. $out/platform/m55-an547/src/platform/
    cp integration/*.c $out/platform/m55-an547/src/platform/
  '';

  setupHook = writeText "setup-hook.sh" ''
    export M33_AN524_PATH="$1/platform/m33-an524/src/platform/"
    export M55_AN547_PATH="$1/platform/m55-an547/src/platform/"
  '';

  meta = {
    description = "Platform files from pqmx for baremetal targets";
    homepage = "https://github.com/slothy-optimizer/pqmx";
  };
}
