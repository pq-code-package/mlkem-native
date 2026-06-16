# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, gcc-arm-embedded
, writeText
}:

# Board-agnostic Zephyr build environment: a pinned Zephyr tree plus the
# modules needed by the boards we target, exposed via a setup hook so a plain
# `cmake` build works with no west workspace. CMSIS-6 covers the Cortex-M
# boards; add further modules here as more boards are wired up.
let
  zephyr = fetchFromGitHub {
    owner = "zephyrproject-rtos";
    repo = "zephyr";
    rev = "v4.4.1";
    hash = "sha256-8bzykJs6fFGiofCxRKh8M9jdXr5R8FM0lAbA28yanGk=";
  };

  # Revision pinned by the Zephyr v4.4.1 manifest (west.yml).
  cmsis_6 = fetchFromGitHub {
    owner = "zephyrproject-rtos";
    repo = "CMSIS_6";
    rev = "30a859f44ef8ab4dc8f84b03ed586fd16ccf9d74";
    hash = "sha256-nTehISN0pu9gnOZMpGaBQ3DFmNxAqAZPGpvbKfEM35o=";
  };
in
stdenvNoCC.mkDerivation {
  pname = "mlkem-native-zephyr";
  version = "4.4.1";

  dontUnpack = true;

  installPhase = ''
    mkdir -p $out
    ln -s ${zephyr} $out/zephyr
    ln -s ${cmsis_6} $out/cmsis_6
  '';

  setupHook = writeText "setup-hook.sh" ''
    export ZEPHYR_BASE="$1/zephyr"
    export ZEPHYR_MODULES="$1/cmsis_6"
    export ZEPHYR_TOOLCHAIN_VARIANT=gnuarmemb
    export GNUARMEMB_TOOLCHAIN_PATH=${gcc-arm-embedded}
  '';

  meta = {
    description = "Pinned Zephyr tree and modules for the Zephyr-based test flows";
    homepage = "https://www.zephyrproject.org/";
  };
}
