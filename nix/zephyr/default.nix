# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, gcc-arm-embedded
, writeText
}:

# Board-agnostic Zephyr build environment: a pinned Zephyr tree plus the
# modules needed by the boards we target, exposed via a setup hook so a plain
# `cmake` build works with no west workspace.
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

  # Revision pinned by the Zephyr v4.4.1 manifest (west.yml).
  hal_stm32 = fetchFromGitHub {
    owner = "zephyrproject-rtos";
    repo = "hal_stm32";
    rev = "fc11896dd39cfca37bf9b4aeaaa2df8861b81875";
    hash = "sha256-AtNq2yTZsTFMTlWn/Ns0wuEiN4Wv/OTV2vWPRu0SnOE=";
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
    ln -s ${hal_stm32} $out/hal_stm32
  '';

  setupHook = writeText "setup-hook.sh" ''
    export ZEPHYR_BASE="$1/zephyr"
    export ZEPHYR_CMSIS_6_MODULE="$1/cmsis_6"
    export ZEPHYR_HAL_STM32_MODULE="$1/hal_stm32"
    export ZEPHYR_MODULES="$1/cmsis_6;$1/hal_stm32"
    export ZEPHYR_TOOLCHAIN_VARIANT=gnuarmemb
    export GNUARMEMB_TOOLCHAIN_PATH=${gcc-arm-embedded}
  '';

  meta = {
    description = "Pinned Zephyr tree and modules for the Zephyr-based test flows";
    homepage = "https://www.zephyrproject.org/";
  };
}
