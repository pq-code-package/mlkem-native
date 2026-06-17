# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, gcc-arm-embedded
, riscv32-toolchain
, writeText
}:

# Board-agnostic Zephyr build environment: a pinned Zephyr tree plus the
# modules needed by the boards we target, exposed via a setup hook so a plain
# `cmake` build works with no west workspace. CMSIS-6 covers the Cortex-M
# boards and hal_rpi_pico covers the Raspberry Pi RP2350 (rpi_pico2) boards;
# add further modules here as more boards are wired up.
let
  zephyr = fetchFromGitHub {
    owner = "zephyrproject-rtos";
    repo = "zephyr";
    rev = "v4.4.1";
    hash = "sha256-8bzykJs6fFGiofCxRKh8M9jdXr5R8FM0lAbA28yanGk=";
  };

  # Revisions pinned by the Zephyr v4.4.1 manifest (west.yml).
  cmsis_6 = fetchFromGitHub {
    owner = "zephyrproject-rtos";
    repo = "CMSIS_6";
    rev = "30a859f44ef8ab4dc8f84b03ed586fd16ccf9d74";
    hash = "sha256-nTehISN0pu9gnOZMpGaBQ3DFmNxAqAZPGpvbKfEM35o=";
  };

  # HAL for the Raspberry Pi RP2040/RP2350 SoCs (bundles the pico-sdk sources).
  # The in-tree $ZEPHYR_BASE/modules/hal_rpi_pico glue (cmake-ext/kconfig-ext)
  # picks this up once it is listed in ZEPHYR_MODULES, satisfying the
  # HAS_RPI_PICO / PICOSDK_USE_* symbols selected by the rpi_pico2 boards.
  hal_rpi_pico = fetchFromGitHub {
    owner = "zephyrproject-rtos";
    repo = "hal_rpi_pico";
    rev = "562b41e10a1d8b1a761b253b107c5c6a84cf4535";
    hash = "sha256-18sQa1+Gc9zKhB95b59TvRsgbuGL2U7MfRu0QcqPBo0=";
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
    ln -s ${hal_rpi_pico} $out/hal_rpi_pico
    ln -s ${riscv32-toolchain} $out/riscv32-toolchain
  '';

  setupHook = writeText "setup-hook.sh" ''
    export ZEPHYR_BASE="$1/zephyr"
    export ZEPHYR_MODULES="$1/cmsis_6;$1/hal_rpi_pico"

    # Default toolchain: arm-none-eabi for the Cortex-M boards. RISC-V targets
    # (rpi_pico2 hazard3) instead pass -DZEPHYR_TOOLCHAIN_VARIANT=cross-compile
    # and -DCROSS_COMPILE=$MLK_ZEPHYR_RISCV32_CROSS_COMPILE to CMake; see
    # test/zephyr/platform.mk.
    export ZEPHYR_TOOLCHAIN_VARIANT=gnuarmemb
    export GNUARMEMB_TOOLCHAIN_PATH=${gcc-arm-embedded}

    # Bare-metal rv32imac/ilp32 (soft-float) GCC for the Hazard3 cores.
    export MLK_ZEPHYR_RISCV32_CROSS_COMPILE="$1/riscv32-toolchain/bin/riscv32-none-elf-"
  '';

  meta = {
    description = "Pinned Zephyr tree and modules for the Zephyr-based test flows";
    homepage = "https://www.zephyrproject.org/";
  };
}
