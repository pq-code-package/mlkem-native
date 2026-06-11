# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, writeText
}:
# Construct a minimal STM32CubeN6-based platform environment for building
# nucleo-n657x0-q benchmarks. The package copies only the required Cube headers
# and sources, then patches selected files where needed to get the intended
# RAM-loaded benchmark behavior.
stdenvNoCC.mkDerivation {
  pname = "mlkem-native-nucleo-n657x0-q";
  version = "main";

  src = fetchFromGitHub {
    owner = "STMicroelectronics";
    repo = "STM32CubeN6";
    rev = "1fc803683e03b0ce78e64523441d31acd0db2829";
    hash = "sha256-7iD7R3A+0YAfMZqKndWBq+z5TUY37XDVxFy5HK8/5Aw=";
    fetchSubmodules = true;
  };

  dontBuild = true;

  installPhase = ''
    set -eu

    outp="$out/platform/nucleo-n657x0-q/src/platform"
    fsbl_tpl="Projects/NUCLEO-N657X0-Q/Templates/Template_FSBL_LRUN"
    hal="Drivers/STM32N6xx_HAL_Driver"
    cmsis_core="Drivers/CMSIS/Core/Include"
    cmsis_device="Drivers/CMSIS/Device/ST/STM32N6xx/Include"

    install_file() {
      src_file="$1"
      dst_file="$outp/$2"
      mkdir -p "$(dirname "$dst_file")"
      cp "$src_file" "$dst_file"
    }

    # CMSIS headers reached by stm32n657xx.h/core_cm55.h under the GCC build.
    for header in \
      cmsis_compiler.h \
      cmsis_gcc.h \
      cmsis_version.h \
      core_cm55.h \
      m-profile/armv7m_cachel1.h \
      m-profile/armv8m_mpu.h \
      m-profile/armv8m_pmu.h \
      m-profile/cmsis_gcc_m.h
    do
      install_file "$cmsis_core/$header" "Drivers/CMSIS/Core/Include/$header"
    done

    for header in \
      stm32n6xx.h \
      stm32n657xx.h \
      system_stm32n6xx.h
    do
      install_file "$cmsis_device/$header" "Drivers/CMSIS/Device/ST/STM32N6xx/Include/$header"
    done

    # FSBL files used by platform.mk.
    install_file \
      "$fsbl_tpl/STM32CubeIDE/Boot/Startup/startup_stm32n657xx_fsbl.s" \
      "gcc/startup_stm32n657xx.S"

    # Use the linker-provided stack top instead of Cube's fixed SRAM stack.
    sed -i.bak -E 's@[.]word[[:space:]]+0x34110000@.word _estack@' \
      "$outp/gcc/startup_stm32n657xx.S"

    # Mask interrupts as soon as Reset_Handler starts to avoid stale debug/board
    # state firing before this RAM-loaded test image initializes C runtime state.
    sed -i.bak -E '/^Reset_Handler:/a\  cpsid i' \
      "$outp/gcc/startup_stm32n657xx.S"
    rm -f "$outp/gcc/startup_stm32n657xx.S.bak"

    install_file "$fsbl_tpl/FSBL/Src/system_stm32n6xx_fsbl.c" "system_stm32n6xx.c"
    install_file "$fsbl_tpl/FSBL/Src/stm32n6xx_it.c" "stm32n6xx_it.c"
    install_file "$fsbl_tpl/FSBL/Inc/stm32n6xx_it.h" "Inc/stm32n6xx_it.h"
    install_file "$fsbl_tpl/FSBL/Inc/main.h" "Inc/main.h"
    install_file "$fsbl_tpl/FSBL/Inc/stm32n6xx_hal_conf.h" "Inc/stm32n6xx_hal_conf.h"

    conf="$outp/Inc/stm32n6xx_hal_conf.h"

    # Disable BSEC because the platform test build does not link the BSEC HAL.
    sed -i.bak -E 's@^[[:space:]]*#[[:space:]]*define[[:space:]]+HAL_BSEC_MODULE_ENABLED@/* #define HAL_BSEC_MODULE_ENABLED */@' "$conf"

    # Disable XSPI because only the extracted clock setup is used, not Cube's
    # external memory setup or XSPI HAL driver.
    sed -i.bak -E 's@^[[:space:]]*#[[:space:]]*define[[:space:]]+HAL_XSPI_MODULE_ENABLED@/* #define HAL_XSPI_MODULE_ENABLED */@' "$conf"
    rm -f "$conf.bak"

    # HAL files named directly by platform.mk, plus headers enabled by the
    # pruned FSBL HAL config and their direct dependencies.
    for header in \
      Legacy/stm32_hal_legacy.h \
      stm32n6xx_hal.h \
      stm32n6xx_hal_cortex.h \
      stm32n6xx_hal_def.h \
      stm32n6xx_hal_dma.h \
      stm32n6xx_hal_dma_ex.h \
      stm32n6xx_hal_exti.h \
      stm32n6xx_hal_gpio.h \
      stm32n6xx_hal_gpio_ex.h \
      stm32n6xx_hal_pwr.h \
      stm32n6xx_hal_pwr_ex.h \
      stm32n6xx_hal_rcc.h \
      stm32n6xx_hal_rcc_ex.h \
      stm32n6xx_ll_bus.h \
      stm32n6xx_ll_rcc.h
    do
      install_file "$hal/Inc/$header" "Drivers/STM32N6xx_HAL_Driver/Inc/$header"
    done

    for source in \
      stm32n6xx_hal.c \
      stm32n6xx_hal_cortex.c \
      stm32n6xx_hal_pwr.c \
      stm32n6xx_hal_pwr_ex.c \
      stm32n6xx_hal_rcc.c \
      stm32n6xx_hal_rcc_ex.c
    do
      install_file "$hal/Src/$source" "Drivers/STM32N6xx_HAL_Driver/Src/$source"
    done

    fsbl_main_c="$fsbl_tpl/FSBL/Src/main.c"
    clock_out="$outp/clock_config.c"
    tmpclk="$TMPDIR/clock_config.$$.$RANDOM.c"
    : > "$tmpclk"

    # Preserve the Cube file header in the generated standalone clock source.
    awk '
      /\/\* USER CODE BEGIN Header \*\// { print; inhdr=1; next }
      inhdr { print }
      /\/\* USER CODE END Header \*\// { inhdr=0 }
    ' "$fsbl_main_c" >> "$tmpclk"
    printf "\n#include \"main.h\"\n\n" >> "$tmpclk"

    # Keep Cube's clock-tree explanatory comment next to SystemClock_Config.
    awk '
      /\/\* USER CODE BEGIN CLK 1 \*\// { print; inclk=1; next }
      inclk { print }
      /\/\* USER CODE END CLK 1 \*\// { inclk=0 }
    ' "$fsbl_main_c" >> "$tmpclk"
    printf "\n" >> "$tmpclk"

    # Extract exactly the SystemClock_Config function body from the FSBL main.c
    # into the generated clock_config.c, tracking braces so that file does not
    # pull in unused FSBL code.
    awk '
      BEGIN { copy=0; lvl=0; sig=0 }
      /^[ \t]*void[ \t]+SystemClock_Config[ \t]*\([ \t]*void[ \t]*\)[ \t]*\{/ {
        print; copy=1; lvl=1; next
      }
      /^[ \t]*void[ \t]+SystemClock_Config[ \t]*\([ \t]*void[ \t]*\)[ \t]*$/ {
        print; copy=1; sig=1; next
      }
      copy {
        if (sig && $0 !~ /\{/) { print; next }
        nopen=gsub(/{/,"{")
        nclose=gsub(/}/,"}")
        lvl += nopen - nclose
        print
        sig=0
        if (lvl<=0) exit
      }
    ' "$fsbl_main_c" >> "$tmpclk"
    grep -q "SystemClock_Config" "$tmpclk"
    mv "$tmpclk" "$clock_out"

    # The standalone clock_config.c calls SystemClock_Config, so make sure the
    # copied FSBL main.h exposes the declaration expected by local platform code.
    if ! grep -q "void[[:space:]]\+SystemClock_Config[[:space:]]*([[:space:]]*void[[:space:]]*)" "$outp/Inc/main.h"; then
      printf "\nvoid SystemClock_Config(void);\n" >> "$outp/Inc/main.h"
    fi

    # SystemClock_Config calls Error_Handler on HAL failures; the implementation
    # is provided by the platform test sources, but main.h must declare it.
    if ! grep -q "void[[:space:]]\+Error_Handler[[:space:]]*([[:space:]]*void[[:space:]]*)" "$outp/Inc/main.h"; then
      printf "void Error_Handler(void);\n" >> "$outp/Inc/main.h"
    fi
  '';

  setupHook = writeText "setup-hook.sh" ''
    export NUCLEO_N657X0_Q_PATH="$1/platform/nucleo-n657x0-q/src/platform/"
  '';

  meta = {
    description = "Platform files for STM32 NUCLEO-N657X0-Q RAM-only OpenOCD tests";
    homepage = "https://github.com/STMicroelectronics/STM32CubeN6";
  };
}
