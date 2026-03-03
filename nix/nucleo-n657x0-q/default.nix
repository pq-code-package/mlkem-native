# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, writeText
}:
stdenvNoCC.mkDerivation {
  pname = "mlkem-native-nucleo-n657x0-q";
  version = "main";

  # Fetch STM32CubeN6 (Template + CMSIS headers)
  # TODO(GAP): Pin rev + hash for reproducibility.
  src = fetchFromGitHub {
    owner = "STMicroelectronics";
    repo = "STM32CubeN6";
    rev = "1fc803683e03b0ce78e64523441d31acd0db2829";
    hash = "sha256-7iD7R3A+0YAfMZqKndWBq+z5TUY37XDVxFy5HK8/5Aw=";
    fetchSubmodules = true;
  };

  dontBuild = true;

  propagatedBuildInputs = [ ];

  installPhase = ''
    set -eu

    outp="$out/platform/nucleo-n657x0-q/src/platform"
    mkdir -p "$outp"

    tpl="Projects/NUCLEO-N657X0-Q/Templates/Template"

    if [ ! -d "$tpl" ]; then
      echo "ERROR: expected Cube template at $tpl"
      exit 1
    fi

    # Copy CMSIS headers needed by system/startup from the Cube tree
    mkdir -p "$outp/Drivers/CMSIS/Core"
    mkdir -p "$outp/Drivers/CMSIS/Device"

    cp -r "Drivers/CMSIS/Core/Include" "$outp/Drivers/CMSIS/Core/"
    # Ensure m-profile subdir (pmu_armv8.h) is present, as some builds include it directly
    if [ -d "Drivers/CMSIS/Core/Include/m-profile" ]; then
      mkdir -p "$outp/Drivers/CMSIS/Core/Include"
      cp -r "Drivers/CMSIS/Core/Include/m-profile" "$outp/Drivers/CMSIS/Core/Include/" || true
    fi
    cp -r "Drivers/CMSIS/Device/ST"     "$outp/Drivers/CMSIS/Device/"

    # Copy startup + system + linker script
    # Prefer board-specific FSBL-LRUN files explicitly when available.
    fsbl_tpl="Projects/NUCLEO-N657X0-Q/Templates/Template_FSBL_LRUN"
    mkdir -p "$outp/gcc" "$outp/gcc/linker"
    if [ -d "$fsbl_tpl" ]; then
      # Explicitly select:
      #  - Startup: STM32CubeIDE/Boot/Startup/startup_stm32n657xx_fsbl.s
      #  - Linker:  STM32CubeIDE/AppS/STM32N657XX_LRUN.ld
      #  - System:  FSBL/Src/system_stm32n6xx_fsbl.c
      #  - IT/MSP:  FSBL/Src/stm32n6xx_it.c, stm32n6xx_hal_msp.c
      start_src="$fsbl_tpl/STM32CubeIDE/Boot/Startup/startup_stm32n657xx_fsbl.s"
      ld_src="$fsbl_tpl/STM32CubeIDE/AppS/STM32N657XX_LRUN.ld"
      sys_src="$fsbl_tpl/FSBL/Src/system_stm32n6xx_fsbl.c"
      it_src="$fsbl_tpl/FSBL/Src/stm32n6xx_it.c"
      msp_src="$fsbl_tpl/FSBL/Src/stm32n6xx_hal_msp.c"
      if [ -f "$start_src" ]; then
        # Normalize to canonical name searched by platform.mk
        cp -v "$start_src" "$outp/gcc/startup_stm32n657xx.S"
      fi
      if [ -f "$ld_src" ]; then
        cp -v "$ld_src" "$outp/gcc/linker/STM32N657XX_LRUN.ld"
      fi
      if [ -f "$sys_src" ]; then
        cp -v "$sys_src" "$outp/system_stm32n6xx.c"
      fi
      if [ -f "$it_src" ]; then
        cp -v "$it_src" "$outp/"
      fi
      if [ -f "$msp_src" ]; then
        cp -v "$msp_src" "$outp/"
      fi
    else
      # Generic fallback to CMSIS templates if FSBL files are not located
      cp -r Drivers/CMSIS/Device/ST/STM32N6xx/Source/Templates/* "$outp" || true
      cp -r Drivers/CMSIS/Device/ST/STM32N6xx/Source/Templates/gcc/* "$outp/gcc/" || true
    fi

    # Copy HAL driver includes and sources so FSBL files build if they reference HAL symbols
    mkdir -p "$outp/Drivers/STM32N6xx_HAL_Driver"
    if [ -d Drivers/STM32N6xx_HAL_Driver/Inc ]; then
      cp -r Drivers/STM32N6xx_HAL_Driver/Inc "$outp/Drivers/STM32N6xx_HAL_Driver/" || true
    fi
    if [ -d Drivers/STM32N6xx_HAL_Driver/Src ]; then
      cp -r Drivers/STM32N6xx_HAL_Driver/Src "$outp/Drivers/STM32N6xx_HAL_Driver/" || true
    fi
    # Guarantee HAL Driver Src exists under output (fallback search if not found in expected path)
    if [ ! -d "$outp/Drivers/STM32N6xx_HAL_Driver/Src" ]; then
      alt_hal_dir=$(find Drivers -type d -name 'STM32N6xx_HAL_Driver' -print -quit || true)
      if [ -n "$alt_hal_dir" ] && [ -d "$alt_hal_dir/Src" ]; then
        echo "Copying HAL Driver Src from $alt_hal_dir"
        mkdir -p "$outp/Drivers/STM32N6xx_HAL_Driver"
        cp -r "$alt_hal_dir/Src" "$outp/Drivers/STM32N6xx_HAL_Driver/" || true
      fi
    fi


    # Copy HAL configuration header, preferring FSBL-LRUN Inc; then disable BSEC and XSPI modules
    fsbl_inc_conf="$fsbl_tpl/FSBL/Inc/stm32n6xx_hal_conf.h"
    if [ -f "$fsbl_inc_conf" ]; then
      mkdir -p "$outp/Inc"
      cp -v "$fsbl_inc_conf" "$outp/Inc/stm32n6xx_hal_conf.h"
      # Also provide FSBL interrupt header in include path if present
      fsbl_it_hdr="$fsbl_tpl/FSBL/Inc/stm32n6xx_it.h"
      if [ -f "$fsbl_it_hdr" ]; then
        cp -v "$fsbl_it_hdr" "$outp/Inc/stm32n6xx_it.h"
      fi
      # Also provide FSBL main.h in include path if present
      fsbl_main_hdr="$fsbl_tpl/FSBL/Inc/main.h"
      if [ -f "$fsbl_main_hdr" ]; then
        cp -v "$fsbl_main_hdr" "$outp/Inc/main.h"
      fi
    else
      # Fallback: Copy the first hal_conf found under Projects
      hal_conf=$(find Projects -type f -name 'stm32n6xx_hal_conf.h' | head -n1 || true)
      if [ -n "$hal_conf" ]; then
        incdir=$(dirname "$hal_conf")
        cp -r "$incdir" "$outp/Inc"
        # Attempt to locate an stm32n6xx_it.h nearby if FSBL header not used
        it_hdr=$(find "$(dirname "$incdir")" -name 'stm32n6xx_it.h' -type f | head -n1 || true)
        if [ -n "$it_hdr" ] && [ ! -f "$outp/Inc/stm32n6xx_it.h" ]; then
          cp -v "$it_hdr" "$outp/Inc/stm32n6xx_it.h"
        fi
        # Attempt to locate a main.h nearby if FSBL header not used
        main_hdr=$(find "$(dirname "$incdir")" -name 'main.h' -type f | head -n1 || true)
        if [ -n "$main_hdr" ] && [ ! -f "$outp/Inc/main.h" ]; then
          cp -v "$main_hdr" "$outp/Inc/main.h"
        fi
      fi
    fi

    # Ensure BSEC and XSPI are disabled for our test build
    conf="$outp/Inc/stm32n6xx_hal_conf.h"
    if [ -f "$conf" ]; then
      # Comment out any explicit enable lines
      sed -i.bak -E 's@^\s*#\s*define\s+HAL_BSEC_MODULE_ENABLED@/* #define HAL_BSEC_MODULE_ENABLED */@' "$conf" || true
      sed -i.bak -E 's@^\s*#\s*define\s+HAL_XSPI_MODULE_ENABLED@/* #define HAL_XSPI_MODULE_ENABLED */@' "$conf" || true
      # Also handle commented-but-enabled variants
      sed -i.bak -E 's@^\s*//\s*#\s*define\s+HAL_BSEC_MODULE_ENABLED@/* #define HAL_BSEC_MODULE_ENABLED */@' "$conf" || true
      sed -i.bak -E 's@^\s*//\s*#\s*define\s+HAL_XSPI_MODULE_ENABLED@/* #define HAL_XSPI_MODULE_ENABLED */@' "$conf" || true
      sed -i.bak -E 's@^\s*/\*\s*#\s*define\s+HAL_BSEC_MODULE_ENABLED\s*\*/@/* #define HAL_BSEC_MODULE_ENABLED */@' "$conf" || true
      sed -i.bak -E 's@^\s*/\*\s*#\s*define\s+HAL_XSPI_MODULE_ENABLED\s*\*/@/* #define HAL_XSPI_MODULE_ENABLED */@' "$conf" || true
      # Belt-and-suspenders: append explicit undefs to override any includes afterward
      printf "\n#undef HAL_BSEC_MODULE_ENABLED\n#undef HAL_XSPI_MODULE_ENABLED\n" >> "$conf"
    fi

    # Extract SystemClock_Config and related user clock snippets from FSBL template into a standalone clock_config.c
    fsbl_main_c="$fsbl_tpl/FSBL/Src/main.c"
    clock_out="$outp/clock_config.c"
    if [ -f "$fsbl_main_c" ]; then
      echo "Generating clock_config.c from $fsbl_main_c"
      tmpclk="$TMPDIR/clock_config.$$.$RANDOM.c"
      : > "$tmpclk"
      # 1) Header block
      awk '
        /\/\* USER CODE BEGIN Header \*\// { print; inhdr=1; next }
        inhdr { print }
        /\/\* USER CODE END Header \*\// { print; inhdr=0 }
      ' "$fsbl_main_c" >> "$tmpclk"
      # 2) Includes lines
      printf "\n/* Includes ------------------------------------------------------------------*/\n" >> "$tmpclk"
      printf "#include \"main.h\"\n\n" >> "$tmpclk"
      # 3) USER CLK 1 block
      awk '
        /\/\* USER CODE BEGIN CLK 1 \*\// { print; inclk=1; next }
        inclk { print }
        /\/\* USER CODE END CLK 1 \*\// { print; inclk=0 }
      ' "$fsbl_main_c" >> "$tmpclk"
      printf "\n" >> "$tmpclk"
      # 4) SystemClock_Config (try to include preceding comment header if present)
      awk '
        BEGIN { copy=0; lvl=0; sig=0 }
        # Signature with brace on same line
        /^[ \t]*void[ \t]+SystemClock_Config[ \t]*\([ \t]*void[ \t]*\)[ \t]*\{/ {
          print; copy=1; lvl=1; next
        }
        # Signature line without brace; start copying and wait for opening brace
        /^[ \t]*void[ \t]+SystemClock_Config[ \t]*\([ \t]*void[ \t]*\)[ \t]*$/ {
          print; copy=1; sig=1; next
        }
        copy {
          if (sig) {
            # Print until we see the first brace; then start level tracking
            if ($0 ~ /\{/) {
              nopen=gsub(/{/,"{"); nclose=gsub(/}/,"}"); lvl += nopen - nclose; print; sig=0;
              if (lvl<=0) exit; next
            }
            print; next
          }
          nopen=gsub(/{/,"{"); nclose=gsub(/}/,"}"); lvl += nopen - nclose; print;
          if (lvl<=0) exit
        }
      ' "$fsbl_main_c" >> "$tmpclk"
      # Sanity check: ensure we captured the function signature
      if ! grep -q "SystemClock_Config" "$tmpclk"; then
        echo "ERROR: Failed to extract SystemClock_Config from $fsbl_main_c" >&2
        exit 1
      fi
      mv "$tmpclk" "$clock_out"
      # Ensure main.h exists and declares needed prototypes
      mkdir -p "$outp/Inc"
      fsbl_main_h="$fsbl_tpl/FSBL/Inc/main.h"
      dest_main_h="$outp/Inc/main.h"
      if [ ! -f "$dest_main_h" ] && [ -f "$fsbl_main_h" ]; then
        cp -v "$fsbl_main_h" "$dest_main_h"
      fi
      if [ -f "$dest_main_h" ]; then
        if ! grep -q "void[[:space:]]\+SystemClock_Config[[:space:]]*([[:space:]]*void[[:space:]]*)" "$dest_main_h"; then
          printf "\n#ifdef __cplusplus\nextern \"C\" {\n#endif\n" >> "$dest_main_h"
          printf "void SystemClock_Config(void);\n" >> "$dest_main_h"
          printf "#ifdef __cplusplus\n}\n#endif\n" >> "$dest_main_h"
        fi
        if ! grep -q "void[[:space:]]\+Error_Handler[[:space:]]*([[:space:]]*void[[:space:]]*)" "$dest_main_h"; then
          printf "void Error_Handler(void);\n" >> "$dest_main_h"
        fi
      fi
    else
      echo "WARNING: FSBL main.c not found at $fsbl_main_c; skipping clock_config generation" >&2
    fi

    # Patch linker script to increase stack to 128 KiB (0x20000) for test workloads
    # Locate STM32N657XX_LRUN.ld under gcc/ or gcc/linker/
    ldpath=""
    for cand in \
      "$outp/gcc/linker/STM32N657XX_LRUN.ld" \
      "$outp/gcc/STM32N657XX_LRUN.ld" \
      $(find "$outp" -type f -name STM32N657XX_LRUN.ld 2>/dev/null | head -n1)
    do
      if [ -f "$cand" ]; then ldpath="$cand"; break; fi
    done
    if [ -n "$ldpath" ]; then
      echo "Patching stack size in $ldpath to 0x20000"
      # Common ST patterns
      sed -i.bak -E 's/(\b_Min_Stack_Size\s*=\s*)0x[0-9a-fA-F]+;/\10x20000;/' "$ldpath" || true
      sed -i.bak -E 's/(\b__STACK_SIZE\s*=\s*)0x[0-9a-fA-F]+;/\10x20000;/' "$ldpath" || true
      sed -i.bak -E 's/(\b__stack_size__\s*=\s*)0x[0-9a-fA-F]+;/\10x20000;/' "$ldpath" || true
      # If none of the vars exist, try to adjust the stack reservation directly
      if ! grep -Eq '\b_Min_Stack_Size\b|\b__STACK_SIZE\b|\b__stack_size__\b' "$ldpath"; then
        sed -i.bak -E 's/(\. = \. \+ )_Min_Stack_Size;/\10x20000;/' "$ldpath" || true
      fi
    else
      echo "WARNING: Could not find STM32N657XX_LRUN.ld to patch stack size" >&2
    fi
  '';

  setupHook = writeText "setup-hook.sh" ''
    export NUCLEO_N657X0_Q_PATH="$1/platform/nucleo-n657x0-q/src/platform/"
    # Platform sources only; runtime debug server provided by STM32CubeCLT on host.
  '';

  meta = {
    description = "Platform files for STM32 NUCLEO-N657X0-Q (use STM32Cube Command Line Tools gdbserver)";
    homepage = "https://github.com/STMicroelectronics/STM32CubeN6";
  };
}
