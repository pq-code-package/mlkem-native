# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ lib
, fetchFromGitHub
, openocd
, autoreconfHook
, autoconf
, automake
, libtool
, which
}:

openocd.overrideAttrs (old: rec {
  pname = "st-openocd";
  version = "unstable-2026-05-01";

  # OpenOCD 0.12.0 lacks the STM32N6 target script required by the
  # NUCLEO-N657X0-Q RAM-only OpenOCD backend.
  src = fetchFromGitHub {
    owner = "openocd-org";
    repo = "openocd";
    rev = "4e9b167e1ae5ccb437eb0538440988b3f0ec53cb";
    fetchSubmodules = true;
    hash = "sha256-8aYl7JzulPxH6vgSeTKTMIZVH6d55JJlXTBkfgAPTbU=";
  };

  buildInputs = lib.filter
    (dep: lib.getName dep != "jimtcl")
    (old.buildInputs or [ ]);

  nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [
    autoreconfHook
    autoconf
    automake
    libtool
    which
  ];

  configureFlags = lib.filter
    (flag: flag != "--disable-internal-jimtcl")
    (old.configureFlags or [ ])
  ++ [
    "--disable-werror"
    "--enable-stlink"
    "--enable-cmsis-dap"
    "--enable-internal-jimtcl"
  ];

  preConfigure = ''
    export PATH=$PWD/.nix-wrappers:$PATH
    mkdir -p .nix-wrappers
    if command -v libtoolize >/dev/null && ! command -v glibtoolize >/dev/null; then
      ln -s "$(command -v libtoolize)" .nix-wrappers/glibtoolize || true
    fi
    if [ -x ./bootstrap ]; then ./bootstrap; fi
    if [ -x ./autogen.sh ]; then ./autogen.sh; fi
  '';

  postInstall = (old.postInstall or "") + ''
    test -f "$out/share/openocd/scripts/target/stm32n6x.cfg"
  '';

  meta = old.meta // {
    description = "OpenOCD snapshot with native ST-LINK and STM32N6 target support";
    homepage = "https://openocd.org/";
    license = lib.licenses.gpl2Plus;
  };
})
