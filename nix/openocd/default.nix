# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ fetchFromGitHub
, openocd
, autoreconfHook
}:

openocd.overrideAttrs (old: rec {
  pname = "openocd";
  version = "unstable-2026-05-01";
  nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ autoreconfHook ];

  src = fetchFromGitHub {
    owner = "openocd-org";
    repo = "openocd";
    rev = "4e9b167e1ae5ccb437eb0538440988b3f0ec53cb";
    fetchSubmodules = true;
    hash = "sha256-8aYl7JzulPxH6vgSeTKTMIZVH6d55JJlXTBkfgAPTbU=";
  };
})
