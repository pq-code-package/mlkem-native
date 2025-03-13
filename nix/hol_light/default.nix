# SPDX-License-Identifier: Apache-2.0

{ hol_light, fetchFromGitHub, writeText, ... }:
hol_light.overrideAttrs (old: {
  setupHook = writeText "setup-hook.sh" ''
    export HOLDIR="$1/lib/hol_light"
    export HOLLIGHT_DIR="$1/lib/hol_light"
  '';
  version = "unstable-2024-12-22";
  src = fetchFromGitHub {
    owner = "jrh13";
    repo = "hol-light";
    rev = "0e4b1bd8c7d400214d6fa6027f15a4221b54f8d4";
    hash = "sha256-M6ddzqoAFyMBmaznuz31+o035xdEz4VXZMHhH4Dm4c8=";
  };
  patches = [ ./0005-Fix-hollight-path.patch ];
  propagatedBuildInputs = old.propagatedBuildInputs ++ old.nativeBuildInputs;
  buildPhase = ''
    HOLLIGHT_USE_MODULE=1 make hol.sh
    patchShebangs hol.sh
    HOLLIGHT_USE_MODULE=1 make
  '';
  installPhase = ''
    mkdir -p "$out/lib/hol_light"
    cp -a . $out/lib/hol_light
    sed "s^__DIR__^$out/lib/hol_light^g; s^__USE_MODULE__^1^g" hol_4.14.sh > hol.sh
    mv hol.sh $out/lib/hol_light/
  '';
})
