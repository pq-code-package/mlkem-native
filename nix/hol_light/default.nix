# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ hol_light, fetchFromGitHub, writeText, ocamlPackages, ledit, ... }:
hol_light.overrideAttrs (old: {
  setupHook = writeText "setup-hook.sh" ''
    export HOLDIR="$1/lib/hol_light"
    export HOLLIGHT_DIR="$1/lib/hol_light"
    export PATH="$1/lib/hol_light:$PATH"
  '';
  version = "unstable-2025-11-17";
  src = fetchFromGitHub {
    owner = "jrh13";
    repo = "hol-light";
    rev = "08bcac75772d37c2447a90c90d1dff9ab415f217";
    hash = "sha256-kYOzGW7uQGOM/b+JPWQfpqqtgMmMku/BkN58WZTtokU=";
  };
  patches = [
    ./0005-Configure-hol-sh-for-mlkem-native.patch
    ./0006-Add-findlib-to-ocaml-hol.patch
  ];
  propagatedBuildInputs = old.propagatedBuildInputs ++ old.nativeBuildInputs ++ [ ocamlPackages.pcre2 ledit ];
  buildPhase = ''
    patchShebangs pa_j/chooser.sh
    patchShebangs update_database/chooser.sh
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
