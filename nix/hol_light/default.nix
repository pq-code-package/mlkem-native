# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ lib, hol_light, fetchFromGitHub, writeText, ocamlPackages, ledit, ... }:
let
  # nixpkgs camlp5 8.05 doesn't propagate its findlib deps; put them on OCAMLPATH for hol.sh.
  # TODO: upstream to nixpkgs (camlp5 should propagate fmt/pcre2) and drop this.
  camlp5OcamlPath = lib.makeSearchPath
    "lib/ocaml/${ocamlPackages.ocaml.version}/site-lib"
    (with ocamlPackages; [ fmt pcre2 camlp-streams ]);
in
hol_light.overrideAttrs (old: {
  setupHook = writeText "setup-hook.sh" ''
    export HOLDIR="$1/lib/hol_light"
    export HOLLIGHT_DIR="$1/lib/hol_light"
    export PATH="$1/lib/hol_light:$PATH"
  '';
  version = "unstable-2026-04-17";
  src = fetchFromGitHub {
    owner = "jrh13";
    repo = "hol-light";
    rev = "af5d20e033025a9f30a490d9c39edace632405a3";
    hash = "sha256-R5hSHguVu7YPP7bnFJQ1Prc8Yy3L41LAB20LfEr/RUw=";
  };
  patches = [
    ./0005-Configure-hol-sh-for-mlkem-native.patch
    ./0006-Add-findlib-to-ocaml-hol.patch
    ./0007-Accept-camlp5-8.05-for-OCaml-5.4.patch
  ];
  propagatedBuildInputs = old.propagatedBuildInputs ++ old.nativeBuildInputs ++ [ ocamlPackages.pcre2 ledit ];
  buildPhase = ''
    patchShebangs .
    HOLLIGHT_USE_MODULE=1 make hol.sh
    HOLLIGHT_USE_MODULE=1 make
  '';
  installPhase = ''
    mkdir -p "$out/lib/hol_light"
    cp -a . $out/lib/hol_light
    sed "s^__DIR__^$out/lib/hol_light^g; s^__USE_MODULE__^1^g" hol_4.14.sh > hol.sh
    mv hol.sh $out/lib/hol_light/
    # TODO: drop once nixpkgs camlp5 propagates its findlib deps (fmt/pcre2).
    substituteInPlace $out/lib/hol_light/hol.sh \
      --replace-fail 'export HOLLIGHT_USE_MODULE=1' \
        'export HOLLIGHT_USE_MODULE=1; export OCAMLPATH="${camlp5OcamlPath}''${OCAMLPATH:+:''$OCAMLPATH}"'
  '';
})
