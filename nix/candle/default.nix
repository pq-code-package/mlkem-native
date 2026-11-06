# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# Candle publishes its CakeML evaluator as x86_64 assembly only, so this
# package is x86_64-linux only.
{ lib
, stdenv
, fetchFromGitHub
, fetchurl
, python3
}:

let
  # The CakeML build that build-instructions.sh of this Candle commit
  # downloads.
  cakeML = fetchurl {
    url = "https://cakeml.org/regression/artefacts/3286/cake-x64-64.tar.gz";
    hash = "sha256-TgdAkOsE2P37YlNkV62zHJjhsX9s1myUg4BmASUQU7c=";
  };
in
stdenv.mkDerivation (finalAttrs: {
  pname = "hol-candle";
  version = "0-unstable";

  src = fetchFromGitHub {
    owner = "CakeML";
    repo = "candle";
    rev = "646e3a2afbf20a8fcfdb15cf7562ee321b74791c";
    hash = "sha256-KFK2wtNsEZBVQQs+c9cK3SOYYudAy/kaUBX2UzXsT30=";
  };

  nativeBuildInputs = [ python3 ];

  dontConfigure = true;
  dontPatchELF = true;
  dontStrip = true;

  buildPhase = ''
    runHook preBuild
    mkdir -p candle/build
    tar xzf ${cakeML} -C candle/build --strip-components=1
    (
      cd candle/build
      patch cake.S ../cake.S.patch
      patch basis_ffi.c ../basis_ffi.c.patch
      cc -O2 cake.S basis_ffi.c -DEVAL -o cake -lm
      ./cake --types < /dev/null > types.txt 2>&1
      python3 ../insulate.py types.txt insulate.ml
      cat ../chdir_to_root.ml >> candle_boot.ml
      rm -f cake.S cake.S.orig basis_ffi.c.orig \
        cake-sexpr-32 cake-sexpr-64
    )
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p "$out/share" "$out/bin"
    cp -r . "$out/share/candle"
    substitute ${./run-candle.sh} "$out/bin/candle" \
      --replace-fail @bash@ ${stdenv.shell} \
      --replace-fail @candle@ "$out/share/candle"
    chmod +x "$out/bin/candle"
    runHook postInstall
  '';

  meta = {
    description = "CakeML implementation of HOL Light";
    homepage = "https://cakeml.org/candle/";
    license = lib.licenses.bsd3;
    mainProgram = "candle";
    platforms = [ "x86_64-linux" ];
  };
})
