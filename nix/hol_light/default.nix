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
    rev = "c5e165f85dfb340a786dabd1073a24aa421dd61b";
    hash = "sha256-umKHUsVKBVZ9EZzu3Ry9harbslP9uWlo11YDxNLaYZY";
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
