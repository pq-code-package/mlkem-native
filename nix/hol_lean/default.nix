# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ lib
, stdenv
, fetchFromGitHub
, lean4
, makeWrapper
}:

stdenv.mkDerivation (finalAttrs: {
  pname = "hol-lean-holtrace";
  version = "0.1.0-unstable";

  src = fetchFromGitHub {
    owner = "hol-light-family";
    repo = "HolLean";
    rev = "91dff2cac719d0de458b73e1b88202f6fa59fbfd";
    hash = "sha256-Aq20XlPPT0oGi+8BimxVsmt1DM5sZL7UesgRQwyEPUg=";
  };

  nativeBuildInputs = [ lean4 makeWrapper ];

  dontConfigure = true;

  postPatch = ''
    cp ${./HolTraceAdapter.lean} HolTraceAdapter.lean
    printf '%s\n' \
      'lean_exe holtrace_adapter where' \
      '  root := `HolTraceAdapter' \
      >> lakefile.lean
  '';

  buildPhase = ''
    runHook preBuild
    lake build holtrace holtrace_adapter
    runHook postBuild
  '';

  # hol-trace runs only hollean-holtrace. The upstream verifier,
  # bin/holtrace, is kept for checking a trace by hand.
  #
  # In compiled Lean, `panic!` prints a message and returns a default
  # value unless LEAN_ABORT_ON_PANIC is set, and HolLean's kernel panics
  # in `type_of`, `inst` and `orda` on inputs it does not expect. Both
  # wrappers set it, so that such a panic ends the replay instead of
  # continuing with a default term, however the binary is started.
  installPhase = ''
    runHook preInstall
    install -Dm755 .lake/build/bin/holtrace "$out/libexec/holtrace"
    install -Dm755 .lake/build/bin/holtrace_adapter \
      "$out/libexec/hollean-holtrace"
    for name in holtrace hollean-holtrace; do
      makeWrapper "$out/libexec/$name" "$out/bin/$name" \
        --set LEAN_ABORT_ON_PANIC 1
    done
    runHook postInstall
  '';

  meta = {
    description = "HOLTrace replay through HolLean's HOL Light kernel";
    homepage = "https://github.com/hol-light-family/HolLean";
    license = lib.licenses.bsd3;
    mainProgram = "hollean-holtrace";
  };
})
