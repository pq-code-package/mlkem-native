# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# HOLTrace (https://holtrace.cr.yp.to/) records the primitive inferences
# of a HOL Light run in a trace file, which a separate HOL Light process
# replays through its own kernel. See proofs/hol_light/hol_trace/README.md.
#
# This builds everything that proofs/hol_light/hol_trace/hol-trace needs:
#
# - hol_light_record: our HOL Light with HOLTrace's `install+hashtt`.
#   Runs the proofs and writes the traces. hashtt changes the kernel
#   (fusion.ml) to cache hashes, so this build is used for recording only.
# - hol_light_replay: our HOL Light with the plain `install`. Replays
#   (checks) traces; its kernel and HOLTrace's replay code are unchanged
#   apart from the comparison fix in 0001. `hol-trace outline` uses it
#   too, because it records every type definition; every HOL Light shell
#   exports it as HOLTRACE_REPLAY_HOL.
# - s2n_bignum_hashtt: s2n-bignum rewritten for hashtt's constructors,
#   with a fix (0005) for code that breaks while HOLTrace records.
# - bin/holtrace-hashtt-rewrite: the same rewrite, for our proofs.
# - bin/holtrace-prune: shrinks a trace to what named theorems need.
#
# All changes to HOLTrace are the patches in this directory.
{ lib
, stdenv
, stdenvNoCC
, fetchurl
, writeText
, makeWrapper
, python3
, pypy3
, hol_light'
, s2n_bignum
}:

let
  version = "20250714";

  tarball = fetchurl {
    url = "https://holtrace.cr.yp.to/holtrace-${version}.tar.gz";
    sha256 = "3c5f8be726d3b3c9f06b93f7a58ce49d624f9e36dcfdf6e9e9cdb9fe64528972";
  };

  commonPatches = [
    ./0001-compare-hol-objects-with-compare.patch
    ./0002-install-worker-string-literals-and-main-guard.patch
    ./0003-holtrace-prune-mark-without-recursion.patch
  ];

  mkSrc = name: patches: stdenvNoCC.mkDerivation {
    pname = "holtrace-src-${name}";
    inherit version patches;
    src = tarball;
    dontConfigure = true;
    dontBuild = true;
    installPhase = ''
      cp -a . "$out"
    '';
  };

  # The replay build, the rewriter (install-worker) and s2n_bignum_hashtt
  # use src_replay. Recording-only patches therefore leave the replay
  # build unchanged.
  src_replay = mkSrc "replay" commonPatches;
  src_record = mkSrc "record" (commonPatches ++ [
    ./0004-holtrace-save-no-per-line-syscalls.patch
  ]);

  # mode: "install" or "install+hashtt"
  #
  # These builds are reached only through the HOLTRACE_*_HOL variables.
  # Drop bin/ and the setup hook that hol_light' has, so that adding one
  # to a shell's packages cannot put its hol.sh on PATH or make it
  # HOLLIGHT_DIR, which ordinary proofs use.
  mkHolLight = pname: src: mode: hol_light'.overrideAttrs (old: {
    inherit pname;
    nativeBuildInputs = old.nativeBuildInputs ++ [ python3 ];
    postPatch = (old.postPatch or "") + ''
      hol="$PWD"
      (cd ${src} && python3 install-worker ${mode} "$hol")
      find . -name '*.hashtt-bak' -delete
    '';
    setupHook = null;
    postInstall = (old.postInstall or "") + ''
      rm -rf "$out/bin"
    '';
  });

  hol_light_record = mkHolLight "hol_light-holtrace-record" src_record "install+hashtt";
  hol_light_replay = mkHolLight "hol_light-holtrace-replay" src_replay "install";

  hashtt_rewrite = stdenvNoCC.mkDerivation {
    pname = "holtrace-hashtt-rewrite";
    inherit version;
    dontUnpack = true;
    installPhase = ''
      mkdir -p "$out/bin"
      substitute ${./hashtt-rewrite.py} "$out/bin/holtrace-hashtt-rewrite" \
        --replace-fail @python3@ ${python3}/bin/python3 \
        --replace-fail @installWorker@ ${src_replay}/install-worker
      chmod +x "$out/bin/holtrace-hashtt-rewrite"
    '';
  };

  s2n_bignum_hashtt = stdenvNoCC.mkDerivation {
    pname = "s2n_bignum-hashtt";
    inherit (s2n_bignum) version;
    src = s2n_bignum;
    patches = [ ./0005-s2n-bignum-x86-decode-without-relying-on-sharing.patch ];
    dontConfigure = true;
    buildPhase = ''
      ${hashtt_rewrite}/bin/holtrace-hashtt-rewrite .
    '';
    installPhase = ''
      cp -a . "$out"
    '';
  };

  # holtrace-prune is a pypy3 script; fall back to CPython (slower).
  python_prune =
    if lib.meta.availableOn stdenv.hostPlatform pypy3
    then "${pypy3}/bin/pypy3"
    else "${python3}/bin/python3";
in
stdenvNoCC.mkDerivation {
  pname = "hol_trace";
  inherit version;
  dontUnpack = true;
  nativeBuildInputs = [ makeWrapper ];
  installPhase = ''
    mkdir -p "$out/bin"
    ln -s ${hashtt_rewrite}/bin/holtrace-hashtt-rewrite "$out/bin/"
    makeWrapper ${python_prune} "$out/bin/holtrace-prune" \
      --add-flags ${src_record}/holtrace-prune
  '';
  # HOLTRACE_REPLAY_HOL is exported by every HOL Light shell instead; see
  # flake.nix.
  setupHook = writeText "hol-trace-setup-hook.sh" ''
    export HOLTRACE_RECORD_HOL=${hol_light_record}/lib/hol_light
    export HOLTRACE_S2N_BIGNUM=${s2n_bignum_hashtt}
  '';
  passthru = {
    inherit hol_light_record hol_light_replay s2n_bignum_hashtt src_record src_replay;
  };
  meta = {
    description = "HOLTrace with mlkem-native patches, for recording and replaying HOL Light proofs";
    homepage = "https://holtrace.cr.yp.to/";
    license = lib.licenses.publicDomain;
  };
}
