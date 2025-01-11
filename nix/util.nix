# SPDX-License-Identifier: Apache-2.0

{ pkgs, bitwuzla }:
rec {
  glibc-join = p: p.buildPackages.symlinkJoin {
    name = "glibc-join";
    paths = [ p.glibc p.glibc.static ];
  };

  wrap-gcc = p: p.buildPackages.wrapCCWith {
    cc = p.buildPackages.gcc13.cc;
    bintools = p.buildPackages.wrapBintoolsWith {
      bintools = p.buildPackages.binutils-unwrapped;
      libc = glibc-join p;
    };
  };

  native-gcc =
    if pkgs.stdenv.isDarwin
    then null
    else wrap-gcc pkgs;

  # cross is for determining whether to install the cross toolchain or not
  core = { cross ? true }:
    let
      x86_64-gcc = wrap-gcc pkgs.pkgsCross.gnu64;
      aarch64-gcc = wrap-gcc pkgs.pkgsCross.aarch64-multiplatform;
      riscv64-gcc = wrap-gcc pkgs.pkgsCross.riscv64;
      aarch64_be-gcc = (pkgs.callPackage ./aarch64_be-none-linux-gnu-gcc.nix { });
    in
    # NOTE:
      # - native toolchain should be equipped in the shell via `mkShellWithCC` (see `mkShell`)
      # - only install extra cross-compiled toolchains if not on darwin or `cross` is specifally set to true
      # - providing cross compilation toolchain (x86_64/aarch64-linux) for darwin can be cumbersome
      #   and won't just work for now
      # - equip all toolchains if cross is explicitly set to true
      # - On some machines, `native-gcc` needed to be evaluated lastly (placed as the last element of the toolchain list), or else would result in environment variables (CC, AR, ...) overriding issue.
    pkgs.lib.optionals (cross && !pkgs.stdenv.isDarwin) [
      (pkgs.lib.optional (! pkgs.stdenv.isx86_64) x86_64-gcc)
      (pkgs.lib.optional (! pkgs.stdenv.isAarch64) aarch64-gcc)
      (pkgs.lib.optional (pkgs.stdenv.isx86_64 || pkgs.stdenv.isAarch64) riscv64-gcc)
      (pkgs.lib.optional (pkgs.stdenv.isx86_64) aarch64_be-gcc)
      native-gcc
    ]
    ++ builtins.attrValues {
      inherit (pkgs)
        python3
        qemu; # 8.2.4
    };

  wrapShell = mkShell: attrs:
    mkShell (attrs // {
      shellHook = ''
        export PATH=$PWD/scripts:$PATH
      '' +
      # NOTE: we don't support nix gcc toolchains for darwin system, therefore explicitly setting environment variables like CC, AR, AS, ... is required
      pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
        export CC=gcc
        export CXX=g++
        for cmd in \
            ar as ld nm objcopy objdump readelf ranlib strip strings size windres
        do
            export ''${cmd^^}=$cmd
        done
      '';
    });

  # NOTE: idiomatic nix way of properly setting the $CC in a nix shell
  mkShellWithCC = cc: pkgs.mkShellNoCC.override { stdenv = pkgs.overrideCC pkgs.stdenv cc; };
  mkShell = mkShellWithCC native-gcc;

  linters =
    builtins.attrValues {
      clang-tools = pkgs.clang-tools.overrideAttrs {
        unwrapped = pkgs.llvmPackages_17.clang-unwrapped;
      };

      inherit (pkgs)
        nixpkgs-fmt
        shfmt;

      inherit (pkgs.python3Packages)
        black;
    };

  cbmc = pkgs.callPackage ./cbmc { inherit bitwuzla; };
}
