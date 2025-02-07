# SPDX-License-Identifier: Apache-2.0

{ pkgs, cbmc, bitwuzla, z3 }:
rec {
  glibc-join = p: p.buildPackages.symlinkJoin {
    name = "glibc-join";
    paths = [ p.glibc p.glibc.static ];
  };

  wrap-gcc = p: p.buildPackages.wrapCCWith {
    cc = p.buildPackages.gcc14.cc;
    bintools = p.buildPackages.wrapBintoolsWith {
      bintools = p.buildPackages.binutils-unwrapped;
      libc = glibc-join p;
    };
  };

  native-gcc =
    if pkgs.stdenv.isDarwin
    then pkgs.clang_15
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
    pkgs.lib.optionals cross [ x86_64-gcc aarch64-gcc riscv64-gcc ]
    ++ pkgs.lib.optionals (cross && pkgs.stdenv.isLinux && pkgs.stdenv.isx86_64) [ aarch64_be-gcc ]
    ++ pkgs.lib.optionals cross [ native-gcc ]
    # NOTE: Tools in /Library/Developer/CommandLineTools/usr/bin on macOS are inaccessible in the Nix shell. This issue is addressed in https://github.com/NixOS/nixpkgs/pull/353893 but hasn’t been merged into the 24.11 channel yet. As a workaround, we include this dependency for macOS temporary. 
    ++ pkgs.lib.optionals (pkgs.stdenv.isDarwin) [ pkgs.git ]
    ++ builtins.attrValues {
      inherit (pkgs.python3Packages) sympy pyyaml;
      inherit (pkgs)
        python3
        qemu; # 8.2.4
    };

  core-pkgs = pkgs.symlinkJoin {
    name = "toolchain join";
    paths = core { };
  };

  wrapShell = mkShell: attrs:
    mkShell (attrs // {
      shellHook = ''
        export PATH=$PWD/scripts:$PATH
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

      inherit (pkgs.llvmPackages_17)
        bintools;

      inherit (pkgs)
        nixpkgs-fmt
        shfmt;

      inherit (pkgs.python3Packages)
        mpmath sympy black;
    };

  cbmc-pkgs = pkgs.callPackage ./cbmc {
    inherit cbmc bitwuzla z3;
  };
  valgrind-varlat = pkgs.callPackage ./valgrind { };
}
