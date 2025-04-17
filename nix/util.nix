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
    then pkgs.clang_16
    else wrap-gcc pkgs;

  # cross is for determining whether to install the cross toolchain dependencies or not
  _toolchains = { cross ? true }:
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
    pkgs.lib.optionals cross [ pkgs.qemu x86_64-gcc aarch64-gcc riscv64-gcc ]
    ++ pkgs.lib.optionals (cross && pkgs.stdenv.isLinux && pkgs.stdenv.isx86_64) [ aarch64_be-gcc ]
    ++ pkgs.lib.optionals cross [ native-gcc ]
    # NOTE: Tools in /Library/Developer/CommandLineTools/usr/bin on macOS are inaccessible in the Nix shell. This issue is addressed in https://github.com/NixOS/nixpkgs/pull/353893 but hasn’t been merged into the 24.11 channel yet. As a workaround, we include this dependency for macOS temporary.
    ++ pkgs.lib.optionals (pkgs.stdenv.isDarwin) [ pkgs.git ]
    ++ builtins.attrValues {
      inherit (pkgs.python3Packages) sympy pyyaml;
      inherit (pkgs)
        gnumake
        python3;
    };

  # NOTE: idiomatic nix way of properly setting the $CC in a nix shell
  mkShellWithCC = cc: attrs: (pkgs.mkShellNoCC.override { stdenv = pkgs.overrideCC pkgs.stdenv cc; }) (
    attrs // {
      shellHook = ''
        export PATH=$PWD/scripts:$PATH
      '';
    }
  );
  mkShellNoCC = mkShellWithCC null;
  mkShell = mkShellWithCC native-gcc;

  mkShellWithCC' = cc:
    mkShellWithCC cc {
      packages = [ pkgs.python3 ];
      hardeningDisable = [ "fortify" ];
    };
  mkShellWithCC_valgrind' = cc:
    mkShellWithCC cc {
      packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ valgrind_varlat ];
      hardeningDisable = [ "fortify" ];
    };

  # some customized packages
  linters = pkgs.symlinkJoin {
    name = "pqcp-linters";
    paths = builtins.attrValues {
      clang-tools = pkgs.clang-tools.overrideAttrs {
        unwrapped = pkgs.llvmPackages_18.clang-unwrapped;
      };

      inherit (pkgs.llvmPackages_18)
        bintools;

      inherit (pkgs)
        nixpkgs-fmt
        shfmt;

      inherit (pkgs.python3Packages)
        mpmath sympy black pyparsing pyyaml;
    };
  };

  cbmc_pkgs = pkgs.callPackage ./cbmc {
    inherit cbmc bitwuzla z3;
  };

  valgrind_varlat = pkgs.callPackage ./valgrind { };
  hol_light' = pkgs.callPackage ./hol_light { };
  s2n_bignum = pkgs.callPackage ./s2n_bignum { };
  slothy = pkgs.callPackage ./slothy { };

  toolchains = pkgs.symlinkJoin {
    name = "toolchains";
    paths = _toolchains { };
  };

  toolchains_native = pkgs.symlinkJoin {
    name = "toolchains-native";
    paths = _toolchains { cross = false; };
  };
}
