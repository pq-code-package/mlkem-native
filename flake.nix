# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{
  description = "mlkem-native";

  inputs = {
    nixpkgs-2405.url = "github:NixOS/nixpkgs/nixos-24.05";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    nixpkgs-unstable.url = "github:NixOS/nixpkgs/nixos-unstable";

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, pkgs, system, ... }:
        let
          pkgs-unstable = inputs.nixpkgs-unstable.legacyPackages.${system};
          pkgs-2405 = inputs.nixpkgs-2405.legacyPackages.${system};
          util = pkgs.callPackage ./nix/util.nix {
            inherit (pkgs) cbmc bitwuzla z3;
            # TODO: switch back to stable python3 for slothy once ortools is fixed in 25.11
            python3-for-slothy = pkgs-unstable.python3;
          };
          zigWrapCC = zig: pkgs.symlinkJoin {
            name = "zig-wrappers";
            paths = [
              (pkgs.writeShellScriptBin "cc"
                ''
                  exec ${zig}/bin/zig cc "$@"
                '')
              (pkgs.writeShellScriptBin "ar"
                ''
                  exec ${zig}/bin/zig ar "$@"
                '')
            ];
          };
          holLightShellHook = ''
            export PATH=$PWD/scripts:$PATH
            export PROOF_DIR="$PWD/proofs/hol_light"
          '';

        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (_:_: {
                # From 24.05 (dropped in 25.11)
                gcc48 = pkgs-2405.gcc48;
                gcc49 = pkgs-2405.gcc49;
                gcc7 = pkgs-2405.gcc7;
                gcc11 = pkgs-2405.gcc11;
                gcc12 = pkgs-2405.gcc12;
                clang_14 = pkgs-2405.clang_14;
                clang_15 = pkgs-2405.clang_15;
                clang_16 = pkgs-2405.clang_16;
                clang_17 = pkgs-2405.clang_17;
                zig_0_12 = pkgs-2405.zig_0_12;
              })
            ];
          };

          packages.linters = util.linters;
          packages.cbmc = util.cbmc_pkgs;
          packages.hol_light = util.hol_light';
          packages.s2n_bignum = util.s2n_bignum;
          packages.valgrind_varlat = util.valgrind_varlat;
          packages.slothy = util.slothy;
          packages.toolchains = util.toolchains;
          packages.toolchains_native = util.toolchains_native;
          packages.toolchain_x86_64 = util.toolchain_x86_64;
          packages.toolchain_aarch64 = util.toolchain_aarch64;
          packages.toolchain_riscv64 = util.toolchain_riscv64;
          packages.toolchain_riscv32 = util.toolchain_riscv32;
          packages.toolchain_ppc64le = util.toolchain_ppc64le;
          packages.toolchain_aarch64_be = util.toolchain_aarch64_be;
          packages.gcc-arm-embedded = pkgs.gcc-arm-embedded;

          devShells.default = util.mkShell {
            packages = builtins.attrValues
              {
                inherit (config.packages) linters cbmc hol_light s2n_bignum slothy toolchains_native hol_server;
                inherit (pkgs)
                  direnv
                  nix-direnv
                  zig_0_13;
              } ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ config.packages.valgrind_varlat ];
          };

          # arm-none-eabi-gcc + platform files from pqmx
          packages.m55-an547 = util.m55-an547;
          packages.avr-toolchain = util.avr-toolchain;
          devShells.arm-embedded = util.mkShell {
            packages = builtins.attrValues
              {
                inherit (config.packages) m55-an547;
                inherit (pkgs) gcc-arm-embedded qemu coreutils python3 git;
              };
          };
          packages.nucleo-n657x0-q = util.nucleo-n657x0-q;
          devShells.nucleo-n657x0-q = util.mkShell {
            packages = builtins.attrValues ({
              inherit (config.packages) nucleo-n657x0-q;
              inherit (pkgs) gcc-arm-embedded coreutils git libffi pkg-config;
            });
          };


          devShells.avr = util.mkShell (import ./nix/avr { inherit pkgs; });
          packages.hol_server = util.hol_server.hol_server_start;
          devShells.hol_light = (util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters hol_light s2n_bignum hol_server; };
          }).overrideAttrs (old: { shellHook = holLightShellHook; });
          devShells.hol_light-cross = (util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchains hol_light s2n_bignum gcc-arm-embedded hol_server; };
          }).overrideAttrs (old: { shellHook = holLightShellHook; });
          devShells.hol_light-cross-aarch64 = (util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_aarch64 hol_light s2n_bignum gcc-arm-embedded hol_server; };
          }).overrideAttrs (old: { shellHook = holLightShellHook; });
          devShells.hol_light-cross-x86_64 = (util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_x86_64 hol_light s2n_bignum gcc-arm-embedded hol_server; };
          }).overrideAttrs (old: { shellHook = holLightShellHook; });
          devShells.ci = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchains_native; };
          };
          devShells.bench = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) toolchains_native; };
          };
          devShells.cbmc = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) cbmc toolchains_native; } ++ [ pkgs.gh ];
          };
          devShells.slothy = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) slothy linters toolchains_native; };
          };
          devShells.cross = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchains; };
          };
          devShells.cross-x86_64 = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_x86_64; };
          };
          devShells.cross-aarch64 = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_aarch64; };
          };
          devShells.cross-riscv64 = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_riscv64; };
          };
          devShells.cross-riscv32 = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_riscv32; };
          };
          devShells.cross-ppc64le = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_ppc64le; };
          };
          devShells.cross-aarch64_be = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters toolchain_aarch64_be; };
          };

          # autogen shell with cross compiler for the "other" architecture
          devShells.cross-autogen = util.mkShell {
            packages = builtins.attrValues { inherit (config.packages) linters; inherit (pkgs) gcc-arm-embedded; }
              ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isx86_64 [ config.packages.toolchain_aarch64 ]
              ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isAarch64 [ config.packages.toolchain_x86_64 ];
          };

          # arm-none-eabi-gcc + platform files from pqmx
          devShells.cross-arm-embedded = util.mkShell {
            packages = builtins.attrValues
              {
                inherit (util) m55-an547;
                inherit (config.packages) linters;
                inherit (pkgs) gcc-arm-embedded qemu coreutils python3 git;
              };
          };
          devShells.cross-aarch64-embedded = util.mkShell {
            packages = builtins.attrValues
              {
                inherit (pkgs) qemu coreutils python3 git;
              } ++ [
              pkgs-unstable.pkgsCross.aarch64-embedded.stdenv.cc
            ];
          };

          devShells.cross-avr = util.mkShell (import ./nix/avr { inherit pkgs; });

          devShells.linter = util.mkShellNoCC {
            packages = builtins.attrValues { inherit (config.packages) linters; };
          };
          devShells.clang14 = util.mkShellWithCC' pkgs.clang_14;
          devShells.clang15 = util.mkShellWithCC' pkgs.clang_15;
          devShells.clang16 = util.mkShellWithCC' pkgs.clang_16;
          devShells.clang17 = util.mkShellWithCC' pkgs.clang_17;
          devShells.clang18 = util.mkShellWithCC' pkgs.clang_18;
          devShells.clang19 = util.mkShellWithCC' pkgs.clang_19;
          devShells.clang20 = util.mkShellWithCC' pkgs.clang_20;
          devShells.clang21 = util.mkShellWithCC' pkgs.clang_21;

          devShells.zig0_12 = util.mkShellWithCC' (zigWrapCC pkgs.zig_0_12);
          devShells.zig0_13 = util.mkShellWithCC' (zigWrapCC pkgs.zig_0_13);
          devShells.zig0_14 = util.mkShellWithCC' (zigWrapCC pkgs.zig_0_14);
          devShells.zig0_15 = util.mkShellWithCC' (zigWrapCC pkgs.zig);

          devShells.gcc48 = util.mkShellWithCC' pkgs.gcc48;
          devShells.gcc49 = util.mkShellWithCC' pkgs.gcc49;
          devShells.gcc7 = util.mkShellWithCC' pkgs.gcc7;
          devShells.gcc11 = util.mkShellWithCC' pkgs.gcc11;
          devShells.gcc12 = util.mkShellWithCC' pkgs.gcc12;
          devShells.gcc13 = util.mkShellWithCC' pkgs.gcc13;
          devShells.gcc14 = util.mkShellWithCC' pkgs.gcc14;
          devShells.gcc15 = util.mkShellWithCC' pkgs.gcc15;

          # valgrind with a patch for detecting variable-latency instructions
          devShells.valgrind-varlat_clang14 = util.mkShellWithCC_valgrind' pkgs.clang_14;
          devShells.valgrind-varlat_clang15 = util.mkShellWithCC_valgrind' pkgs.clang_15;
          devShells.valgrind-varlat_clang16 = util.mkShellWithCC_valgrind' pkgs.clang_16;
          devShells.valgrind-varlat_clang17 = util.mkShellWithCC_valgrind' pkgs.clang_17;
          devShells.valgrind-varlat_clang18 = util.mkShellWithCC_valgrind' pkgs.clang_18;
          devShells.valgrind-varlat_clang19 = util.mkShellWithCC_valgrind' pkgs.clang_19;
          devShells.valgrind-varlat_clang20 = util.mkShellWithCC_valgrind' pkgs.clang_20;
          devShells.valgrind-varlat_clang21 = util.mkShellWithCC_valgrind' pkgs.clang_21;
          devShells.valgrind-varlat_gcc48 = util.mkShellWithCC_valgrind' pkgs.gcc48;
          devShells.valgrind-varlat_gcc49 = util.mkShellWithCC_valgrind' pkgs.gcc49;
          devShells.valgrind-varlat_gcc7 = util.mkShellWithCC_valgrind' pkgs.gcc7;
          devShells.valgrind-varlat_gcc11 = util.mkShellWithCC_valgrind' pkgs.gcc11;
          devShells.valgrind-varlat_gcc12 = util.mkShellWithCC_valgrind' pkgs.gcc12;
          devShells.valgrind-varlat_gcc13 = util.mkShellWithCC_valgrind' pkgs.gcc13;
          devShells.valgrind-varlat_gcc14 = util.mkShellWithCC_valgrind' pkgs.gcc14;
          devShells.valgrind-varlat_gcc15 = util.mkShellWithCC_valgrind' pkgs.gcc15;
        };
      flake = {
        devShell.x86_64-linux =
          let
            pkgs = inputs.nixpkgs.legacyPackages.x86_64-linux;
            pkgs-unstable = inputs.nixpkgs-unstable.legacyPackages.x86_64-linux;
            util = pkgs.callPackage ./nix/util.nix {
              inherit pkgs;
              inherit (pkgs) cbmc bitwuzla z3;
              # TODO: switch back to stable python3 for slothy once ortools is fixed in 25.11
              python3-for-slothy = pkgs-unstable.python3;
            };
          in
          util.mkShell {
            packages =
              [
                util.linters
                util.cbmc_pkgs
                util.hol_light'
                util.s2n_bignum
                util.toolchains_native
                pkgs.zig_0_13
              ]
              ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind_varlat ];
          };
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
