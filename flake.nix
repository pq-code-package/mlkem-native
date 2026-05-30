# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{
  description = "mlkem-native";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    nixpkgs-unstable.url = "github:NixOS/nixpkgs/nixos-unstable";

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ./nix/legacy/module.nix ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, pkgs, system, ... }:
        let
          pkgs-unstable = inputs.nixpkgs-unstable.legacyPackages.${system};
          util = pkgs.callPackage ./nix/util.nix {
            inherit (pkgs) bitwuzla z3;
            inherit (pkgs-unstable) cbmc;
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
            # Resolve the repo root independently of the directory from which
            # `nix develop` was invoked, so that PROOF_DIR / IMPORTS_DIR always
            # point at the real proofs/hol_light tree (and .imports is not
            # created in a spurious subdirectory-nested path).
            REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || echo "$PWD")"
            export PATH="$REPO_ROOT/scripts:$PATH"
            export PROOF_DIR="$REPO_ROOT/proofs/hol_light"
            # Namespaced imports root for HOL-Light proofs.
            # See scripts/check-hol-light-imports for the enforced rule.
            export IMPORTS_DIR="$PROOF_DIR/.imports"
            mkdir -p "$IMPORTS_DIR"
            ln -sfn "$S2N_BIGNUM_DIR" "$IMPORTS_DIR/s2n_bignum"
            ln -sfn "$PROOF_DIR"      "$IMPORTS_DIR/mlkem_native"
          '';
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (_:_: {
                # Add pkgs-unstable overlays here when needed
              })
            ];
          };
          _module.args.util = util;
          _module.args.zigWrapCC = zigWrapCC;

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

          devShells.default = (util.mkShell {
            packages = builtins.attrValues
              {
                inherit (config.packages) linters cbmc hol_light s2n_bignum slothy toolchains_native hol_server;
                inherit (pkgs)
                  direnv
                  nix-direnv
                  zig_0_13;
              } ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ config.packages.valgrind_varlat ];
          }).overrideAttrs (old: { shellHook = holLightShellHook; });

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
                inherit (util) pqmx;
                inherit (config.packages) linters;
                inherit (pkgs) gcc-arm-embedded qemu coreutils git;
              };
          };
          devShells.cross-aarch64-embedded = util.mkShell {
            packages = builtins.attrValues
              {
                inherit (pkgs) qemu coreutils git;
              } ++ [
              util.pythonEnv
              pkgs-unstable.pkgsCross.aarch64-embedded.stdenv.cc
            ];
          };

          devShells.cross-avr = util.mkShell (import ./nix/avr { inherit pkgs; });

          devShells.linter = util.mkShellNoCC {
            packages = builtins.attrValues { inherit (config.packages) linters; };
          };
          devShells.clang19 = util.mkShellWithCC' pkgs.clang_19;
          devShells.clang20 = util.mkShellWithCC' pkgs.clang_20;
          devShells.clang21 = util.mkShellWithCC' pkgs.clang_21;
          devShells.clang22 = util.mkShellWithCC' pkgs.clang_22;

          devShells.zig0_13 = util.mkShellWithCC' (zigWrapCC pkgs.zig_0_13);
          devShells.zig0_14 = util.mkShellWithCC' (zigWrapCC pkgs.zig_0_14);
          devShells.zig0_15 = util.mkShellWithCC' (zigWrapCC pkgs.zig_0_15);
          devShells.zig0_16 = util.mkShellWithCC' (zigWrapCC pkgs.zig_0_16);

          devShells.gcc13 = util.mkShellWithCC' pkgs.gcc13;
          devShells.gcc14 = util.mkShellWithCC' pkgs.gcc14;
          devShells.gcc15 = util.mkShellWithCC' pkgs.gcc15;
          devShells.gcc16 = util.mkShellWithCC' pkgs.gcc16;

          # valgrind with a patch for detecting variable-latency instructions
          devShells.valgrind-varlat_clang19 = util.mkShellWithCC_valgrind' pkgs.clang_19;
          devShells.valgrind-varlat_clang20 = util.mkShellWithCC_valgrind' pkgs.clang_20;
          devShells.valgrind-varlat_clang21 = util.mkShellWithCC_valgrind' pkgs.clang_21;
          devShells.valgrind-varlat_clang22 = util.mkShellWithCC_valgrind' pkgs.clang_22;
          devShells.valgrind-varlat_gcc13 = util.mkShellWithCC_valgrind' pkgs.gcc13;
          devShells.valgrind-varlat_gcc14 = util.mkShellWithCC_valgrind' pkgs.gcc14;
          devShells.valgrind-varlat_gcc15 = util.mkShellWithCC_valgrind' pkgs.gcc15;
          devShells.valgrind-varlat_gcc16 = util.mkShellWithCC_valgrind' pkgs.gcc16;
        };
      flake = {
        devShell.x86_64-linux =
          let
            pkgs = inputs.nixpkgs.legacyPackages.x86_64-linux;
            pkgs-unstable = inputs.nixpkgs-unstable.legacyPackages.x86_64-linux;
            util = pkgs.callPackage ./nix/util.nix {
              inherit pkgs;
              inherit (pkgs) bitwuzla z3;
              inherit (pkgs-unstable) cbmc;
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
