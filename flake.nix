# SPDX-License-Identifier: Apache-2.0

{
  description = "mlkem-native";

  inputs = {
    nixpkgs-2405.url = "github:NixOS/nixpkgs/nixos-24.05";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
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
            cbmc = pkgs-unstable.cbmc;
            bitwuzla = pkgs-unstable.bitwuzla;
            z3 = pkgs-unstable.z3;
          };
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (_:_: {
                gcc48 = pkgs-2405.gcc48;
                gcc49 = pkgs-2405.gcc49;
                qemu = pkgs-unstable.qemu; # 9.2.0
              })
            ];
          };
          packages.cbmc = util.cbmc-pkgs;
          packages.hol_light = pkgs.callPackage ./nix/hol_light { };
          packages.s2n_bignum = pkgs.callPackage ./nix/s2n_bignum { };
          packages.toolchain = util.core-pkgs;

          devShells.default = util.wrapShell util.mkShell {
            packages =
              util.linters ++
              builtins.attrValues
                {
                  inherit (config.packages) toolchain cbmc s2n_bignum;
                  inherit (pkgs)
                    direnv
                    nix-direnv;
                };
          };

          devShells.hol_light = util.wrapShell util.mkShell {
            packages = builtins.attrValues {
              inherit (config.packages) hol_light s2n_bignum;
            };
          };

          devShells.ci = util.wrapShell util.mkShell { packages = util.linters ++ util.core { cross = false; }; };
          devShells.ci-bench = util.wrapShell util.mkShell { packages = util.core { cross = false; }; };
          devShells.ci-cross = util.wrapShell util.mkShell { packages = util.linters ++ util.core { }; };
          devShells.ci-cbmc = util.wrapShell util.mkShell { packages = util.core { cross = false; } ++ [ config.packages.cbmc ]; };
          devShells.ci-cbmc-cross = util.wrapShell util.mkShell { packages = util.core { } ++ [ config.packages.cbmc ]; };
          devShells.ci-linter = util.wrapShell pkgs.mkShellNoCC { packages = util.linters; };

          devShells.ci_clang14 = util.wrapShell (util.mkShellWithCC pkgs.clang_14) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_clang15 = util.wrapShell (util.mkShellWithCC pkgs.clang_15) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_clang16 = util.wrapShell (util.mkShellWithCC pkgs.clang_16) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_clang17 = util.wrapShell (util.mkShellWithCC pkgs.clang_17) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_clang18 = util.wrapShell (util.mkShellWithCC pkgs.clang_18) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_clang19 = util.wrapShell (util.mkShellWithCC inputs.nixpkgs2411.legacyPackages.${system}.clang_19) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_gcc48 = util.wrapShell (util.mkShellWithCC pkgs.gcc48) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_gcc49 = util.wrapShell (util.mkShellWithCC pkgs.gcc49) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_gcc7 = util.wrapShell (util.mkShellWithCC pkgs.gcc7) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_gcc11 = util.wrapShell (util.mkShellWithCC pkgs.gcc11) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_gcc12 = util.wrapShell (util.mkShellWithCC pkgs.gcc12) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_gcc13 = util.wrapShell (util.mkShellWithCC pkgs.gcc13) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_gcc14 = util.wrapShell (util.mkShellWithCC pkgs.gcc14) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.valgrind ]; hardeningDisable = [ "fortify" ]; };

          # valgrind with a patch for detecting variable-latency instructions
          devShells.ci_valgrind-varlat_clang14 = util.wrapShell (util.mkShellWithCC pkgs.clang_14) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_clang15 = util.wrapShell (util.mkShellWithCC pkgs.clang_15) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_clang16 = util.wrapShell (util.mkShellWithCC pkgs.clang_16) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_clang17 = util.wrapShell (util.mkShellWithCC pkgs.clang_17) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_clang18 = util.wrapShell (util.mkShellWithCC pkgs.clang_18) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_clang19 = util.wrapShell (util.mkShellWithCC inputs.nixpkgs2411.legacyPackages.${system}.clang_19) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_gcc48 = util.wrapShell (util.mkShellWithCC pkgs.gcc48) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_gcc49 = util.wrapShell (util.mkShellWithCC pkgs.gcc49) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_gcc7 = util.wrapShell (util.mkShellWithCC pkgs.gcc7) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_gcc11 = util.wrapShell (util.mkShellWithCC pkgs.gcc11) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_gcc12 = util.wrapShell (util.mkShellWithCC pkgs.gcc12) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_gcc13 = util.wrapShell (util.mkShellWithCC pkgs.gcc13) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };
          devShells.ci_valgrind-varlat_gcc14 = util.wrapShell (util.mkShellWithCC pkgs.gcc14) { packages = [ pkgs.python3 ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ util.valgrind-varlat ]; hardeningDisable = [ "fortify" ]; };

        };
      flake = {
        devShell.x86_64-linux =
          let
            pkgs = inputs.nixpkgs.legacyPackages.x86_64-linux;
            pkgs-unstable = inputs.nixpkgs-unstable.legacyPackages.x86_64-linux;
            util = pkgs.callPackage ./nix/util.nix {
              inherit pkgs;
              cbmc = pkgs-unstable.cbmc;
              bitwuzla = pkgs-unstable.bitwuzla;
              z3 = pkgs-unstable.z3;
            };
          in
          util.wrapShell util.mkShell {
            packages =
              util.core { } ++
              util.linters ++
              [
                util.cbmc
              ];
          };
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
