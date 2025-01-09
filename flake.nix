# SPDX-License-Identifier: Apache-2.0

{
  description = "mlkem-native";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    nixpkgs2411.url = "github:NixOS/nixpkgs/nixos-24.11";
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
          util = pkgs.callPackage ./nix/util.nix { bitwuzla = inputs.nixpkgs-unstable.legacyPackages.${system}.bitwuzla; };
        in
        {
          packages.cbmc = util.cbmc;
          packages.hol_light = pkgs.callPackage ./nix/hol_light { };

          devShells.default = util.wrapShell util.mkShell {
            packages =
              util.core { } ++
              util.linters ++
              builtins.attrValues
                {
                  inherit (config.packages) cbmc hol_light;
                  inherit (pkgs)
                    direnv
                    nix-direnv;
                };
          };

          devShells.hol_light = util.wrapShell util.mkShell { packages = [ config.packages.hol_light ]; };

          devShells.ci = util.wrapShell util.mkShell { packages = util.core { cross = false; }; };
          devShells.ci-cross = util.wrapShell util.mkShell { packages = util.core { }; };
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
              bitwuzla = pkgs-unstable.bitwuzla;
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
