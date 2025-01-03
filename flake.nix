# SPDX-License-Identifier: Apache-2.0

{
  description = "mlkem-native";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
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

          devShells.default = util.wrapShell util.mkShell {
            packages =
              util.core { } ++
              util.linters ++
              builtins.attrValues
                {
                  inherit (config.packages) cbmc;
                  inherit (pkgs)
                    direnv
                    nix-direnv;
                };
          };

          devShells.ci = util.wrapShell util.mkShell { packages = util.core { cross = false; }; };
          devShells.ci-cross = util.wrapShell util.mkShell { packages = util.core { }; };
          devShells.ci-cbmc = util.wrapShell util.mkShell { packages = util.core { cross = false; } ++ [ config.packages.cbmc ]; };
          devShells.ci-cbmc-cross = util.wrapShell util.mkShell { packages = util.core { } ++ [ config.packages.cbmc ]; };
          devShells.ci-linter = util.wrapShell pkgs.mkShellNoCC { packages = util.linters; };

          devShells.ci_clang18 = util.wrapShell (util.mkShellWithCC pkgs.clang_18) { packages = [ pkgs.python3 ]; };
          devShells.ci_gcc48 = util.wrapShell (util.mkShellWithCC pkgs.gcc48) { packages = [ pkgs.python3 ]; };
          devShells.ci_gcc49 = util.wrapShell (util.mkShellWithCC pkgs.gcc49) { packages = [ pkgs.python3 ]; };
          devShells.ci_gcc7 = util.wrapShell (util.mkShellWithCC pkgs.gcc7) { packages = [ pkgs.python3 ]; };
          devShells.ci_gcc11 = util.wrapShell (util.mkShellWithCC pkgs.gcc11) { packages = [ pkgs.python3 ]; };
          devShells.ci_gcc14 = util.wrapShell (util.mkShellWithCC pkgs.gcc14) { packages = [ pkgs.python3 ]; };
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
