# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{
  perSystem = { lib, system, util, zigWrapCC, ... }:
    let
      legacy = import ./default.nix { inherit system; };
    in
    {
      devShells =
        lib.mapAttrs (_: cc: util.mkShellWithCC' cc) legacy.ccs
        // lib.mapAttrs' (n: cc: lib.nameValuePair "valgrind-varlat_${n}" (util.mkShellWithCC_valgrind' cc)) legacy.ccs
        // lib.mapAttrs (_: zig: util.mkShellWithCC' (zigWrapCC zig)) legacy.zigs;
    };
}
