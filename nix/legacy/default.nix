# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ system }:
let
  pkgs-2405 = import
    (builtins.fetchTarball {
      url = "https://github.com/NixOS/nixpkgs/archive/b134951a4c9f3c995fd7be05f3243f8ecd65d798.tar.gz";
      sha256 = "0zydsqiaz8qi4zd63zsb2gij2p614cgkcaisnk11wjy3nmiq0x1s";
    })
    { inherit system; };

  pkgs-2305 = import
    (builtins.fetchTarball {
      url = "https://github.com/NixOS/nixpkgs/archive/70bdadeb94ffc8806c0570eb5c2695ad29f0e421.tar.gz";
      sha256 = "05cbl1k193c9la9xhlz4y6y8ijpb2mkaqrab30zij6z4kqgclsrd";
    })
    { inherit system; };
in
{
  ccs = {
    gcc48 = pkgs-2405.gcc48;
    gcc49 = pkgs-2405.gcc49;
    gcc6 = pkgs-2405.gcc6;
    gcc7 = pkgs-2405.gcc7;
    gcc8 = pkgs-2405.gcc8;
    gcc9 = pkgs-2405.gcc9;
    gcc10 = pkgs-2405.gcc10;
    gcc11 = pkgs-2405.gcc11;
    gcc12 = pkgs-2405.gcc12;

    clang6 = pkgs-2305.clang_6;
    clang7 = pkgs-2305.clang_7;
    clang8 = pkgs-2305.clang_8;
    clang9 = pkgs-2305.clang_9;
    clang10 = pkgs-2305.clang_10;
    clang11 = pkgs-2305.clang_11;
    clang12 = pkgs-2405.clang_12;
    clang13 = pkgs-2405.clang_13;
    clang14 = pkgs-2405.clang_14;
    clang15 = pkgs-2405.clang_15;
    clang16 = pkgs-2405.clang_16;
    clang17 = pkgs-2405.clang_17;
  };

  zigs = {
    zig0_10 = pkgs-2405.zig_0_10;
    zig0_11 = pkgs-2405.zig_0_11;
    zig0_12 = pkgs-2405.zig_0_12;
  };
}
