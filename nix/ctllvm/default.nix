# SPDX-License-Identifier: Apache-2.0

{ stdenv, fetchFromGitHub, llvmPackages }:

stdenv.mkDerivation rec {
  pname = "ct-llvm";
  version = "74f31984d300dfa3865ef5f23d5b373d52817425";

  src = fetchFromGitHub {
    owner = "Neo-Outis";
    repo = "CT-LLVM-Artifact";
    rev = "74f31984d300dfa3865ef5f23d5b373d52817425";
    hash = "sha256-1UZAwY4iP/oIx9ek/c4SBaMsqyDvy4brI34z3OQnYJM=";
  };

  nativeBuildInputs = [ llvmPackages.clang ];
  buildInputs = [ llvmPackages.llvm llvmPackages.llvm.dev ];

  buildPhase = ''
    clang++ -Wno-c++17-extensions -fPIC -shared -std=c++17 \
      ctllvm.cpp -o ctllvm.so \
      $(llvm-config --cxxflags --ldflags --system-libs --libs core passes)
  '';

  installPhase = ''
    mkdir -p $out/bin
    cp ctllvm.so $out/bin/
  '';

  meta = {
    description = "CT-LLVM: Constant-Time Analysis Tool for LLVM";
    homepage = "https://github.com/Neo-Outis/CT-LLVM-Artifact";
    license = "Apache-2.0";
    platforms = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
  };
}
