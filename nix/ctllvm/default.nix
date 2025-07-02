# SPDX-License-Identifier: Apache-2.0

{ stdenv, fetchFromGitHub, llvmPackages }:

stdenv.mkDerivation rec {
  pname = "ct-llvm";
  version = "4a502a1fd1bb9609c676fc2b36f5a77bd90ec850";

  src = fetchFromGitHub {
    owner = "Neo-Outis";
    repo = "CT-LLVM-Artifact";
    rev = "4a502a1fd1bb9609c676fc2b36f5a77bd90ec850";
    hash = "sha256-j/e5feXFJkWJD4z7BXFFmMQsXUUj8Hzf1XSjUNaAXCk=";
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
