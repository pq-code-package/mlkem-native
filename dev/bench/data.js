window.BENCHMARK_DATA = {
  "lastUpdate": 1791703975957,
  "repoUrl": "https://github.com/pq-code-package/mlkem-native",
  "entries": {
    "Arm Cortex-A76 (Raspberry Pi 5) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "matthias@zerorisc.com",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "6b12c8cd67e1edd07c43f581386449a6b064e6e2",
          "message": "x86_64: Clear upper YMM state before returning from AVX2 assembly\n\nNone of the AVX2 routines executes vzeroupper, so they return with\ndirty upper YMM halves, and callers built without AVX pay for every\nlegacy SSE instruction that follows. AWS-LC, whose C code is compiled\nwithout -mavx2, runs ML-KEM-768 keygen in 43k cycles on Zen 4; adding\nvzeroupper to its (identical) s2n-bignum Keccak x4 routine alone brings\nthat down to 36k.\n\nBump s2n-bignum to a version that models VZEROUPPER and update the\nHOL-Light proofs accordingly: allow all ZMM registers to change, and\nstep until the target RIP, as the AArch64 proofs do, instead of\nhard-coding the number of instructions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-06T04:36:07Z",
          "tree_id": "e5b36c58c1f4558fc2fa23774d86a8a5ba146c4f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/6b12c8cd67e1edd07c43f581386449a6b064e6e2"
        },
        "date": 1791348217081,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44499,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47588,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53843,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68490,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70162,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78631,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98229,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "matthias@zerorisc.com",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "6b12c8cd67e1edd07c43f581386449a6b064e6e2",
          "message": "x86_64: Clear upper YMM state before returning from AVX2 assembly\n\nNone of the AVX2 routines executes vzeroupper, so they return with\ndirty upper YMM halves, and callers built without AVX pay for every\nlegacy SSE instruction that follows. AWS-LC, whose C code is compiled\nwithout -mavx2, runs ML-KEM-768 keygen in 43k cycles on Zen 4; adding\nvzeroupper to its (identical) s2n-bignum Keccak x4 routine alone brings\nthat down to 36k.\n\nBump s2n-bignum to a version that models VZEROUPPER and update the\nHOL-Light proofs accordingly: allow all ZMM registers to change, and\nstep until the target RIP, as the AArch64 proofs do, instead of\nhard-coding the number of instructions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-06T04:36:07Z",
          "tree_id": "e5b36c58c1f4558fc2fa23774d86a8a5ba146c4f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/6b12c8cd67e1edd07c43f581386449a6b064e6e2"
        },
        "date": 1791442619584,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28211,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34079,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44499,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47586,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68492,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70164,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78621,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98225,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Arm Cortex-M55 (NUCLEO-N657X0-Q) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "matthias@zerorisc.com",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "6b12c8cd67e1edd07c43f581386449a6b064e6e2",
          "message": "x86_64: Clear upper YMM state before returning from AVX2 assembly\n\nNone of the AVX2 routines executes vzeroupper, so they return with\ndirty upper YMM halves, and callers built without AVX pay for every\nlegacy SSE instruction that follows. AWS-LC, whose C code is compiled\nwithout -mavx2, runs ML-KEM-768 keygen in 43k cycles on Zen 4; adding\nvzeroupper to its (identical) s2n-bignum Keccak x4 routine alone brings\nthat down to 36k.\n\nBump s2n-bignum to a version that models VZEROUPPER and update the\nHOL-Light proofs accordingly: allow all ZMM registers to change, and\nstep until the target RIP, as the AArch64 proofs do, instead of\nhard-coding the number of instructions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-06T04:36:07Z",
          "tree_id": "e5b36c58c1f4558fc2fa23774d86a8a5ba146c4f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/6b12c8cd67e1edd07c43f581386449a6b064e6e2"
        },
        "date": 1791444600599,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 647367,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 728024,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 928692,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 1032214,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 1162339,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 1433590,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 1594936,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 1747347,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 2094866,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Intel Xeon 4th gen (c7i)": [
      {
        "commit": {
          "author": {
            "email": "matthias@zerorisc.com",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": false,
          "id": "7155ef240925a0f5c554075e4b94885328760902",
          "message": "CI: Add zig 0.17 compiler tests\n\nAdds a zig-0.17 entry to the compiler matrices, sourced from\nnixpkgs-unstable, and drops zig 0.14 from ci.yml (still covered in\nlegacy-compilers).\n\nzig 0.17 fixes ziglang/zig#23576 (CPU-feature predefines such as\n__AVX2__ being dropped in assembler-with-cpp mode), so we now also\ntest the native backends and examples with it. The ABI check is\nskipped: on AArch64 it passes -march=armv8-a+simd and\n-march=armv8.4-a+sha3, which zig rejects since it parses -march as a\nCPU name.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T04:24:12Z",
          "tree_id": "20859022781f2a3b1b43a62bfbaa3e0f11668cb5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7155ef240925a0f5c554075e4b94885328760902"
        },
        "date": 1791703802891,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13118,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16810,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19315,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20653,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26153,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27947,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30188,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37425,
            "unit": "cycles"
          }
        ]
      }
    ],
    "ppc64le (POWER10) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "matthias@zerorisc.com",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": false,
          "id": "7155ef240925a0f5c554075e4b94885328760902",
          "message": "CI: Add zig 0.17 compiler tests\n\nAdds a zig-0.17 entry to the compiler matrices, sourced from\nnixpkgs-unstable, and drops zig 0.14 from ci.yml (still covered in\nlegacy-compilers).\n\nzig 0.17 fixes ziglang/zig#23576 (CPU-feature predefines such as\n__AVX2__ being dropped in assembler-with-cpp mode), so we now also\ntest the native backends and examples with it. The ABI check is\nskipped: on AArch64 it passes -march=armv8-a+simd and\n-march=armv8.4-a+sha3, which zig rejects since it parses -march as a\nCPU name.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T04:24:12Z",
          "tree_id": "20859022781f2a3b1b43a62bfbaa3e0f11668cb5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7155ef240925a0f5c554075e4b94885328760902"
        },
        "date": 1791703726031,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 38565,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 43433,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 53948,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 68752,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 77589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 91685,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 112760,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 123458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 141848,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton5": [
      {
        "commit": {
          "author": {
            "email": "matthias@zerorisc.com",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": false,
          "id": "7155ef240925a0f5c554075e4b94885328760902",
          "message": "CI: Add zig 0.17 compiler tests\n\nAdds a zig-0.17 entry to the compiler matrices, sourced from\nnixpkgs-unstable, and drops zig 0.14 from ci.yml (still covered in\nlegacy-compilers).\n\nzig 0.17 fixes ziglang/zig#23576 (CPU-feature predefines such as\n__AVX2__ being dropped in assembler-with-cpp mode), so we now also\ntest the native backends and examples with it. The ABI check is\nskipped: on AArch64 it passes -march=armv8-a+simd and\n-march=armv8.4-a+sha3, which zig rejects since it parses -march as a\nCPU name.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T04:24:12Z",
          "tree_id": "20859022781f2a3b1b43a62bfbaa3e0f11668cb5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7155ef240925a0f5c554075e4b94885328760902"
        },
        "date": 1791703831473,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13479,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15830,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21355,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25213,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33111,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33245,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 37063,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47123,
            "unit": "cycles"
          }
        ]
      }
    ]
  }
}