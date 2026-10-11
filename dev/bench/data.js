window.BENCHMARK_DATA = {
  "lastUpdate": 1791712829260,
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
      },
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
        "date": 1791703762080,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28213,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44500,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47593,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53841,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68493,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70177,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78569,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98283,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712310856,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28211,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34078,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44497,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47587,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53841,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68491,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70176,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78569,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98284,
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
      },
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
        "date": 1791705508434,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712374937,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11685,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13119,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16815,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19303,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20636,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26137,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27937,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30184,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37491,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712276867,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 38374,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 43160,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 53820,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 67389,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76239,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 90802,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 112829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 123504,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 142241,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712385739,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13478,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21356,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25211,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33108,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33245,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 37062,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47124,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Intel Xeon 4th gen (c7i) (no-opt)": [
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
        "date": 1791703979831,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35099,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44378,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 44510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53126,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67259,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 66650,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78174,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 93922,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712552333,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27735,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35095,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44398,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 44434,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53199,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67099,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 66638,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 93979,
            "unit": "cycles"
          }
        ]
      }
    ],
    "AMD EPYC 4th gen (c7a)": [
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
        "date": 1791703825381,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12789,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14256,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19004,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21617,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29785,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30584,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32906,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42060,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712373105,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12849,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14282,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19062,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21674,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22847,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29790,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30613,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32928,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42046,
            "unit": "cycles"
          }
        ]
      }
    ],
    "AMD EPYC 3rd gen (c6a)": [
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
        "date": 1791703819921,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14404,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15958,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21385,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23586,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25060,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32804,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33441,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 36121,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46363,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712369948,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14408,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15975,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21431,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23580,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25050,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32793,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33312,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35949,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46180,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton5 (no-opt)": [
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
        "date": 1791704016811,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27494,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 31889,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 40671,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 44276,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 50937,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 62628,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69020,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76035,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90615,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712572136,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27493,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 31899,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 40673,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 44277,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 50935,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 62632,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69027,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76031,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90618,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Intel Xeon 3rd gen (c6i)": [
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
        "date": 1791703817794,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20622,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27730,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31821,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 42900,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43456,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45899,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62679,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712369298,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20628,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27662,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31780,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 33143,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 42905,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43767,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45845,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62662,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton4": [
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
        "date": 1791703849690,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17663,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20534,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29860,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32689,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41903,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61367,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712401941,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17655,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20532,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27008,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29858,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41901,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48569,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61364,
            "unit": "cycles"
          }
        ]
      }
    ],
    "AMD EPYC 4th gen (c7a) (no-opt)": [
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
        "date": 1791704050863,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 36953,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 43019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 55763,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58423,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67098,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84147,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88561,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 99040,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120356,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712600853,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37093,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 43216,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56005,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58630,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67304,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84273,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88880,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 99559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120842,
            "unit": "cycles"
          }
        ]
      }
    ],
    "AMD EPYC 3rd gen (c6a) (no-opt)": [
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
        "date": 1791704061238,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39747,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 48056,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 61484,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 62654,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75245,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92520,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 95266,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 110087,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132885,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712610493,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39789,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 48106,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 61508,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 62637,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 74987,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92466,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 95228,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 110167,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132768,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Intel Xeon 3rd gen (c6i) (no-opt)": [
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
        "date": 1791704092787,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 48875,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57390,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 73427,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 77801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 89158,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 110786,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116106,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 131059,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157974,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712644904,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 48877,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 57360,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 73484,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 77738,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 89065,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 110736,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130947,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157881,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton4 (no-opt)": [
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
        "date": 1791704104832,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 40278,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 50996,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 57265,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 64571,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79093,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88060,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97343,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 116122,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712654236,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 40278,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 50996,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 57266,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 64581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79100,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88059,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97345,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 116125,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton3": [
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
        "date": 1791703889392,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18655,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28876,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31588,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34817,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44853,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46167,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51467,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65073,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712425865,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18656,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28877,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31591,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34819,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44865,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46161,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51462,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65071,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton3 (no-opt)": [
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
        "date": 1791704178383,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39304,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44843,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63042,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 71277,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87217,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96705,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106988,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127705,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712720763,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39299,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56665,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63025,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 71267,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87209,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96699,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106957,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127679,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton2": [
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
        "date": 1791703902671,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34109,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44468,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47604,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53830,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68514,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70201,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78576,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98295,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712446265,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28321,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34220,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44644,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47607,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70226,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78614,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98337,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Graviton2 (no-opt)": [
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
        "date": 1791704282179,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58606,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 67997,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 86917,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 94357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 108539,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 133556,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 149517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 163653,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197245,
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
          "id": "b2555cc5b02c0f74b2913d8d182e5fa5604108b0",
          "message": "HOL-Light: Don't report incomplete proof runs as OK\n\nThe `%.correct` rule only grepped the proof log for errors, so a proof\nkilled mid-run was reported as OK; also require the `Running time:`\nmarker that build-proof.sh prints after `check_axioms`.\n\nThis ports mldsa-native b215ba81.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-11T08:12:11Z",
          "tree_id": "557ea6f3edd0eecb6d999d43a59e4af321094b4b",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b2555cc5b02c0f74b2913d8d182e5fa5604108b0"
        },
        "date": 1791712828862,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58619,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 68009,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 86937,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 94275,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 108470,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 133472,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 149731,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 163989,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197593,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Arm Cortex-A72 (Raspberry Pi 4) benchmarks": [
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
        "date": 1791706524791,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 51346,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59565,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 76499,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 87126,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 95801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 119756,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 130338,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 142772,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 174525,
            "unit": "cycles"
          }
        ]
      }
    ]
  }
}