window.BENCHMARK_DATA = {
  "lastUpdate": 1791445361679,
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
    ]
  }
}