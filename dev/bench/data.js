window.BENCHMARK_DATA = {
  "lastUpdate": 1792876178071,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811364668,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34077,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44500,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47587,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68488,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70177,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98280,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844380633,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34078,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44495,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47589,
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
            "value": 70177,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78567,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98282,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060495434,
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
            "value": 47588,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68494,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70179,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98280,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213665119,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34076,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44496,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47589,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68495,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70190,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78566,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98281,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447292910,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34079,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47619,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68474,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78566,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98326,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501125288,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34079,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44529,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47618,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68470,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70154,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98325,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518124729,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44530,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47618,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68469,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98322,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596114944,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28250,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34081,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47619,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68473,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70148,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98326,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851083433,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44528,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47618,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68475,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98326,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875833556,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28251,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34081,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47619,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53841,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68474,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98326,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792062322687,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 647661,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 762080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 962748,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 1067411,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 1180399,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 1451597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 1595742,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 1748091,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 2095684,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792448771565,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 398781,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 513218,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 713958,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 669732,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 782707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 1053941,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 898976,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 1051351,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1398918,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792519594648,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 398857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 513294,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 714034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 669876,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 782851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 1054085,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 899202,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 1051577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1399144,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792818252870,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 398857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 513294,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 714034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 669876,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 782851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 1054085,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 899202,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 1051577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1399144,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792853607462,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 398857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 513294,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 714034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 669876,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 782851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 1054085,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 899202,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 1051577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 1399144,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811418627,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19302,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20638,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27926,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30257,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37494,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844424940,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11686,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13127,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16812,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19316,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20670,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26145,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27967,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30218,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37549,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060529514,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13117,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16818,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19312,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20639,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26131,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27926,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30199,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37452,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213719996,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11679,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13111,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16804,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19297,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20628,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26125,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27920,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30182,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37532,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447345795,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11653,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13065,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19295,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20646,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26190,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27923,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30178,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37522,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501177380,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11645,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13063,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19299,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20655,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26179,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27918,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30178,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37525,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518171268,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11653,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13080,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16869,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19312,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20655,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26205,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27925,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30178,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37555,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596165661,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11656,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13073,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16859,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19317,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20657,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26195,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27931,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30188,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37548,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851130753,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11658,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13072,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16866,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19300,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20637,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26184,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27929,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30171,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37558,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875881962,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 11658,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 13069,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 16859,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 19302,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 20625,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 26200,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 27963,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 30204,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 37545,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811330566,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39197,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46785,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56962,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 69116,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76338,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 91460,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 110761,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 121558,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 139995,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844355297,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39274,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56808,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 70307,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 77612,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92919,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 112862,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 123465,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 143351,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060490956,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39429,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46967,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57108,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 69751,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 77489,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92319,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 111416,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 122182,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 141485,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213634235,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39164,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46735,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57039,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 69014,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76450,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 91273,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 111112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 122054,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 140972,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447262824,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39101,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46508,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56676,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 70321,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 77843,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92940,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 111181,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 121886,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 141016,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501094244,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46383,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56640,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 68934,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76130,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 91107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 110959,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 121784,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 140918,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518090758,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39065,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46436,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56347,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 68939,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76309,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 91283,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 110254,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 120808,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 139955,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596084623,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 38891,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46496,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56734,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 68788,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76012,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 90998,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 110316,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 120954,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 139954,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851047325,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39061,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46421,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56742,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 68819,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76120,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 90929,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 109800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 120451,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 139221,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875802187,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39075,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46528,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 56702,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 69596,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 76825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 91865,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 112086,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 123134,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 141902,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811451597,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13478,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15830,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22880,
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
            "value": 33244,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 37063,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47122,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844452842,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13478,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15830,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21356,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22880,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33241,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 37059,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47120,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060572400,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13477,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15831,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22880,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25210,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33106,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33244,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 37058,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47124,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213751114,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13478,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15831,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21355,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22882,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25211,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33107,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33241,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 37059,
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
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447362167,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13432,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15816,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21335,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22867,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25292,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33168,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33302,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 36978,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47117,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501208620,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13433,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21341,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22869,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25291,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33167,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33301,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 36975,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47113,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518217846,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13432,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15820,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21337,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22867,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25291,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33168,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33304,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 36978,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47118,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596202845,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13434,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21343,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22870,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25295,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33172,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33303,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 36981,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47122,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851155925,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13433,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15820,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21339,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22869,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25296,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33173,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33303,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 36978,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47119,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875923719,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 13432,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15821,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21341,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 22871,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25294,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 33169,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33302,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 36979,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 47119,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811597050,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28314,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45407,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46550,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55352,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67682,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69634,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81085,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96815,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844602944,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28350,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35439,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45468,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46540,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55333,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67657,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69656,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81136,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96758,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060708325,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28283,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35326,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45385,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46580,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55319,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67645,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69622,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81134,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96816,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213897990,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28310,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35292,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45335,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46555,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55363,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67754,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69651,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81091,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96681,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447524332,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28264,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35311,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45402,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46593,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55270,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67639,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69396,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81093,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96558,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501356512,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28285,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35364,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45382,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46646,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55359,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67736,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69553,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81152,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96580,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518350322,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28288,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35292,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45367,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46622,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55274,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67636,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69491,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81060,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96520,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596345020,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28292,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35305,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45367,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46562,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55353,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67681,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69500,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81081,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96560,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851311122,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28281,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45420,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46609,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55242,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67638,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81125,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96556,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792876060004,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28363,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 35250,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 45364,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46610,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 55334,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 67677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69565,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 81129,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 96504,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811427818,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12858,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14277,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19046,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21586,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22806,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29706,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30512,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32806,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 41977,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844445501,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12823,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14247,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 18994,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21582,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22764,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29722,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30480,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32709,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 41784,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060557947,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12813,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14224,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 18954,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21601,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22747,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30488,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32681,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 41791,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213734527,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12852,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14280,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19048,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21635,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22831,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29923,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30606,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32991,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42052,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447365375,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12865,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14278,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21670,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22867,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29783,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30550,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32759,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42052,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501192919,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12866,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14270,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21667,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22812,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29754,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30564,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32755,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42074,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518188732,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12856,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14280,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19042,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21650,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22815,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29767,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30602,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32727,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42067,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596180603,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12868,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14314,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19047,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21640,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22812,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29761,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30549,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32744,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42051,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851142226,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12868,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14301,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19037,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21644,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22818,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30553,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32722,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 42029,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875901530,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12860,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14288,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19042,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21655,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 22829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 29765,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30475,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 32620,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 41963,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811429704,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14401,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21387,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23595,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25065,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32821,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33461,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35997,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46193,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844439742,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14392,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15933,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21361,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23580,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25042,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32787,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33316,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35959,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46190,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060545554,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14401,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15953,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21363,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25050,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32786,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33314,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35956,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46187,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213722527,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14396,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15932,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21350,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25056,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32802,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33323,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35990,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46185,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447359699,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14454,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21389,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23604,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25075,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32797,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33277,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35978,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46224,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501184380,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14447,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15937,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21382,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23599,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25044,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32776,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33306,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35945,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46161,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518190909,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14446,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15907,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21369,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23601,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25055,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32793,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33256,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35936,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46147,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596179789,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14466,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15944,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21381,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23596,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25046,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32795,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33279,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35946,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46175,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851140683,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14457,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15949,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21400,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25064,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32810,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33341,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35990,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46203,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875897677,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 14458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 15941,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 21382,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 23600,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 25050,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 32804,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 33270,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 35948,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 46176,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811636098,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27578,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 33028,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41935,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 45400,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51720,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63300,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69207,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 75864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90539,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844639769,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27574,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 33030,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41936,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 45405,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51722,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63300,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69195,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 75862,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90529,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060756743,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27568,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 33027,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41932,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 45408,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51730,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63306,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69227,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 75872,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90547,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213937948,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27579,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 33033,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41932,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 45433,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51743,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63328,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 69214,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 75874,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90540,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447550085,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27547,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 32947,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41860,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46730,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51416,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 68200,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76563,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90907,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501395361,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27557,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 32950,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41866,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51421,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63761,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 68202,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90916,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518401344,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27551,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 32945,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41860,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46730,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51414,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63745,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 68207,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76568,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90913,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596394021,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27551,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 32947,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41865,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46732,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51417,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63739,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 68212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76568,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90923,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851340248,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27555,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 32948,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41863,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46732,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51417,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63755,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 68205,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90914,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792876110025,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 27559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 32948,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 41869,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 46729,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 51413,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 63748,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 68212,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 76562,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 90919,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811425786,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18357,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20620,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27654,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 32279,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32291,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 42883,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43462,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45748,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62044,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844444292,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18380,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20634,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27679,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32981,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 42904,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43548,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62529,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060546436,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18384,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20638,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27726,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 32316,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 33019,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 42910,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43746,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45872,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62621,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213723441,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18370,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20638,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27668,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31518,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 33537,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 42917,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 44139,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45936,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62695,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447357671,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18351,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20622,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31711,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32287,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 43041,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43482,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 46839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62632,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501187340,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18355,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20620,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27723,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31658,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32591,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 43034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 46297,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62502,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518189194,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18346,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20636,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27727,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 32057,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32139,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 43049,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 44989,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45855,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62471,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596175349,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18349,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20630,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27728,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31674,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32254,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 43057,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43890,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45854,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62414,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851138440,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18347,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20624,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31630,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 43023,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43954,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 46485,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62339,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875892890,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18349,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20628,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31033,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32101,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 43034,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 44934,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 45770,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 62325,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811486926,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20539,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27010,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29855,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32689,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41906,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48572,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61364,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844473913,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20530,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27000,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29865,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32692,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41909,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48584,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61366,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060588985,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17661,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20521,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27001,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29860,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32695,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41913,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43687,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61366,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213781274,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27007,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29866,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32694,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41913,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43692,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48574,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61382,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447392379,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17684,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27032,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29828,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32711,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41838,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48641,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61340,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501265486,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17700,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20547,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27028,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32705,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43672,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48647,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61340,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518222678,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17686,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20538,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27027,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29824,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32705,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43672,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48635,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61338,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596228926,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17689,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20534,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27027,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32707,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43670,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48636,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61336,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851201687,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17679,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27018,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29824,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32696,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43671,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48643,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61337,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875922532,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 17695,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 20533,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 27029,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 29823,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 32708,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 41845,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 43668,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 48632,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 61336,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811655538,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 36987,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44339,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57090,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59740,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88276,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98866,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120323,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844670865,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37076,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59871,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67953,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84836,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88577,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98942,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120471,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060787458,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37079,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44468,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57258,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 60009,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67780,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84658,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88236,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120092,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213963233,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37109,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44516,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57340,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59722,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67727,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88335,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98898,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120323,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447591547,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 36978,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44322,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57081,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59677,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67609,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84682,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88326,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98768,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120028,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501420426,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37138,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44539,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57356,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59898,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84782,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88312,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98689,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120343,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518416093,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37099,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57310,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59974,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67957,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84971,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88613,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 99101,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120823,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596410065,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37093,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44509,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57308,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59976,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67973,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84964,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88585,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 99074,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120603,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851367202,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37021,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44402,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57179,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59688,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67631,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84714,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88331,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98709,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120226,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792876129761,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 37053,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 44459,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 57246,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 59723,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 67685,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 84646,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88273,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 98780,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 120404,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811670910,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39704,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49601,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62941,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63978,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 93070,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94880,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109674,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132708,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844680101,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39668,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49567,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62887,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75456,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92963,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94828,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109585,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132434,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060787427,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39652,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49551,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62873,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63934,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75491,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92988,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109604,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132341,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213963856,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49519,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62833,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63919,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75452,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92939,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94768,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109525,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132289,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447602392,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39673,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49545,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62875,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63925,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 93059,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94861,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109570,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132286,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501425545,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39623,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49506,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63904,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75407,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 93017,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 95106,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109886,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132634,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518434548,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39597,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49443,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62776,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63905,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75459,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 93082,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 95010,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109715,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132909,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596423209,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39625,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49483,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62813,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75591,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92927,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94982,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109657,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132399,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851384904,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39709,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62916,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63974,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 93117,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94931,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109947,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132479,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792876141485,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39620,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 49491,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 62837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 63860,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 75381,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 92951,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 94911,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 109632,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 132355,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811700679,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49119,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59681,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75452,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80193,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90603,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111526,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116382,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130938,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157689,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844719512,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49161,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59690,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75422,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80237,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90668,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111546,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116407,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130867,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157658,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060823050,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49168,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59716,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75521,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80236,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111616,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116328,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130901,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157727,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792214000225,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49222,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75527,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80185,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90663,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111603,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116342,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130979,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157703,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447635556,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49194,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59734,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75573,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80442,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90753,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111726,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116381,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130972,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157841,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501468707,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49205,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75487,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80263,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90638,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111512,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116310,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130905,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157691,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518466511,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49213,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59705,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75523,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80368,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90766,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111648,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116369,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 131087,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157798,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596454623,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49187,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75485,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80399,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90754,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111690,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130831,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157711,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851416682,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49303,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75691,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80483,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90916,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111886,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116513,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 131319,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 158323,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792876168516,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 49142,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59698,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75465,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 80326,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 90684,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 111649,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 116246,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 130833,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 157623,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811738791,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35505,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58812,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 64881,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 87937,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97221,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115996,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844730503,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41832,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58809,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 64870,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79460,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 87946,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97237,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 116013,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060844508,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35506,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41832,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52509,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 64878,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79459,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 87937,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97222,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115995,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792214034730,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35508,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41836,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52515,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 64869,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79446,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 87936,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97222,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 116013,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447647293,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35461,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41768,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52519,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58717,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 65032,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88174,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115614,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501520800,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35463,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41769,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52516,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58715,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 65057,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79384,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88177,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97128,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115619,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518479142,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35463,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41772,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52518,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 65062,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79377,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88173,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97117,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115624,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596480431,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35462,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41768,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58719,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 65061,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79376,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88178,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97128,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115617,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851455236,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35462,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41768,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52521,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58721,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 65047,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79383,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88174,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97128,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115624,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792876177736,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 35460,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 41764,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 52514,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 58718,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 65062,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 79383,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 88169,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 97118,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 115608,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811470273,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18658,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21856,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28879,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31593,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34820,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44859,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46165,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51466,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65069,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844504622,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18660,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28879,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31585,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34810,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44852,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46158,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65064,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060622284,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18657,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21851,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28872,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31587,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34813,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44857,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46157,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65063,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213771370,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18652,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21846,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28867,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31583,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34807,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44846,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46155,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51457,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65067,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447419613,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18676,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21855,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28903,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31551,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34812,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46128,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51513,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65015,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501237833,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18679,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21862,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28911,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31548,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34813,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44803,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46137,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51523,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65037,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518242375,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18681,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21859,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28908,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31550,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44784,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46133,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51521,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65034,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596269360,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18682,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21858,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28913,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31559,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34818,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44797,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46132,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65022,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851206395,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21856,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28907,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31547,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34807,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44789,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46120,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65018,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875937686,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 18684,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 21861,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 28913,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 31546,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 34811,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 44785,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 46124,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 51510,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 65015,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811769332,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39246,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46482,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58283,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64735,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 71845,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87778,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96617,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106973,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127600,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844797838,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39250,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46506,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58308,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64715,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 71824,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87767,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96575,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106980,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127604,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060911007,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39244,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46495,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58293,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64736,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 71831,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87790,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96573,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106975,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127599,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792214070688,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39235,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46478,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58276,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64695,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 71823,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87748,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96556,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106929,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127558,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447719077,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39231,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46453,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58402,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64680,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 72157,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87746,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96841,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106839,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127172,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501534256,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39219,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46444,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58385,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64645,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 72149,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87730,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96862,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127172,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518535730,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39226,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46448,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58394,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64652,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 72150,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87737,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96874,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127166,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596570218,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39213,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46441,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58384,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64663,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 72146,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87740,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96834,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106825,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127161,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851502644,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 39226,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 46466,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 58409,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 64679,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 72174,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 87757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 96837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 106845,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 127187,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811499432,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34110,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44470,
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
            "value": 68518,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70198,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78581,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98293,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844513603,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34111,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44471,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47604,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53829,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68514,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70197,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78573,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98291,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792060640856,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44473,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47606,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53831,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68523,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70201,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78583,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98303,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792213800894,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28229,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34111,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44470,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47602,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53830,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68517,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70200,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78572,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98291,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447424863,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28263,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34076,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47625,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53838,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68473,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70163,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78640,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98243,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501261503,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28264,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34075,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47624,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53840,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68470,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70234,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78752,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98420,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518290987,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28265,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34079,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44533,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47626,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53843,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68480,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70165,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78640,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98247,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596284472,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28269,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34079,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44534,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47625,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68476,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70163,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78641,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98238,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851218089,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 28267,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 34076,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 44531,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 47650,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 53870,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 68541,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 70157,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 78633,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 98233,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811881589,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58264,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70507,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89377,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 96838,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109796,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134838,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150402,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164553,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197998,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844893634,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58184,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70497,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89426,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 96746,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109706,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134745,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150087,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164271,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197589,
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
          "id": "7da6bd118a948b0f029deaf712b5c16c63e37d62",
          "message": "sys.h: Do not depend on configuration options\n\nsys.h evaluated MLK_CONFIG_NO_ASM, MLK_CONFIG_CT_TESTING_ENABLED and\nMLK_CONFIG_CUSTOM_CAPABILITY_FUNC when it was first included.\nConfiguration hooks such as MLK_CONFIG_CUSTOM_ZEROIZE include sys.h,\nand its include guard prevents re-evaluation, so an option defined\nafter such a hook was silently ignored or, for the capability function,\ncaused a redefinition error. This affects the order of the config\ntemplate and test/configs/no_asm_config.h: the \"No ASM\" configuration\nkept the inline-assembly value barrier and never built the volatile\nopt-blocker, and a late CT_TESTING_ENABLED made constant-time tests\nvacuous.\n\nMove the inline-assembly decision and the CT-testing macros to\ncommon.h, after the whole configuration has been read. Move the default\nmlk_sys_check_capability() to a new shared header capability.h,\nincluded from common.h, so that multilevel builds still define it only\nonce. Document in sys.h that it must not depend on configuration\noptions.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-15T09:03:02Z",
          "tree_id": "0d57b47ac8d8245791ffbcb836dbca81e5c3dc79",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/7da6bd118a948b0f029deaf712b5c16c63e37d62"
        },
        "date": 1792061022137,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58249,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70492,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89371,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 96853,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109801,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134842,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150199,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164402,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197762,
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
          "id": "eae4179cd5fc71cf2fef378a1b812cfe841fab35",
          "message": "Fix inaccurate comments and documentation\n\nFix swapped FIPS 203 algorithm numbers in the frommsg/tomsg docs, wrong\nline references for e2 sampling, a stale sentence on poly_tobytes, the\nreference-implementation citation for mlk_ct_memcmp, the missing init\nfunctions in FIPS202.md, and the memset note in STDLIB.md.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-17T03:49:16Z",
          "tree_id": "60f1a4e6fe75e1813a0953d52bedcc9489c4ffbb",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/eae4179cd5fc71cf2fef378a1b812cfe841fab35"
        },
        "date": 1792214183921,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58249,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70513,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89389,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 96864,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109800,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134822,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150259,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164442,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197752,
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
          "distinct": true,
          "id": "d8cc522a8ed905466a5109bae97e4661ef80cf22",
          "message": "Test: Run ABI checks as Zephyr applications\n\nThe ABI-check target bypassed the custom platform build path and linked\nan executable directly with $(LD). Under Zephyr that produced a host\nexecutable, which was then handed to Arm QEMU and faulted at startup.\n\nRoute the ABI-check target through the existing $(LINK)/CUSTOM_BUILD\nmechanism, so the ABI driver, self-tests, generated checks, and\nArmv8.1-M assembly sources build as a standalone Zephyr application.\nSelect armv81m explicitly for mps3-an547 rather than inferring it from\nthe generic arm-none-eabi compiler prefix, and reject ABI-check requests\nfor other Zephyr targets explicitly. Preserve OPT and AUTO when\nscripts/tests invokes a run target, so the run step no longer re-enters\nthe makefiles under a platform's own OPT default.\n\nTrack OPT, the selected FIPS202 backend, and the now-configurable test\ncounts in the active build marker so changes to those inputs rebuild\nstale Zephyr binaries, name the native assembly amalgamation as an\nexplicit dependency, and allow QEMU execution timeouts to be overridden.\n\nPorts pq-code-package/mldsa-native#1318.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-19T19:29:29Z",
          "tree_id": "5945ee18a8890ce81d74d6ad1506e0b9a43d0bfa",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/d8cc522a8ed905466a5109bae97e4661ef80cf22"
        },
        "date": 1792447806104,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58270,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70482,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89241,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 96959,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109676,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134631,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150781,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164817,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 198478,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": true,
          "id": "a7914d44f2321b9422ba853c952cb4f3391ea964",
          "message": "CI: Enable unit tests on all Zephyr targets\n\nZephyr CI runs ML-KEM tests on five emulated Arm boards, but skips\nthe unit suite. Those checks therefore do not run in these jobs.\n\nEnable unit tests for every board in the existing matrix. Keep the\ncurrent OPT modes: Cortex-M55 runs portable and MVE builds, and the\nother boards run portable builds. Leave other test selections and\nstack sizes unchanged.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T11:37:55Z",
          "tree_id": "f4feaac10b3344830f0737da72e15bd5a522a8d5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/a7914d44f2321b9422ba853c952cb4f3391ea964"
        },
        "date": 1792501641207,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58295,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70516,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89264,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 97099,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109763,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134670,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164511,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197892,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "distinct": true,
          "id": "b9550181de754f798941b8a4f495f8a9b8b5e3ec",
          "message": "PPC64: Align backend selection and ABI feature guards\n\nThe PPC64 ABI checker registered kernels whenever the target was\nPPC64LE, while the kernels require POWER8 vector support. Removing the\nchecker's forced assembly flags would leave checks referring to kernels\nomitted by the build's CPU flags.\n\nAdd `MLK_SYS_PPC64LE_POWER8_VECTOR`, requiring `__ALTIVEC__`, `__VSX__`,\nand `__POWER8_VECTOR__` on PPC64LE. Use it to select the default PPC64\nbackend in `native/meta.h`, as for the NEON and AVX2 backends.\nUnsupported targets then use portable C without selecting the native\nwrappers.\n\nRemove the per-kernel and constant-table `__POWER8_VECTOR__` guards and\nthe wrappers' compile-time fallback branches. Explicitly selecting the\nPPC64 backend now requires a target with its documented features,\nmatching the other backends.\n\nThe PPC64 wrappers previously checked only `__POWER8_VECTOR__` at\ncompile time, so a custom capability function could not disable them at\nruntime. Append `MLK_SYS_CAP_PPC64LE_POWER8_VECTOR` and have all four\nwrappers consult the capability hook before calling assembly. Return\n`MLK_NATIVE_FUNC_FALLBACK` without modifying the input if it rejects\nPOWER8 vector support.\n\nUse the same feature macro for the generated ABI checks, registry, call\nstub and self-test. Name the ABI feature `POWER8_VECTOR` and consult the\ncapability hook before calling assembly from ABI checks or the\nself-test.\n\nCorrect the backend READMEs from POWER9 to POWER8 and state the AltiVec\nand VSX requirement. The default capability hook assumes compile-time\nfeatures are supported; runtime detection requires a custom function.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-20T16:11:56Z",
          "tree_id": "338e3d87e2fcd142f599f4a3dbd8d1f6b4e6a9b8",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/b9550181de754f798941b8a4f495f8a9b8b5e3ec"
        },
        "date": 1792518671459,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58230,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70526,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89329,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 96967,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109666,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134547,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 149963,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164452,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197751,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792596673919,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58296,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70505,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 97098,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109769,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134664,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150070,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164541,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197900,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851465427,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 58292,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70506,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89247,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 97046,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 109746,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 134648,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 150112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 164523,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 197893,
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
          "id": "aad9b745c7447ac8022cbee3c40df73c13880d9f",
          "message": "FIPS202: Apply MLK_INTERNAL_API to the FIPS202 layer\n\nThe FIPS202 functions lacked MLK_INTERNAL_API, so single-CU builds with\nMLK_CONFIG_INTERNAL_API_QUALIFIER=static still exported them.\n\nOnce static, they\nalso need precise guards so that configurations not using them do not\ntrip -Wunused-function.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T11:58:17Z",
          "tree_id": "07ae0317323b9ff580cc211073058ea701b3af7f",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/aad9b745c7447ac8022cbee3c40df73c13880d9f"
        },
        "date": 1791811526970,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 51306,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59407,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75434,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 86327,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 94649,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118194,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 130749,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 143525,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 174590,
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
          "id": "c2827a8e8be4cd09b20dfe3544fe854777bcaefb",
          "message": "SOUNDNESS: State the scope of the constant-time tests\n\nThe valgrind constant-time tests only run on x86_64 and AArch64 in\nthe default configuration.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-12T21:01:07Z",
          "tree_id": "2428da4c26c9bd8adbf509f8345fa21898dab533",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/c2827a8e8be4cd09b20dfe3544fe854777bcaefb"
        },
        "date": 1791844538093,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 51315,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59313,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 75528,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 86169,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 94238,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118724,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 130267,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 142905,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 175003,
            "unit": "cycles"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792818757545,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 51529,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59389,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 76158,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 87519,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 96960,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118318,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 131631,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 143538,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 174880,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851242017,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 51375,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 59104,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 76683,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 87122,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 95335,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 118409,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 132888,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 143874,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 176949,
            "unit": "cycles"
          }
        ]
      }
    ],
    "SpacemiT K1 8 (Banana Pi F3) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792815646018,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 143396,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 159976,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 198236,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 242458,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 255194,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 309968,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 366901,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 388770,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 460832,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792854433246,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 143374,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 159939,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 198266,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 242397,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 255110,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 309915,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 366310,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 389243,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 459641,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Arm Cortex-A55 (Snapdragon 888) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792818507051,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59781,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70502,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89522,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 100895,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 112932,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 140591,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 154785,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 172372,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 208629,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792853854781,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 59798,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 70566,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 89524,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 100931,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 112747,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 139827,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 155066,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 171292,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 208177,
            "unit": "cycles"
          }
        ]
      }
    ],
    "Mac Mini (M1, 2020) benchmarks": [
      {
        "commit": {
          "author": {
            "email": "beckphan@amazon.co.uk",
            "name": "Hanno Becker",
            "username": "hanno-becker"
          },
          "committer": {
            "email": "matthias@kannwischer.eu",
            "name": "Matthias J. Kannwischer",
            "username": "mkannwischer"
          },
          "distinct": false,
          "id": "e2d4b50896c76ada9950de2855dcd6069789e74e",
          "message": "CI: Enable ABI checks in the Zig 0.17 jobs\n\nThe Zig 0.17 jobs skip ABI checks because the checker previously added\nAArch64 `-march` flags which Zig parses as CPU names. The checker now\nuses the platform's CPU flags, so that restriction no longer applies.\n\nRemove `--no-abicheck` from the Extended compiler matrix and the Linux\nand macOS legacy matrices. Drop the comments about the old `-march`\nflags.\n\nSigned-off-by: Hanno Becker <beckphan@amazon.co.uk>",
          "timestamp": "2026-10-21T14:01:28Z",
          "tree_id": "9aa3a4ff1dd1ee167dc89b6ebd7e54c7d65f28e5",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e2d4b50896c76ada9950de2855dcd6069789e74e"
        },
        "date": 1792823727149,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12380,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14837,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19409,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21366,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 23612,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 30195,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30446,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 34247,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 43885,
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
          "distinct": true,
          "id": "e32e3688066806d683fe6a31b22777a0ee746c3b",
          "message": "README: List PyCryptodome as a consumer\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T12:51:07Z",
          "tree_id": "2aced513cff8e1ad3eafa2e924b1da1f7e8c3666",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/e32e3688066806d683fe6a31b22777a0ee746c3b"
        },
        "date": 1792851038618,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12316,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14755,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19310,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21256,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 23483,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 30025,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30333,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 34113,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 43666,
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
          "distinct": true,
          "id": "8898866e9f134db2f7d73e6aa7761c77a697cfe2",
          "message": "CBMC: Use a second solver for 157/190 proofs\n\nA soundness bug in a single SMT solver would silently invalidate every\nproof discharged by it. To mitigate this risk, we aim to have each\nproof discharged by at least two solvers.\n\n157 of 190 proofs gain a second solver: 82 bitwuzla, 3\ncvc5_arrays_exp, and 72 Z3 profiles alongside a z3 or bitwuzla\ndefault. Of the others, one already runs with several solvers and\n32 do not get a second one, mostly because bitwuzla timed out or\ncvc5 returned unknown under a local 300s per-proof cap for\nMLKEM_K=2, 3, or 4.\n\nSigned-off-by: Matthias J. Kannwischer <matthias@zerorisc.com>",
          "timestamp": "2026-10-24T19:51:41Z",
          "tree_id": "7d205ced9a05110355f8f495b9409978ed717041",
          "url": "https://github.com/pq-code-package/mlkem-native/commit/8898866e9f134db2f7d73e6aa7761c77a697cfe2"
        },
        "date": 1792875793038,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "ML-KEM-512 keypair",
            "value": 12318,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 encaps",
            "value": 14757,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-512 decaps",
            "value": 19313,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 keypair",
            "value": 21255,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 encaps",
            "value": 23483,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-768 decaps",
            "value": 30027,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 keypair",
            "value": 30332,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 encaps",
            "value": 34112,
            "unit": "cycles"
          },
          {
            "name": "ML-KEM-1024 decaps",
            "value": 43665,
            "unit": "cycles"
          }
        ]
      }
    ]
  }
}