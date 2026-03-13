[//]: # (SPDX-License-Identifier: CC-BY-4.0)

mlkem-native ChangeLog
======================

= mlkem-native xxxx-xx-xx (since v1.0.0)

**Security**
   * Zeroize pkpv in `mlk_indcpa_keypair_derand()` and `mlk_indcpa_enc()`,
     which was previously left on the stack after use. [#1328](https://github.com/pq-code-package/mlkem-native/pull/1328)
   * Mark the stack as non-executable in all assembly files via
     `.note.GNU-stack` section markers. [#1340](https://github.com/pq-code-package/mlkem-native/pull/1340)
   * Make the value barrier volatile to prevent compilers from optimizing
     it away, strengthening the constant-time countermeasure. This is a purely
     preventative measure; no insecure compilations of the previous value barrier
     have been noted. [#1342](https://github.com/pq-code-package/mlkem-native/pull/1342)
   * Zeroize pk and sk buffers on keypair generation failure (e.g. when
     the pairwise consistency test fails due to OOM), to prevent leaking
     partial key material on API misuse. [#1559](https://github.com/pq-code-package/mlkem-native/pull/1559)
   * Fix a 4-byte buffer overread in x86_64 rejection sampling assembly.
     The overread was within the stack frame and the excess bytes were
     not acted on, but the read itself exceeded the nominal buffer
     bounds. Found while working on the corresponding memory-safety proof.
     [#1615](https://github.com/pq-code-package/mlkem-native/pull/1615)

**API changes**
   * Add `MLK_CONFIG_CUSTOM_MEMCPY` and `MLK_CONFIG_CUSTOM_MEMSET` options
     to allow replacement of `memcpy` and `memset`, following the same
     mechanism used for `zeroize` and `randombytes`. [#1105](https://github.com/pq-code-package/mlkem-native/pull/1105)
   * Add `MLK_CONFIG_NO_RANDOMIZED_API` option to build only the
     deterministic (_derand) API, omitting functions that require
     `randombytes()`. [#1185](https://github.com/pq-code-package/mlkem-native/pull/1185)
   * Add `mlk_kem_check_pk()` and `mlk_kem_check_sk()` to the public API,
     implementing the FIPS 203 modulus check (Section 7.2) and hash
     check (Section 7.3) respectively. [#1216](https://github.com/pq-code-package/mlkem-native/pull/1216)
   * Add `MLK_CONFIG_SERIAL_FIPS202_ONLY` option to disable 4x-batched
     FIPS-202 operations, allowing use of a simpler serial-only
     FIPS-202 backend. [#1231](https://github.com/pq-code-package/mlkem-native/pull/1231)
   * Add `MLK_CONFIG_NO_ASM_VALUE_BARRIER` to allow disabling the
     assembly-based value barrier at compile time. [#1325](https://github.com/pq-code-package/mlkem-native/pull/1325)
   * Move the configuration file from `mlkem/src/config` to
     mlkem/`mlkem_native_config.h`, and derive the public header
     configuration from it. [#1352](https://github.com/pq-code-package/mlkem-native/pull/1352)
   * Add `MLK_CONFIG_CUSTOM_ALLOC_FREE` option to allow consumers to
     provide custom allocation and deallocation functions for large
     internal structures, enabling use on systems with limited stack
     space. [#1389](https://github.com/pq-code-package/mlkem-native/pull/1389)
   * Add C++ compatibility to the public header `mlkem_native.h` by
     wrapping declarations in `extern "C"`. [#1465](https://github.com/pq-code-package/mlkem-native/pull/1465)
   * Remove the SUPERCOP API (`crypto_kem_keypair`, `crypto_kem_enc`,
     `crypto_kem_dec`) from `kem.[ch]`. The public API in `mlkem_native.h`
     is now the sole entry point. [#1470](https://github.com/pq-code-package/mlkem-native/pull/1470)
   * Add a context parameter to the KEM API functions, following the
     pattern established in FIPS 203. [#1467](https://github.com/pq-code-package/mlkem-native/pull/1467)
   * Add per-operation `MLK_TOTAL_ALLOC` constants to `mlkem_native.h`,
     indicating peak memory consumption for each KEM operation and
     parameter set when custom allocation is used. [#1468](https://github.com/pq-code-package/mlkem-native/pull/1468)
   * Add failure mode support for `randombytes()`: the RNG callback may
     now return an error code, which is propagated through the KEM API.
     [#1331](https://github.com/pq-code-package/mlkem-native/pull/1331)

**Features**
   * Add stack usage measurement support using GCC `-fstack-usage` and
     `valgrind`/`DHAT`. [#1102](https://github.com/pq-code-package/mlkem-native/pull/1102)
   * Add code size measurement integrated into the test script. [#1089](https://github.com/pq-code-package/mlkem-native/pull/1089)
   * Add compile-time compiler and host platform feature detection to
     the Makefile. [#1146](https://github.com/pq-code-package/mlkem-native/pull/1146)
   * Add runtime dispatch mechanism based on a custom CPU capabilities
     function, allowing backends to be selected at runtime based on
     detected CPU features. Extends to both arithmetic and FIPS-202
     backends. [#1152](https://github.com/pq-code-package/mlkem-native/pull/1152)
   * Add CFI (Call Frame Information) directives to all assembly
     functions for improved debugger support. [#1166](https://github.com/pq-code-package/mlkem-native/pull/1166)
   * Add unit test framework for testing internal functions (NTT, INTT,
     polynomial operations, rejection sampling, Keccak) with native
     backend consistency checks. [#1188](https://github.com/pq-code-package/mlkem-native/pull/1188)
   * Add RISC-V RVV (Vector Extension 1.0) native backend, providing
     vectorized NTT, inverse NTT, polynomial arithmetic, and rejection
     sampling for rv64gcv targets. Supports arbitrary vector lengths
     with automatic fallback to C for unsupported VLEN. [#1037](https://github.com/pq-code-package/mlkem-native/pull/1037)
   * Add test exercising top-level API with unaligned input buffers.
     [#1241](https://github.com/pq-code-package/mlkem-native/pull/1241)
   * Add initial Armv8.1-M+MVE native backend for Cortex-M55 and
     similar targets, including baremetal build support for the MPS3
     AN547 platform. [#1220](https://github.com/pq-code-package/mlkem-native/pull/1220)
   * Add baremetal environment for AVR (ATmega128RFR2) to test
     correctness on 16-bit integer platforms. [#1245](https://github.com/pq-code-package/mlkem-native/pull/1245)
   * Add allocation failure testing with a bump allocator that can be
     configured to fail at specific invocations. [#1424](https://github.com/pq-code-package/mlkem-native/pull/1424)
   * Add PMU cycle counting support for Armv8.1-M targets. [#1514](https://github.com/pq-code-package/mlkem-native/pull/1514)
   * Add MVE Keccak-f1600 x4 implementation for Armv8.1-M using
     bit-interleaved state representation. [#1518](https://github.com/pq-code-package/mlkem-native/pull/1518)
   * Add RNG failure test to verify correct error propagation when
     `randombytes()` fails. [#1331](https://github.com/pq-code-package/mlkem-native/pull/1331)
   * Add hol-server for programmatic HOL-Light communication, enabling
     interactive proof development. [#1500](https://github.com/pq-code-package/mlkem-native/pull/1500)
   * Add `.size` directives to all assembly functions on x86_64, AArch64,
     and Armv8.1-M for better tooling support. [#1552](https://github.com/pq-code-package/mlkem-native/pull/1552)
   * Add native Keccak x4 XORBytes and ExtractBytes interface for
     Armv8.1-M MVE. [#1524](https://github.com/pq-code-package/mlkem-native/pull/1524)
   * Replace x86_64 Keccak-f1600 x4 C intrinsics implementation with
     formally verified AVX2 assembly from s2n-bignum. [#1576](https://github.com/pq-code-package/mlkem-native/pull/1576)
   * Add `SOUNDNESS.md` documenting the scope, assumptions, and
     limitations of the formal verification effort. [#1582](https://github.com/pq-code-package/mlkem-native/pull/1582)
   * Add Wycheproof test suite infrastructure and scripts for ML-KEM
     test vector validation. [#1588](https://github.com/pq-code-package/mlkem-native/pull/1588)

**Bugfix**
   * Fix Makefile to use `shasum` instead of `sha256sum` for macOS
     compatibility. [#1131](https://github.com/pq-code-package/mlkem-native/pull/1131)
   * Fix Makefile to not use .WAIT primitive, restoring compatibility
     with make versions before 4.4. [#1198](https://github.com/pq-code-package/mlkem-native/pull/1198)
   * Fix little-endian detection when compiling with MSVC. [#1309](https://github.com/pq-code-package/mlkem-native/pull/1309)
   * Fix global CFLAGS setting that broke benchmarking. [#1327](https://github.com/pq-code-package/mlkem-native/pull/1327)
   * Fix pointer cleanup on dynamic allocation failure: previously, a
     failed allocation could lead to a null pointer dereference during
     cleanup. [#1402](https://github.com/pq-code-package/mlkem-native/pull/1402)
   * Fix `__attribute__` usage in `sys.h` for non-GCC compilers. [#1483](https://github.com/pq-code-package/mlkem-native/pull/1483)
   * Fix feature detection in example Makefiles via `auto.mk`. [#1490](https://github.com/pq-code-package/mlkem-native/pull/1490)
   * Fix alignment faults in AArch64 Neon assembly on bare-metal systems
     without MMU by replacing ldp/stp Q-register instructions with
     alignment-safe alternatives in Keccak x2/x4 and rej_uniform. [#1544](https://github.com/pq-code-package/mlkem-native/pull/1544)
   * Fix incorrect bounds check in `mlk_poly_getnoise_eta2()`: the upper
     bound on coefficient absolute values was using `MLKEM_ETA1` instead
     of `MLKEM_ETA2`. [#1572](https://github.com/pq-code-package/mlkem-native/pull/1572)

**Formal verification**
   * CBMC: Update to CBMC 6.7.0 ([#1098](https://github.com/pq-code-package/mlkem-native/pull/1098)), 6.7.1 ([#1118](https://github.com/pq-code-package/mlkem-native/pull/1118)), 6.8.0 ([#1279](https://github.com/pq-code-package/mlkem-native/pull/1279)).

   * CBMC: Add proofs for `crypto_kem_check_pk` and `crypto_kem_check_sk`.
     [#1176](https://github.com/pq-code-package/mlkem-native/pull/1176)
   * CBMC: Introduce explicit upper bounds on input/output buffer
     lengths. [#1191](https://github.com/pq-code-package/mlkem-native/pull/1191)
   * HOL-Light: Improve proof infrastructure: avoid hardcoded lengths
     ([#1218](https://github.com/pq-code-package/mlkem-native/pull/1218), [#1226](https://github.com/pq-code-package/mlkem-native/pull/1226)), run proofs until target PC ([#1221](https://github.com/pq-code-package/mlkem-native/pull/1221)), simplify
     poly_tobytes proof ([#1222](https://github.com/pq-code-package/mlkem-native/pull/1222)), speed up NTT/INTT proofs ([#1425](https://github.com/pq-code-package/mlkem-native/pull/1425)),
     allow cross-generation of bytecode ([#1444](https://github.com/pq-code-package/mlkem-native/pull/1444)), add HOL-Light cross
     shells ([#1441](https://github.com/pq-code-package/mlkem-native/pull/1441)).
   * CBMC: Stabilize proof of `polyvec_add()` and demonstrate use of
     external SMT solver. [#1288](https://github.com/pq-code-package/mlkem-native/pull/1288), [#1529](https://github.com/pq-code-package/mlkem-native/pull/1529)
   * HOL-Light: Add correctness proofs for x86_64 forward NTT ([#1374](https://github.com/pq-code-package/mlkem-native/pull/1374)),
     inverse NTT ([#1378](https://github.com/pq-code-package/mlkem-native/pull/1378)), poly_reduce ([#1381](https://github.com/pq-code-package/mlkem-native/pull/1381)), poly_tobytes ([#1383](https://github.com/pq-code-package/mlkem-native/pull/1383)),
     rejection sampling ([#1409](https://github.com/pq-code-package/mlkem-native/pull/1409)), frombytes ([#1418](https://github.com/pq-code-package/mlkem-native/pull/1418)), tomont ([#1418](https://github.com/pq-code-package/mlkem-native/pull/1418)),
     nttunpack ([#1420](https://github.com/pq-code-package/mlkem-native/pull/1420)), and mulcache_compute ([#1420](https://github.com/pq-code-package/mlkem-native/pull/1420)).
   * CBMC: Remove uses of object_whole and same_object for improved
     proof portability. [#1390](https://github.com/pq-code-package/mlkem-native/pull/1390)
   * CBMC: Use instrumented malloc/free for `MLK_ALLOC`/`MLK_FREE` to cover
     custom allocation in proofs. [#1405](https://github.com/pq-code-package/mlkem-native/pull/1405)
   * CBMC: Add functional specification for `mlk_ct_cmov_zero`. [#1437](https://github.com/pq-code-package/mlkem-native/pull/1437)
   * HOL-Light: Add output bounds to mulcache_compute proof. [#1443](https://github.com/pq-code-package/mlkem-native/pull/1443)
   * CBMC: Strengthen post-condition of ct_memcmp. [#1463](https://github.com/pq-code-package/mlkem-native/pull/1463)
   * CBMC: Add x86_64 HOL-Light-based contracts and proofs for native
     backend functions. [#1393](https://github.com/pq-code-package/mlkem-native/pull/1393)
   * HOL-Light: Add constant-time proofs for all AArch64 assembly:
     poly_tobytes ([#1563](https://github.com/pq-code-package/mlkem-native/pull/1563)), tomont/reduce/mulcache_compute ([#1565](https://github.com/pq-code-package/mlkem-native/pull/1565)),
     NTT/INTT/basemul ([#1568](https://github.com/pq-code-package/mlkem-native/pull/1568)), and Keccak-f1600 variants ([#1569](https://github.com/pq-code-package/mlkem-native/pull/1569)).
   * HOL-Light: Add constant-time proofs for all x86_64 assembly:
     reduce, tomont, and various other functions ([#1570](https://github.com/pq-code-package/mlkem-native/pull/1570)), basemul/NTT/
     INTT ([#1575](https://github.com/pq-code-package/mlkem-native/pull/1575)), and compression/decompression functions ([#1545](https://github.com/pq-code-package/mlkem-native/pull/1545)).
   * HOL-Light: Add correctness proofs for x86_64 poly_compress_d{4,5,
     10,11} ([#1545](https://github.com/pq-code-package/mlkem-native/pull/1545)) and poly_decompress_d{4,5,10,11} ([#1543](https://github.com/pq-code-package/mlkem-native/pull/1543)).
   * HOL-Light: Add correctness and safety proof for x86_64 AVX2
     Keccak-f1600 x4 permutation. [#1576](https://github.com/pq-code-package/mlkem-native/pull/1576)
   * HOL-Light: Add memory safety proofs for x86_64 and AArch64
     rejection sampling. [#1616](https://github.com/pq-code-package/mlkem-native/pull/1616), [#1617](https://github.com/pq-code-package/mlkem-native/pull/1617)

**Performance**
   * x86_64: Add AVX2 assembly implementation of polyvec_basemul for
     all parameter sets (k=2,3,4). [#1097](https://github.com/pq-code-package/mlkem-native/pull/1097)
   * Simplify `gen_matrix()` and `poly_rej_uniform_x4()`. [#1112](https://github.com/pq-code-package/mlkem-native/pull/1112)
   * x86_64: Rewrite rejection sampling in SSE4.1 assembly, replacing
     the previous AVX2 implementation with a simpler and faster
     approach. [#1136](https://github.com/pq-code-package/mlkem-native/pull/1136)
   * x86_64: Replace local function calls with macros in tomont,
     nttunpack, nttfrombytes, ntttobytes, and reduce assembly. [#1177](https://github.com/pq-code-package/mlkem-native/pull/1177)
   * x86_64: Broadcast 16-bit constants from immediates instead of
     loading from memory in several backend functions. [#1178](https://github.com/pq-code-package/mlkem-native/pull/1178)
   * AArch64: Re-run SLOTHY superoptimization for Neoverse-N1 model,
     including integration of scaling into invNTT layers. [#1088](https://github.com/pq-code-package/mlkem-native/pull/1088)
   * Serial FIPS-202: Do not use x4 Keccak for CBD sampling when
     `MLK_CONFIG_SERIAL_FIPS202_ONLY` is set. [#1392](https://github.com/pq-code-package/mlkem-native/pull/1392)
   * x86_64: Convert poly_compress_d{4,5,10,11} and
     poly_decompress_d{4,5,10,11} from AVX2 intrinsics to assembly.
     [#1543](https://github.com/pq-code-package/mlkem-native/pull/1543), [#1545](https://github.com/pq-code-package/mlkem-native/pull/1545)

**Build system & portability**
   * Nix: update to nixpkgs 25.11 ([#1556](https://github.com/pq-code-package/mlkem-native/pull/1556)), add gcc15 ([#1141](https://github.com/pq-code-package/mlkem-native/pull/1141)),
     clang 21 ([#1140](https://github.com/pq-code-package/mlkem-native/pull/1140)), zig 0.15 ([#1183](https://github.com/pq-code-package/mlkem-native/pull/1183)), Mingw-w64 14/15 ([#1253](https://github.com/pq-code-package/mlkem-native/pull/1253)),
     remove zig 0.10/0.11 ([#1083](https://github.com/pq-code-package/mlkem-native/pull/1083)).
   * Nix: introduce separate shells for cross compilation. [#1104](https://github.com/pq-code-package/mlkem-native/pull/1104)
   * Namespace zetas -> `mlk_zetas`. [#1120](https://github.com/pq-code-package/mlkem-native/pull/1120)
   * Remove unnecessary usage of `__m256i` from x86_64 backend C code,
     improving portability. [#1156](https://github.com/pq-code-package/mlkem-native/pull/1156)
   * Remove references to AES extension in x86_64 backend. [#1158](https://github.com/pq-code-package/mlkem-native/pull/1158)
   * Hoist default C backend into separate functions for cleaner
     native/fallback separation. [#1195](https://github.com/pq-code-package/mlkem-native/pull/1195)
   * Remove dependency on `stddef.h`, `string.h`, and `limits.h` from the
     library; only `stdint.h` is now required. [#1227](https://github.com/pq-code-package/mlkem-native/pull/1227), [#1548](https://github.com/pq-code-package/mlkem-native/pull/1548)
   * Add `-Wconversion` to builds and fix all resulting warnings. [#1230](https://github.com/pq-code-package/mlkem-native/pull/1230)
   * Introduce helper functions for signed<->unsigned conversions to
     avoid implementation-defined behavior. [#1239](https://github.com/pq-code-package/mlkem-native/pull/1239)
   * Autogenerate test configurations from `configs.yml`. [#1259](https://github.com/pq-code-package/mlkem-native/pull/1259)
   * Track environment variable changes in Makefile to trigger rebuilds
     when needed. [#1260](https://github.com/pq-code-package/mlkem-native/pull/1260)
   * Add support for Intel syntax in simpasm. [#1275](https://github.com/pq-code-package/mlkem-native/pull/1275)
   * Use consistent syntax for macro definitions and invocations across
     all assembly. [#1313](https://github.com/pq-code-package/mlkem-native/pull/1313)
   * Reintroduce struct definitions for `mlk_polyvec` and `mlk_polymat`
     (replacing raw arrays). [#1263](https://github.com/pq-code-package/mlkem-native/pull/1263)
   * Speed up make by reducing redundant work. [#1350](https://github.com/pq-code-package/mlkem-native/pull/1350)
   * Autogenerate the entire x86_64 `qdata` constant array for NTT/INTT.
     [#1430](https://github.com/pq-code-package/mlkem-native/pull/1430)
   * Refactor test directory structure: move sources to `test/src/`,
     `test/bench/`, `test/acvp/`, and `test/configs/`. [#1398](https://github.com/pq-code-package/mlkem-native/pull/1398), [#1401](https://github.com/pq-code-package/mlkem-native/pull/1401),
     [#1414](https://github.com/pq-code-package/mlkem-native/pull/1414), [#1416](https://github.com/pq-code-package/mlkem-native/pull/1416)
   * Use consistent architecture identifiers throughout. [#1456](https://github.com/pq-code-package/mlkem-native/pull/1456)
   * Use `MLK_MUST_CHECK_RETURN_VALUE` for all functions with return
     values. [#1454](https://github.com/pq-code-package/mlkem-native/pull/1454)
   * Namespace KeccakP_1600_times4_SIMD256 symbols with MLK_ prefix.
     [#1407](https://github.com/pq-code-package/mlkem-native/pull/1407)
   * Add shellcheck for shell script linting. [#1329](https://github.com/pq-code-package/mlkem-native/pull/1329)
   * Add actionlint for GitHub Actions linting. [#1537](https://github.com/pq-code-package/mlkem-native/pull/1537)

**Integration**
   * AWS-LC: Remove integration patches that have been merged upstream.
     [#1090](https://github.com/pq-code-package/mlkem-native/pull/1090), [#1165](https://github.com/pq-code-package/mlkem-native/pull/1165), [#1168](https://github.com/pq-code-package/mlkem-native/pull/1168)
   * libOQS: Autogenerate file list in integration metadata. [#1155](https://github.com/pq-code-package/mlkem-native/pull/1155)
   * libOQS: Expose encaps_derand in integration YML. [#1167](https://github.com/pq-code-package/mlkem-native/pull/1167)
   * libOQS: Enable constant-time testing in CI. [#1200](https://github.com/pq-code-package/mlkem-native/pull/1200)
   * OpenTitan: Add integration test to CI. [#1243](https://github.com/pq-code-package/mlkem-native/pull/1243)
   * AWS-LC: Handle `MLK_ASM_FN_SIZE` in importer for `.size` directives.
     [#1552](https://github.com/pq-code-package/mlkem-native/pull/1552)

**Changes**
   * Upgrade SLOTHY to latest main branch. [#1085](https://github.com/pq-code-package/mlkem-native/pull/1085)
   * Remove unused constant declaration headers from AArch64 backend.
     [#1095](https://github.com/pq-code-package/mlkem-native/pull/1095)
   * Guard #undef blocks in SCU by system-specific directives. [#1096](https://github.com/pq-code-package/mlkem-native/pull/1096)
   * ACVP: Update test vectors to v1.1.0.40 ([#1100](https://github.com/pq-code-package/mlkem-native/pull/1100)) and v1.1.0.41
     ([#1310](https://github.com/pq-code-package/mlkem-native/pull/1310)), and add transparent on-the-fly download. [#1119](https://github.com/pq-code-package/mlkem-native/pull/1119)
   * AArch64: Add YAML-based documentation to assembly files. [#1133](https://github.com/pq-code-package/mlkem-native/pull/1133)
   * FIPS202/AArch64: Unify naming of hybrid assembly routines. [#1134](https://github.com/pq-code-package/mlkem-native/pull/1134)
   * Reduce autogen runtime significantly. [#1266](https://github.com/pq-code-package/mlkem-native/pull/1266)
   * Various CI improvements: switch to free GitHub runners ([#1326](https://github.com/pq-code-package/mlkem-native/pull/1326)),
     add POWER10 benchmarking ([#1406](https://github.com/pq-code-package/mlkem-native/pull/1406)), add NixOS build+test ([#1297](https://github.com/pq-code-package/mlkem-native/pull/1297)),
     add symlink-check ([#1464](https://github.com/pq-code-package/mlkem-native/pull/1464)).
   * Meet PQCP Project Documentation Standards. [#1299](https://github.com/pq-code-package/mlkem-native/pull/1299)
   * Add `BUILDING.md` details for reproducing HOL-Light and CBMC proofs.
     [#1354](https://github.com/pq-code-package/mlkem-native/pull/1354)
   * Consolidate input-bound assertions in poly_ntt and
     polyvec_basemul_acc. [#1334](https://github.com/pq-code-package/mlkem-native/pull/1334)
   * Revise contributor guidelines. [#1369](https://github.com/pq-code-package/mlkem-native/pull/1369)
   * Remove x86_64 tomont_avx2 unused `qdata` argument. [#1432](https://github.com/pq-code-package/mlkem-native/pull/1432)
   * Remove unused *.inc files from x86_64 backend. [#1457](https://github.com/pq-code-package/mlkem-native/pull/1457)
   * Add documentation for `randombytes` and `mlk_randombytes`. [#1522](https://github.com/pq-code-package/mlkem-native/pull/1522)
