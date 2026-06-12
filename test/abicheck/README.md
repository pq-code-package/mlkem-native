[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# ABI Checker

This directory contains an ABI compliance checker for the assembly kernels of mlkem-native. It checks that each kernel preserves the callee-saved registers required by its platform ABI; the bullets below cover that subset, and the cited specs hold the full rules.

- **AArch64 (AAPCS64[^AAPCS64], § "Machine Registers")**: GPRs x19–x28; frame pointer x29; lower 64 bits of SIMD/FP registers d8–d15 must be preserved across calls. x30/LR is the link register; x18 is the platform register (Darwin reserves it; ELF leaves it free).
- **x86_64 (System V AMD64 psABI[^SysVAMD64], § 3.2 "Function Calling Sequence")**: GPRs rbx, rbp, r12–r15 must be preserved across calls. **No XMM/YMM/ZMM register is callee-saved** — every SIMD register is volatile.
- **PowerPC64 (ELFv2[^PPC64ELFv2], § 2.2 "Register Usage")**: GPRs r14–r31; lower 64 bits of FPRs f14–f31; full 128 bits of VSX/VR v20–v31; CR fields CR2–CR4. (CR is the 32-bit condition register, eight 4-bit fields CR0..CR7; CR0/CR1 and CR5–CR7 are volatile.)
- **Armv8.1-M (AAPCS32[^AAPCS32], § 5.1 "Machine Registers"; MVE/Helium register file per the Armv8-M Architecture Reference Manual[^ArmARMv8M], § B7)**: GPRs r4–r11; MVE Q4–Q7 (which alias D8–D15 / S16–S23 in the FP/Helium register file). r12 (IP), LR/r14, and the lower vector lanes belonging to the standard FP set are caller-saved.

Only the lower 64 bits of d8–d15 (AArch64) and f14–f31 (PPC64) are callee-saved — the upper halves (q8–q15 lanes) are volatile — and the checker compares exactly those byte ranges.

Violations cause silent miscompilation in callers that hold live values in a clobbered callee-saved register.

## Usage

```bash
# Build and run via Make (requires OPT=1 for assembly)
make run_abicheck OPT=1

# Via the test script
./scripts/tests abicheck

# As part of the full test suite (enabled by default)
./scripts/tests all
./scripts/tests all --no-abicheck   # to skip
```

The ABI checker is only meaningful when native backends are enabled (`OPT=1`). With `OPT=0`, the targets are no-ops.

## How it works

### Assembly call stubs

Each (arch, calling-convention) pair has its own assembly call stub and `register_state` struct. The AArch64 stub:

```c
// AArch64 (AAPCS64); x86_64 / ppc64le / armv8.1-M follow the same shape
// with a per-arch <arch>_register_state struct and an arch-suffixed symbol
// (asm_call_stub_x86_64_sysv, asm_call_stub_ppc64le, asm_call_stub_armv81m).
void asm_call_stub_aarch64(struct aarch64_register_state *input,
                           struct aarch64_register_state *output,
                           void (*function_ptr)(void));
```

Each stub:
1. Saves its own callee-saved registers to the stack.
2. Loads all GPRs (and SIMD/NEON/VSX registers as relevant) from the `input` struct.
3. Calls `function_ptr`.
4. Captures the full register state into the `output` struct.
5. Restores its own callee-saved registers and returns.

Crucially, the stub does *not* assume `function_ptr` obeys the calling convention — that is what we are testing.

### Per-function checks

Each generated `check_<name>.c` does the following for each test iteration:
1. Seeds the input register state with random bytes (via `test/notrandombytes/`, deterministic for reproducibility).
2. For pointer arguments (identified from the YAML metadata), allocates `MLK_ALIGN`-ed buffers of the correct size and places their addresses in the corresponding register slots.
3. Calls the function under test through the matching call stub.
4. Compares the callee-saved registers between input and output states; any mismatch is reported and the iteration fails.

### YAML metadata

Each dev assembly file carries a `/*yaml ... */` block with this shape:

```yaml
/*yaml
Name: ntt_avx2_asm
Description: x86_64 AVX2 forward NTT
Signature: void mlk_ntt_avx2_asm(int16_t *r, const int16_t *qdata)
ABI:
  Architecture: x86_64
  CallingConvention: SysV
  Features: [AVX2]
  Registers:
    rdi:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t *r
      description: Input/output polynomial (256 x int16_t)
    rsi:
      type: buffer
      size_bytes: 1248
      permissions: read-only
      c_parameter: const int16_t *qdata
      description: Precomputed constants (624 x int16_t)
*/
```

- **`Name`** — the kernel's `.global` symbol; `Signature` names the C entry point as `mlk_<Name>`.
- **`Architecture` / `CallingConvention`** — the pair keys an `ARCH_CALLINGS` row in `scripts/autogen` (today: `aarch64/AAPCS64`, `x86_64/SysV`, `powerpc64le/ELFv2`, `armv81m/AAPCS32`).
- **`Features`** — drawn from `ABI_CAPS` (today: `AVX2`, `SHA3`, `MVE`); drives the per-kernel C-time `#if` guard, the runtime `mlk_sys_check_capability` skip, and the build-time per-cap CFLAGS (e.g. `-march=armv8.4-a+sha3`).
- **Register entries** — each remaining child of `ABI:` pre-populates the input state and validates buffer sizes.

### Code generation via autogen

`scripts/autogen` runs `gen_abicheck()` to produce, from the dev/ YAML:

1. **Per-function `test/abicheck/<arch>/check_<name>.c`** with the right buffer setup, capability gate, call stub, and compliance check — all driven by the (arch, calling) row and `ABI_CAPS` lookups.
2. **`test/abicheck/<arch>/checks_<arch>_all.h`** registering only the kernels for the architecture being built. Within an architecture, individual entries are gated on their calling-convention's extra guards (e.g. `MLK_SYSV_ABI_SUPPORTED` for x86_64 SysV) plus their feature guards.
3. **`test/abicheck/abicheck_features.mk`** mapping each capability to the list of shipped `mlkem/src/.../*.S` files needing it, with the matching CFLAGS attached. Included by `test/mk/components.mk`.

### Handwritten files

| File | Purpose |
|------|---------|
| [`aarch64/aarch64_callstub.S`](aarch64/aarch64_callstub.S) | AArch64 (AAPCS64) call stub — captures GPRs and NEON registers |
| [`x86_64/x86_64_callstub.S`](x86_64/x86_64_callstub.S) | x86_64 (System V) call stub — captures GPRs only (no callee-saved SIMD) |
| [`ppc64le/ppc64le_callstub.S`](ppc64le/ppc64le_callstub.S) | PowerPC64 (ELF v2) call stub — captures GPRs, FPRs, VRs, and the CR |
| [`armv81m/armv81m_callstub.S`](armv81m/armv81m_callstub.S) | Armv8.1-M (Thumb-2 / AAPCS32+MVE) call stub — captures GPRs and the MVE Q-registers |
| [`abicheck.c`](abicheck.c) | Test driver — runs the selftest, then iterates over `all_checks[]` and reports results |
| [`abicheckutil.c`](abicheckutil.c) / [`abicheckutil.h`](abicheckutil.h) | Per-(arch, calling) compliance check, register-state init, return-code constants (`MLK_ABICHECK_PASSED/SKIPPED/FAILED`), `MLK_ABICHECK_NUM_TESTS`, and the `MLK_ABICHECK_VERBOSE/QUIET` flag |
| [`selftest.c`](selftest.c), [`selftest.h`](selftest.h) | Meta-test harness — runs each per-arch corrupter through the stub+compliance check and asserts the checker fires |
| [`aarch64/selftest_aarch64.S`](aarch64/selftest_aarch64.S), [`x86_64/selftest_x86_64.S`](x86_64/selftest_x86_64.S), [`ppc64le/selftest_ppc64le.S`](ppc64le/selftest_ppc64le.S), [`armv81m/selftest_armv81m.S`](armv81m/selftest_armv81m.S) | Per-arch corrupter stubs (one per callee-saved register, plus a noop), called by the selftest harness |

### Build integration

The ABI checker has its own build directory (`test/build/abicheck/`) and assembles the shipped `mlkem/src/{native,fips202/native}/<arch>/src/*.S` directly — no copy, no export step. The build defines `MLK_CONFIG_MULTILEVEL_WITH_SHARED`, `MLK_CONFIG_PARAMETER_SET=768`, `MLK_CONFIG_NAMESPACE_PREFIX=mlk`, and every `MLK_ARITH_BACKEND_*` / `MLK_FIPS202_*_NEED_*` macro to satisfy the `#if` guards in each kernel source, and undefines `MLK_CONFIG_USE_NATIVE_BACKEND_{ARITH,FIPS202}` so `common.h` does not pull in the backend headers that would redefine those macros. Per-feature CFLAGS (e.g. `-march=armv8.4-a+sha3`, `-mavx2 -mbmi2`) come from autogen into `abicheck_features.mk` (consumed by `test/mk/components.mk`); PPC64 builds also apply `-mcpu=power8 -maltivec -mvsx` arch-wide. On AArch64, SHA3-only Keccak variants are filtered out when `MK_COMPILER_SUPPORTS_SHA3` (set by `test/mk/auto.mk` from a `-march=armv8.4-a+sha3` probe) is not `1`.

<!--- bibliography --->
[^AAPCS32]: Arm Limited: Procedure Call Standard for the Arm Architecture (AAPCS32), [https://github.com/ARM-software/abi-aa/blob/main/aapcs32/aapcs32.rst](https://github.com/ARM-software/abi-aa/blob/main/aapcs32/aapcs32.rst)
[^AAPCS64]: Arm Limited: Procedure Call Standard for the Arm 64-bit Architecture (AAPCS64), [https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst)
[^ArmARMv8M]: Arm Limited: Armv8-M Architecture Reference Manual (DDI 0553), [https://developer.arm.com/documentation/ddi0553/latest/](https://developer.arm.com/documentation/ddi0553/latest/)
[^PPC64ELFv2]: OpenPOWER Foundation: 64-Bit ELFv2 ABI Specification — Power Architecture, [https://openpowerfoundation.org/specifications/64bitelfabi/](https://openpowerfoundation.org/specifications/64bitelfabi/)
[^SysVAMD64]: Matz, Hubička, Jaeger, Mitchell: System V Application Binary Interface — AMD64 Architecture Processor Supplement, [https://gitlab.com/x86-psABIs/x86-64-ABI](https://gitlab.com/x86-psABIs/x86-64-ABI)
