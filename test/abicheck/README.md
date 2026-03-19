[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# ABI Checker

This directory contains an ABI compliance checker for all AArch64 and x86_64 assembly in mlkem-native. Its purpose is to verify that every assembly function obeys the platform calling convention — specifically:

- **AArch64 (AAPCS64)**: x19–x28, x29/FP, and d8–d15 must be preserved across calls.
- **x86_64 (System V)**: rbx, rbp, and r12–r15 must be preserved across calls. No SIMD registers are callee-saved.

Failure to obey the calling convention can lead to rare but fatal bugs depending on the exact compiler and compilation settings, since the compiler assumes callee-saved registers are untouched after a function call.

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

The core mechanism is an architecture-specific assembly call stub:

```c
// AArch64
void asm_call_stub(struct register_state *input,
                   struct register_state *output,
                   void (*function_ptr)(void));

// x86_64
void asm_call_stub_x86_64(struct x86_64_register_state *input,
                           struct x86_64_register_state *output,
                           void (*function_ptr)(void));
```

Each stub:
1. Saves its own callee-saved registers to the stack.
2. Loads all GPRs (and NEON registers on AArch64) from the `input` struct.
3. Calls `function_ptr`.
4. Captures the full register state into the `output` struct.
5. Restores its own callee-saved registers and returns.

Crucially, the stub does *not* assume `function_ptr` obeys the calling convention — that is what we are testing.

### Per-function checks

Each per-function check (`check_*_<arch>.c`) does the following for each test iteration:
1. Initializes a register state with known sentinel values for callee-saved registers.
2. For pointer arguments (identified from YAML metadata), allocates aligned buffers of the correct size and places their addresses in the corresponding register slots.
3. Calls the function under test through the call stub.
4. Compares the callee-saved registers between input and output states.

### Code generation via autogen

The per-function check files and the `checks_all.h` registry are **auto-generated** by `scripts/autogen` (function `gen_abicheck()`). The generation works as follows:

1. **Discovery**: `autogen` globs for all `.S` files under the native backend directories for each architecture.

2. **YAML parsing**: Each assembly file contains a `/*yaml ... */` metadata block specifying the function name, C signature, and ABI — which registers are buffers (with sizes) vs. scalars. For example:

   ```yaml
   /*yaml
     Name: ntt_avx2
     Signature: void mlk_ntt_avx2(int16_t *r, const int16_t *qdata)
     ABI:
       rdi:
         type: buffer
         size_bytes: 512
       rsi:
         type: buffer
         size_bytes: 1248
   */
   ```

3. **Check generation**: For each function, `autogen` emits a `test/abicheck/check_<name>_<arch>.c` file that declares the function, allocates `MLK_ALIGN`-ed buffers for each `buffer`-typed register, and wires up the call stub and compliance check.

4. **Architecture guards**: `autogen` detects preprocessor guards (e.g. `__ARM_FEATURE_SHA3`) in the assembly source and wraps the corresponding check in matching `#if`/`#endif`.

5. **Registry**: `autogen` generates `checks_all.h` containing an array of `{name, function_pointer}` entries for all checks on the current architecture, used by the driver `abicheck.c`.

### Handwritten files

| File | Purpose |
|------|---------|
| `aarch64_callstub.S` | AArch64 call stub — captures GPRs and NEON registers |
| `x86_64_callstub.S` | x86_64 call stub — captures GPRs only (no callee-saved SIMD) |
| `abicheck.c` | Test driver — iterates over all checks and reports results |
| `abicheckutil.c/h` | Compliance check and register state initialization per architecture |

### Build integration

The ABI checker has its own build directory (`test/build/abicheck/`) and compiles the assembly files under test directly — bypassing the normal backend selection by explicitly defining the preprocessor guards (`MLK_ARITH_BACKEND_AARCH64`, `MLK_ARITH_BACKEND_X86_64_DEFAULT`, etc.). See `test/mk/components.mk` for details.

For x86_64, the build also includes C files providing constant data needed by the assembly (`consts.c`, `compress_consts.c`, `rej_uniform_table.c`, `keccakf1600_constants.c`).
