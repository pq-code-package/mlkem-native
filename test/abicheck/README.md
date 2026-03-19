[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# ABI Checker

This directory contains an ABI compliance checker for all AArch64 assembly in mlkem-native. Its purpose is to verify that every assembly function obeys the [AAPCS64](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst) calling convention — specifically, that callee-saved registers (x19–x28, x29/FP, d8–d15) are preserved across calls.

Failure to obey the AAPCS can lead to rare but fatal bugs depending on the exact compiler and compilation settings, since the compiler assumes callee-saved registers are untouched after a function call.

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

### Assembly call stub

The core mechanism is an assembly call stub (`aarch64_callstub.S`):

```c
void asm_call_stub(struct register_state *input,
                   struct register_state *output,
                   void (*function_ptr)(void));
```

This stub:
1. Saves its own callee-saved registers to the stack.
2. Loads *all* GPRs (x0–x29) and NEON registers (q0–q31) from the `input` struct.
3. Calls `function_ptr` via `blr`.
4. Captures the full register state into the `output` struct.
5. Restores its own callee-saved registers and returns.

Crucially, the stub does *not* assume `function_ptr` obeys the AAPCS — that is what we are testing.

### Per-function checks

Each per-function check (`check_*.c`) does the following for each test iteration:
1. Initializes a `register_state` with known values for all registers.
2. For pointer arguments (identified from YAML metadata), allocates aligned buffers of the correct size and places their addresses in the corresponding GPR slots.
3. Calls the function under test through `asm_call_stub`.
4. Compares the callee-saved registers (x18–x29, d8–d15) between input and output states.

### Code generation via autogen

The per-function check files and the `checks_all.h` registry are **auto-generated** by `scripts/autogen` (function `gen_abicheck()`). The generation works as follows:

1. **Discovery**: `autogen` globs for all `.S` files under `mlkem/src/native/aarch64/src/` and `mlkem/src/fips202/native/aarch64/src/`.

2. **YAML parsing**: Each assembly file contains a `/*yaml ... */` metadata block specifying the function name, C signature, and ABI — which registers are buffers (with sizes) vs. scalars. For example:

   ```yaml
   /*yaml
     Name: ntt_asm
     Signature: void mlk_ntt_asm(int16_t p[256], ...)
     ABI:
       x0:
         type: buffer
         size_bytes: 512
       x1:
         type: buffer
         size_bytes: 160
   */
   ```

3. **Check generation**: For each function, `autogen` emits a `test/abicheck/check_<name>.c` file that declares the function, allocates `MLK_ALIGN`-ed buffers for each `buffer`-typed register, and wires up the `asm_call_stub` call and compliance check.

4. **Architecture guards**: `autogen` detects `#if defined(__ARM_FEATURE_SHA3)` guards in the assembly source and wraps the corresponding check in matching `#if`/`#endif`.

5. **Registry**: `autogen` generates `checks_all.h` containing an array of `{name, function_pointer}` entries for all checks, used by the driver `abicheck.c`.

### Handwritten files

| File | Purpose |
|------|---------|
| `aarch64_callstub.S` | Assembly stub to call functions with controlled register state |
| `abicheck.c` | Test driver — iterates over all checks and reports results |
| `abicheckutil.c/h` | AAPCS compliance check and register state initialization |

### Build integration

The ABI checker has its own build directory (`test/build/abicheck/`) and compiles the assembly files under test directly — bypassing the normal backend selection by explicitly defining the preprocessor guards (`MLK_ARITH_BACKEND_AARCH64`, `MLK_FIPS202_AARCH64_NEED_*`, etc.). See `test/mk/components.mk` for details.
