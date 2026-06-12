[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# ABI Checker

Checks that each assembly kernel preserves the callee-saved registers required
by its platform ABI.

- **AArch64** (AAPCS64[^AAPCS64]): x19–x28, x29/FP, lower 64 bits of d8–d15.
- **x86_64** (System V[^SysVAMD64]): rbx, rbp, r12–r15. No SIMD register is callee-saved.
- **PowerPC64** (ELFv2[^PPC64ELFv2]): r14–r31, lower 64 bits of f14–f31, v20–v31, CR2–CR4.
- **Armv8.1-M** (AAPCS32[^AAPCS32] + MVE[^ArmARMv8M]): r4–r11, MVE Q4–Q7 (= D8–D15).

## Usage

```bash
make run_abicheck OPT=1       # OPT=1 required; a no-op without it
./scripts/tests abicheck
./scripts/tests all           # runs abicheck by default; --no-abicheck to skip
```

## How it works

A per-arch assembly call stub (`<arch>/callstub_<arch>.S`) loads a random
register state, calls the kernel, and captures the result — it does *not*
assume the kernel obeys the calling convention, which is the point. The
generated `<arch>/checks/check_<name>.c` then seeds the state, backs pointer
arguments with correctly-sized buffers, calls through the stub, and reports any
callee-saved register the kernel failed to preserve.

Before trusting any verdict, `abicheck.c` runs a self-test: hand-written
corrupters (`<arch>/selftest_<arch>.S`) that each clobber one callee-saved
register, confirming the checker fires.

The shipped `mlkem/src/.../*.S` are assembled directly — no copy. On
unsupported architectures the registry is empty and the driver exits cleanly.

## Code generation

Each kernel's buffer sizes, calling convention, and required CPU features come
from a `/*yaml ... */` block in its `dev/` assembly source. `scripts/autogen`
turns that into the per-kernel `check_<name>.c`, the `checks_<arch>_all.h`
registry, and the per-arch `abicheck_<arch>.mk` (CFLAGS per feature, e.g.
`-mavx2`), all included via `abicheck.mk` from `test/mk/components.mk`. Edit the
YAML, not the generated files.

<!--- bibliography --->
[^AAPCS32]: Arm Limited: Procedure Call Standard for the Arm Architecture (AAPCS32), [https://github.com/ARM-software/abi-aa/blob/main/aapcs32/aapcs32.rst](https://github.com/ARM-software/abi-aa/blob/main/aapcs32/aapcs32.rst)
[^AAPCS64]: Arm Limited: Procedure Call Standard for the Arm 64-bit Architecture (AAPCS64), [https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst)
[^ArmARMv8M]: Arm Limited: Armv8-M Architecture Reference Manual (DDI 0553), [https://developer.arm.com/documentation/ddi0553/latest/](https://developer.arm.com/documentation/ddi0553/latest/)
[^PPC64ELFv2]: OpenPOWER Foundation: 64-Bit ELFv2 ABI Specification — Power Architecture, [https://openpowerfoundation.org/specifications/64bitelfabi/](https://openpowerfoundation.org/specifications/64bitelfabi/)
[^SysVAMD64]: Matz, Hubička, Jaeger, Mitchell: System V Application Binary Interface — AMD64 Architecture Processor Supplement, [https://gitlab.com/x86-psABIs/x86-64-ABI](https://gitlab.com/x86-psABIs/x86-64-ABI)
