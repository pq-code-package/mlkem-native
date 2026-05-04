// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

use std::env;
use std::path::{Path, PathBuf};

// x86_64: enable when AVX2 is present (e.g. RUSTFLAGS="-C target-feature=+avx2").
// AArch64 LE: enable when NEON is present (mandatory on ARMv8-A, but check to be safe).
//   Big-endian AArch64 is excluded: the assembly backend only supports little-endian.
//   SHA3 (ARMv8.4-A): enables optimized Keccak x1/x2/x4 backends via __ARM_FEATURE_SHA3.
// RISC-V 64: arith-only backend (no RVV FIPS202 backend); enable with RUSTFLAGS="-C target-feature=+v".
enum Backend {
    Generic,
    Avx2,
    Aarch64 { sha3: bool },
    Riscv64Rvv,
}

impl Backend {
    fn detect() -> Self {
        let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
        let endian = env::var("CARGO_CFG_TARGET_ENDIAN").unwrap_or_default();
        let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
        let has = |f: &str| features.split(',').any(|t| t == f);

        match arch.as_str() {
            "x86_64" if has("avx2") => Backend::Avx2,
            "aarch64" if endian == "little" && has("neon") => Backend::Aarch64 { sha3: has("sha3") },
            "riscv64" if has("v") => Backend::Riscv64Rvv,
            _ => Backend::Generic,
        }
    }

    // AArch64 and x86_64 have assembly backends bundled in mlkem_native_asm.S;
    // RISC-V uses only C intrinsics so no separate asm compilation is needed.
    fn needs_asm(&self) -> bool {
        matches!(self, Backend::Avx2 | Backend::Aarch64 { .. })
    }

    fn apply(&self, build: &mut cc::Build) {
        let is_msvc = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default() == "msvc";
        match self {
            Backend::Avx2 => {
                build
                    .define("MLK_CONFIG_USE_NATIVE_BACKEND_ARITH", None)
                    .define("MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202", None)
                    .flag(if is_msvc { "/arch:AVX2" } else { "-mavx2" });
            }
            Backend::Aarch64 { sha3 } => {
                build
                    .define("MLK_CONFIG_USE_NATIVE_BACKEND_ARITH", None)
                    .define("MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202", None);
                if *sha3 {
                    build.flag("-march=armv8.4-a+sha3");
                }
            }
            Backend::Riscv64Rvv => {
                build
                    .define("MLK_CONFIG_USE_NATIVE_BACKEND_ARITH", None)
                    .flag("-march=rv64gcv");
            }
            Backend::Generic => {}
        }
    }

    fn emit_cfg(&self) {
        for key in [
            "mlkem_native_backend_avx2",
            "mlkem_native_backend_aarch64",
            "mlkem_native_backend_aarch64_sha3",
            "mlkem_native_backend_riscv64_rvv",
        ] {
            println!("cargo:rustc-check-cfg=cfg({key})");
        }
        match self {
            Backend::Avx2 => println!("cargo:rustc-cfg=mlkem_native_backend_avx2"),
            Backend::Aarch64 { sha3 } => {
                println!("cargo:rustc-cfg=mlkem_native_backend_aarch64");
                if *sha3 {
                    println!("cargo:rustc-cfg=mlkem_native_backend_aarch64_sha3");
                }
            }
            Backend::Riscv64Rvv => println!("cargo:rustc-cfg=mlkem_native_backend_riscv64_rvv"),
            Backend::Generic => {}
        }
    }
}

// When cross-compiling, derive the C compiler explicitly so that a CC env
// var pointing at the host compiler (common in Nix shells) doesn't
// silently produce host-arch object files. CC_<target> takes precedence
// over this fallback; CC on its own is ignored when cross-compiling
// because it typically names the host compiler, not the cross-compiler.
//
// RISC-V triples include "gc" (e.g. riscv64gc-unknown-linux-gnu) but the
// gcc binary omits it (riscv64-unknown-linux-gnu-gcc).
fn cross_compiler(host: &str, target: &str) -> Option<String> {
    if host == target {
        return None;
    }
    let cc_env = format!("CC_{}", target.replace('-', "_"));
    if env::var(&cc_env).is_ok() {
        return None;
    }
    let gcc_triple = target
        .replace("riscv64gc-", "riscv64-")
        .replace("riscv32gc-", "riscv32-");
    Some(format!("{}-gcc", gcc_triple))
}

fn base_build(mlkem_dir: &Path, level: u32, compiler: Option<&str>) -> cc::Build {
    let level_str = level.to_string();
    let mut build = cc::Build::new();
    build
        .include(mlkem_dir)
        .define("MLK_CONFIG_PARAMETER_SET", level_str.as_str())
        .define("MLK_CONFIG_NO_RANDOMIZED_API", None)
        .opt_level(3);
    if let Some(cc) = compiler {
        build.compiler(cc);
    }
    build
}

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    // The mlkem C sources are bundled alongside this crate in the `mlkem/`
    // directory (a symlink to the repository root's mlkem/ in the source tree,
    // and the resolved files in published packages).
    let mlkem_dir = manifest_dir.join("mlkem");

    println!("cargo:rerun-if-changed={}", mlkem_dir.display());

    let host = env::var("HOST").unwrap_or_default();
    let target = env::var("TARGET").unwrap_or_default();
    let compiler = cross_compiler(&host, &target);
    let backend = Backend::detect();
    backend.emit_cfg();

    for &level in &[512u32, 768, 1024] {
        let mut c_build = base_build(&mlkem_dir, level, compiler.as_deref());
        c_build.file(mlkem_dir.join("mlkem_native.c"));
        backend.apply(&mut c_build);
        c_build.compile(&format!("mlkem_native_{}", level));

        if backend.needs_asm() {
            let mut asm_build = base_build(&mlkem_dir, level, compiler.as_deref());
            asm_build.file(mlkem_dir.join("mlkem_native_asm.S"));
            backend.apply(&mut asm_build);
            asm_build.compile(&format!("mlkem_native_asm_{}", level));
        }
    }
}
