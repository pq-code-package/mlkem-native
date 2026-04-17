// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

use std::env;
use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    // The mlkem C sources live at the repository root, three directories above
    // this crate (bindings/rust/mlkem-native/ → repo root).
    let repo_root = manifest_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let mlkem_dir = repo_root.join("mlkem");

    println!("cargo:rerun-if-changed={}", mlkem_dir.display());

    // Enable AVX2 native backends when the target is x86_64 and the `avx2`
    // CPU feature is present at compile time (e.g. via
    // `RUSTFLAGS="-C target-cpu=native"` or
    // `RUSTFLAGS="-C target-feature=+avx2"`).
    let target_features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    let use_avx2 = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default() == "x86_64"
        && target_features.split(',').any(|f| f == "avx2");

    if use_avx2 {
        println!("cargo:rustc-cfg=mlkem_native_avx2");
    }

    for &level in &[512u32, 768, 1024] {
        let level_str = level.to_string();

        let mut c_build = cc::Build::new();
        c_build
            .file(mlkem_dir.join("mlkem_native.c"))
            .include(&mlkem_dir)
            .define("MLK_CONFIG_PARAMETER_SET", level_str.as_str())
            .define("MLK_CONFIG_NO_RANDOMIZED_API", None)
            .opt_level(3);

        if use_avx2 {
            c_build
                .define("MLK_CONFIG_USE_NATIVE_BACKEND_ARITH", None)
                .define("MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202", None)
                .flag("-mavx2");
        }

        c_build.compile(&format!("mlkem_native_{}", level));

        if use_avx2 {
            cc::Build::new()
                .file(mlkem_dir.join("mlkem_native_asm.S"))
                .include(&mlkem_dir)
                .define("MLK_CONFIG_PARAMETER_SET", level_str.as_str())
                .define("MLK_CONFIG_USE_NATIVE_BACKEND_ARITH", None)
                .define("MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202", None)
                .flag("-mavx2")
                .compile(&format!("mlkem_native_asm_{}", level));
        }
    }
}
