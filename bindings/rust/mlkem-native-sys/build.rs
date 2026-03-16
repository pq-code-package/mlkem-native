// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

use std::env;
use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let mlkem_dir = manifest_dir.join("mlkem");
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    println!("cargo:rerun-if-changed={}", mlkem_dir.display());

    // Compile the C library for each parameter set using the monolithic build file.
    // We build without the randomized API so no randombytes() implementation is needed.
    for &level in &[512u32, 768, 1024] {
        cc::Build::new()
            .file(mlkem_dir.join("mlkem_native.c"))
            .include(&mlkem_dir)
            .define("MLK_CONFIG_PARAMETER_SET", level.to_string().as_str())
            .define("MLK_CONFIG_NO_RANDOMIZED_API", None)
            .opt_level(3)
            .compile(&format!("mlkem_native_{}", level));
    }

    // Generate bindings for each parameter set.
    let header = mlkem_dir.join("mlkem_native.h");
    for &level in &[512u32, 768, 1024] {
        let bindings = bindgen::Builder::default()
            .header(header.to_str().unwrap())
            .clang_arg(format!("-I{}", mlkem_dir.display()))
            .clang_arg(format!("-DMLK_CONFIG_PARAMETER_SET={}", level))
            // Suppress SUPERCOP crypto_kem_* aliases — use namespaced names only.
            .clang_arg("-DMLK_CONFIG_API_NO_SUPERCOP")
            // Must match the compiled library.
            .clang_arg("-DMLK_CONFIG_NO_RANDOMIZED_API")
            .allowlist_function(format!("PQCP_MLKEM_NATIVE_MLKEM{}_.*", level))
            .allowlist_var(format!("MLKEM{}_.*", level))
            .allowlist_var("MLKEM_BYTES")
            .allowlist_var("MLKEM_SYMBYTES")
            .allowlist_var("MLK_ERR_.*")
            .use_core()
            .generate()
            .unwrap_or_else(|_| panic!("Unable to generate bindings for MLKEM-{}", level));

        bindings
            .write_to_file(out_dir.join(format!("bindings_{}.rs", level)))
            .unwrap_or_else(|_| panic!("Couldn't write bindings for MLKEM-{}", level));
    }
}
