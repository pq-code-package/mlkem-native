// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! Raw FFI bindings to [mlkem-native], a C90 implementation of ML-KEM ([FIPS 203]).
//!
//! This crate exposes the deterministic (`_derand`) API for all three parameter
//! sets. The randomized API (`keypair` / `enc`) is intentionally omitted here;
//! it is provided by the higher-level `mlkem-native` crate using Rust's RNG
//! ecosystem.
//!
//! # Safety
//!
//! All functions in this crate are `unsafe` — callers must ensure that buffers
//! are valid, correctly-sized, and non-overlapping, as documented by each
//! function in the C header `mlkem/mlkem_native.h`.
//!
//! [mlkem-native]: https://github.com/pq-code-package/mlkem-native
//! [FIPS 203]: https://csrc.nist.gov/pubs/fips/203/final

#![no_std]
#![allow(non_upper_case_globals, non_camel_case_types, non_snake_case, dead_code)]

/// Bindings for ML-KEM-512 (NIST security level 1).
pub mod mlkem512 {
    include!(concat!(env!("OUT_DIR"), "/bindings_512.rs"));
}

/// Bindings for ML-KEM-768 (NIST security level 3).
pub mod mlkem768 {
    include!(concat!(env!("OUT_DIR"), "/bindings_768.rs"));
}

/// Bindings for ML-KEM-1024 (NIST security level 5).
pub mod mlkem1024 {
    include!(concat!(env!("OUT_DIR"), "/bindings_1024.rs"));
}
