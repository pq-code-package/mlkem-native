// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#![allow(non_upper_case_globals, non_camel_case_types, non_snake_case, dead_code)]

pub mod mlkem512 {
    include!(concat!(env!("OUT_DIR"), "/bindings_512.rs"));
}
pub mod mlkem768 {
    include!(concat!(env!("OUT_DIR"), "/bindings_768.rs"));
}
pub mod mlkem1024 {
    include!(concat!(env!("OUT_DIR"), "/bindings_1024.rs"));
}
