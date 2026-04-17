// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#![allow(non_upper_case_globals, non_camel_case_types, non_snake_case, dead_code)]

pub mod mlkem512 {
    pub const MLKEM512_SECRETKEYBYTES: usize = 1632;
    pub const MLKEM512_PUBLICKEYBYTES: usize = 800;
    pub const MLKEM512_CIPHERTEXTBYTES: usize = 768;
    pub const MLKEM512_SYMBYTES: usize = 32;
    pub const MLKEM512_BYTES: usize = 32;

    pub const MLKEM_SYMBYTES: usize = 32;
    pub const MLKEM_BYTES: usize = 32;

    pub const MLK_ERR_FAIL: i32 = -1;
    pub const MLK_ERR_OUT_OF_MEMORY: i32 = -2;
    pub const MLK_ERR_RNG_FAIL: i32 = -3;

    extern "C" {
        pub fn PQCP_MLKEM_NATIVE_MLKEM512_keypair_derand(
            pk: *mut u8,
            sk: *mut u8,
            coins: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM512_enc_derand(
            ct: *mut u8,
            ss: *mut u8,
            pk: *const u8,
            coins: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM512_dec(
            ss: *mut u8,
            ct: *const u8,
            sk: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM512_check_pk(pk: *const u8) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM512_check_sk(sk: *const u8) -> i32;
    }
}

pub mod mlkem768 {
    pub const MLKEM768_SECRETKEYBYTES: usize = 2400;
    pub const MLKEM768_PUBLICKEYBYTES: usize = 1184;
    pub const MLKEM768_CIPHERTEXTBYTES: usize = 1088;
    pub const MLKEM768_SYMBYTES: usize = 32;
    pub const MLKEM768_BYTES: usize = 32;

    pub const MLKEM_SYMBYTES: usize = 32;
    pub const MLKEM_BYTES: usize = 32;

    pub const MLK_ERR_FAIL: i32 = -1;
    pub const MLK_ERR_OUT_OF_MEMORY: i32 = -2;
    pub const MLK_ERR_RNG_FAIL: i32 = -3;

    extern "C" {
        pub fn PQCP_MLKEM_NATIVE_MLKEM768_keypair_derand(
            pk: *mut u8,
            sk: *mut u8,
            coins: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM768_enc_derand(
            ct: *mut u8,
            ss: *mut u8,
            pk: *const u8,
            coins: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM768_dec(
            ss: *mut u8,
            ct: *const u8,
            sk: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM768_check_pk(pk: *const u8) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM768_check_sk(sk: *const u8) -> i32;
    }
}

pub mod mlkem1024 {
    pub const MLKEM1024_SECRETKEYBYTES: usize = 3168;
    pub const MLKEM1024_PUBLICKEYBYTES: usize = 1568;
    pub const MLKEM1024_CIPHERTEXTBYTES: usize = 1568;
    pub const MLKEM1024_SYMBYTES: usize = 32;
    pub const MLKEM1024_BYTES: usize = 32;

    pub const MLKEM_SYMBYTES: usize = 32;
    pub const MLKEM_BYTES: usize = 32;

    pub const MLK_ERR_FAIL: i32 = -1;
    pub const MLK_ERR_OUT_OF_MEMORY: i32 = -2;
    pub const MLK_ERR_RNG_FAIL: i32 = -3;

    extern "C" {
        pub fn PQCP_MLKEM_NATIVE_MLKEM1024_keypair_derand(
            pk: *mut u8,
            sk: *mut u8,
            coins: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM1024_enc_derand(
            ct: *mut u8,
            ss: *mut u8,
            pk: *const u8,
            coins: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM1024_dec(
            ss: *mut u8,
            ct: *const u8,
            sk: *const u8,
        ) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM1024_check_pk(pk: *const u8) -> i32;

        pub fn PQCP_MLKEM_NATIVE_MLKEM1024_check_sk(sk: *const u8) -> i32;
    }
}
