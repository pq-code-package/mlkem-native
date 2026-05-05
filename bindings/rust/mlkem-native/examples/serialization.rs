// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! Demonstrates serialization and deserialization of ML-KEM keys.
//!
//! Run with:
//!   cargo run --example serialization

use mlkem_native::{
    kem::{Decapsulate, Encapsulate, KeyExport, Kem},
    mlkem768::{DecapsulationKey, EncapsulationKey, MlKem},
};

fn main() {
    // Generate a fresh keypair.
    let (dk, ek) = MlKem::generate_keypair();

    // --- Serialize ---
    let ek_bytes: Vec<u8> = ek.to_bytes().to_vec(); // 1184 bytes
    let dk_bytes: Vec<u8> = dk.as_bytes().to_vec(); // 2400 bytes

    println!("ek: {} bytes", ek_bytes.len());
    println!("dk: {} bytes", dk_bytes.len());

    // --- Deserialize ---
    // Both constructors validate the key (check_pk / check_sk) and return
    // Err(InvalidKey) if the bytes are the wrong length or fail validation.
    let ek2 = EncapsulationKey::try_from(ek_bytes.as_slice()).expect("valid ek");
    let dk2 = DecapsulationKey::try_from(dk_bytes.as_slice()).expect("valid dk");

    // Verify the round-tripped keys still work correctly.
    let (ct, ss_sender) = ek2.encapsulate();
    let ss_receiver = dk2.decapsulate(&ct);
    assert_eq!(ss_sender, ss_receiver, "shared secrets must match after round-trip");

    println!("Round-trip successful — shared secret established.");
}
