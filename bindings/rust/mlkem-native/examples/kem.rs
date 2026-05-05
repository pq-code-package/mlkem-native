// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! Demonstrates key generation, encapsulation, and decapsulation for all
//! three ML-KEM parameter sets using the system's secure RNG.
//!
//! Run with:
//!   cargo run --example kem

use mlkem_native::{
    kem::{Decapsulate, Encapsulate, Kem},
    mlkem1024, mlkem512, mlkem768,
};

fn demo<K: Kem>(name: &str)
where
    K::EncapsulationKey: Encapsulate<Kem = K>,
    K::DecapsulationKey: Decapsulate<Kem = K>,
{
    // Alice generates a keypair. The decapsulation key is kept secret;
    // the encapsulation key is shared with the sender.
    let (dk, ek) = K::generate_keypair();

    // Bob encapsulates a fresh shared secret to Alice's encapsulation key.
    // `ct` is the ciphertext sent to Alice; `ss_sender` is Bob's share.
    let (ct, ss_sender) = ek.encapsulate();

    // Alice decapsulates the ciphertext to recover the shared secret.
    let ss_receiver = dk.decapsulate(&ct);

    assert_eq!(ss_sender, ss_receiver, "{name}: shared secrets must match");

    println!(
        "{name}: shared secret ({} bytes) established successfully",
        ss_sender.as_slice().len()
    );
}

fn main() {
    demo::<mlkem512::MlKem>("ML-KEM-512");
    demo::<mlkem768::MlKem>("ML-KEM-768");
    demo::<mlkem1024::MlKem>("ML-KEM-1024");
}
