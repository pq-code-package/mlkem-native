// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! ML-KEM (FIPS 203) implemented via [mlkem-native], exposing the
//! [RustCrypto KEM traits].
//!
//! All three parameter sets are provided as submodules:
//! - [`mlkem512`]  — NIST security level 1
//! - [`mlkem768`]  — NIST security level 3
//! - [`mlkem1024`] — NIST security level 5
//!
//! Each submodule exposes a marker struct `MlKem` implementing [`kem::Kem`],
//! plus `EncapsulationKey` and `DecapsulationKey` types.
//!
//! # Example
//!
//! ```rust,ignore
//! use mlkem_native::{kem::{Decapsulate, Encapsulate, Kem}, mlkem768};
//!
//! // Key generation (uses system RNG; requires the `getrandom` feature on `kem`).
//! let (dk, ek) = mlkem768::MlKem::generate_keypair();
//!
//! // Encapsulate a shared secret to the recipient's public key.
//! let (ct, ss_sender) = ek.encapsulate();
//!
//! // Decapsulate to recover the same shared secret.
//! let ss_receiver = dk.decapsulate(&ct);
//!
//! assert_eq!(ss_sender.as_slice(), ss_receiver.as_slice());
//! ```
//!
//! [mlkem-native]: https://github.com/pq-code-package/mlkem-native
//! [RustCrypto KEM traits]: https://crates.io/crates/kem

#![no_std]

pub use kem;

mod sys;

macro_rules! define_mlkem {
    (
        module          = $module:ident,
        sys_mod         = $sys_mod:ident,
        pk_len          = $pk_len:literal,
        sk_len          = $sk_len:literal,
        ek_start        = $ek_start:literal,
        pk_size         = $pk_size:ty,
        ct_size         = $ct_size:ty,
        keypair_derand  = $keypair_derand:ident,
        enc_derand      = $enc_derand:ident,
        dec             = $dec:ident,
        check_pk        = $check_pk:ident,
        check_sk        = $check_sk:ident,
    ) => {
        pub mod $module {
            use crate::sys::$sys_mod::{$check_pk, $check_sk, $dec, $enc_derand, $keypair_derand};
            use hybrid_array::Array;
            use kem::{
                common::{Generate, InvalidKey, KeyExport, KeySizeUser, TryKeyInit},
                Ciphertext, Decapsulate, Encapsulate, Kem, SharedKey,
            };
            use rand_core::{CryptoRng, TryCryptoRng};

            /// Marker struct for this ML-KEM parameter set; implements [`Kem`].
            #[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
            pub struct MlKem;

            impl Kem for MlKem {
                type DecapsulationKey = DecapsulationKey;
                type EncapsulationKey = EncapsulationKey;
                type SharedKeySize = hybrid_array::typenum::U32;
                type CiphertextSize = $ct_size;
            }

            /// The encapsulation (public) key.
            #[derive(Clone, PartialEq, Eq)]
            pub struct EncapsulationKey([u8; $pk_len]);

            impl core::fmt::Debug for EncapsulationKey {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.debug_tuple("EncapsulationKey")
                        .field(&self.0.as_ref())
                        .finish()
                }
            }

            impl KeySizeUser for EncapsulationKey {
                type KeySize = $pk_size;
            }

            impl TryKeyInit for EncapsulationKey {
                fn new(key: &Array<u8, $pk_size>) -> Result<Self, InvalidKey> {
                    Self::try_from(key.as_slice())
                }
            }

            impl KeyExport for EncapsulationKey {
                fn to_bytes(&self) -> Array<u8, $pk_size> {
                    let mut out = Array::<u8, $pk_size>::default();
                    out.copy_from_slice(&self.0);
                    out
                }
            }

            impl Encapsulate for EncapsulationKey {
                type Kem = MlKem;

                fn encapsulate_with_rng<R: CryptoRng + ?Sized>(
                    &self,
                    rng: &mut R,
                ) -> (Ciphertext<MlKem>, SharedKey<MlKem>) {
                    let mut ct = Ciphertext::<MlKem>::default();
                    let mut ss = SharedKey::<MlKem>::default();
                    let mut coins = [0u8; 32]; // MLKEM_SYMBYTES
                    rng.fill_bytes(&mut coins);
                    let ret = unsafe {
                        $enc_derand(
                            ct.as_mut_slice().as_mut_ptr(),
                            ss.as_mut_slice().as_mut_ptr(),
                            self.0.as_ptr(),
                            coins.as_ptr(),
                        )
                    };
                    assert_eq!(ret, 0, "enc_derand failed — key may have been corrupted");
                    (ct, ss)
                }
            }

            /// The decapsulation (secret) key.
            ///
            /// The encapsulation key is stored alongside to support
            /// [`kem::Decapsulator::encapsulation_key`].
            pub struct DecapsulationKey {
                sk: [u8; $sk_len],
                ek: EncapsulationKey,
            }

            impl DecapsulationKey {
                pub fn as_bytes(&self) -> &[u8] {
                    &self.sk
                }
            }

            impl core::fmt::Debug for DecapsulationKey {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.write_str("DecapsulationKey([redacted])")
                }
            }

            impl kem::Decapsulator for DecapsulationKey {
                type Kem = MlKem;

                fn encapsulation_key(&self) -> &EncapsulationKey {
                    &self.ek
                }
            }

            impl Decapsulate for DecapsulationKey {
                fn decapsulate(&self, ct: &Ciphertext<MlKem>) -> SharedKey<MlKem> {
                    let mut ss = SharedKey::<MlKem>::default();
                    // ML-KEM decapsulation always produces a value (implicit rejection
                    // for invalid ciphertexts per FIPS 203 §8.3); non-zero only if the
                    // hash check on the secret key fails, which is guarded against on
                    // construction.
                    let ret = unsafe {
                        $dec(
                            ss.as_mut_slice().as_mut_ptr(),
                            ct.as_slice().as_ptr(),
                            self.sk.as_ptr(),
                        )
                    };
                    assert_eq!(ret, 0, "dec failed — key may have been corrupted");
                    ss
                }
            }

            impl Generate for DecapsulationKey {
                fn try_generate_from_rng<R: TryCryptoRng + ?Sized>(
                    rng: &mut R,
                ) -> Result<Self, R::Error> {
                    let mut pk = [0u8; $pk_len];
                    let mut sk = [0u8; $sk_len];
                    let mut coins = [0u8; 64]; // 2 × MLKEM_SYMBYTES
                    rng.try_fill_bytes(&mut coins)?;
                    let ret = unsafe {
                        $keypair_derand(pk.as_mut_ptr(), sk.as_mut_ptr(), coins.as_ptr())
                    };
                    assert_eq!(ret, 0, "keypair_derand failed unexpectedly");
                    Ok(Self {
                        sk,
                        ek: EncapsulationKey(pk),
                    })
                }
            }

            impl TryFrom<&[u8]> for DecapsulationKey {
                type Error = InvalidKey;

                fn try_from(bytes: &[u8]) -> Result<Self, InvalidKey> {
                    let arr: [u8; $sk_len] = bytes.try_into().map_err(|_| InvalidKey)?;
                    if unsafe { $check_sk(arr.as_ptr()) } != 0 {
                        return Err(InvalidKey);
                    }
                    let mut pk = [0u8; $pk_len];
                    pk.copy_from_slice(&arr[$ek_start..$ek_start + $pk_len]);
                    Ok(Self {
                        sk: arr,
                        ek: EncapsulationKey::try_from(pk.as_slice())?,
                    })
                }
            }

            impl TryFrom<&[u8]> for EncapsulationKey {
                type Error = InvalidKey;

                fn try_from(bytes: &[u8]) -> Result<Self, InvalidKey> {
                    let arr: [u8; $pk_len] = bytes.try_into().map_err(|_| InvalidKey)?;
                    let key = Self(arr);
                    if unsafe { $check_pk(key.0.as_ptr()) } != 0 {
                        return Err(InvalidKey);
                    }
                    Ok(key)
                }
            }
        }
    };
}

define_mlkem! {
    module          = mlkem512,
    sys_mod         = mlkem512,
    pk_len          = 800,
    sk_len          = 1632,
    ek_start        = 768,
    pk_size         = hybrid_array::typenum::U800,
    ct_size         = hybrid_array::typenum::U768,
    keypair_derand  = PQCP_MLKEM_NATIVE_MLKEM512_keypair_derand,
    enc_derand      = PQCP_MLKEM_NATIVE_MLKEM512_enc_derand,
    dec             = PQCP_MLKEM_NATIVE_MLKEM512_dec,
    check_pk        = PQCP_MLKEM_NATIVE_MLKEM512_check_pk,
    check_sk        = PQCP_MLKEM_NATIVE_MLKEM512_check_sk,
}

define_mlkem! {
    module          = mlkem768,
    sys_mod         = mlkem768,
    pk_len          = 1184,
    sk_len          = 2400,
    ek_start        = 1152,
    pk_size         = hybrid_array::sizes::U1184,
    ct_size         = hybrid_array::sizes::U1088,
    keypair_derand  = PQCP_MLKEM_NATIVE_MLKEM768_keypair_derand,
    enc_derand      = PQCP_MLKEM_NATIVE_MLKEM768_enc_derand,
    dec             = PQCP_MLKEM_NATIVE_MLKEM768_dec,
    check_pk        = PQCP_MLKEM_NATIVE_MLKEM768_check_pk,
    check_sk        = PQCP_MLKEM_NATIVE_MLKEM768_check_sk,
}

define_mlkem! {
    module          = mlkem1024,
    sys_mod         = mlkem1024,
    pk_len          = 1568,
    sk_len          = 3168,
    ek_start        = 1536,
    pk_size         = hybrid_array::sizes::U1568,
    ct_size         = hybrid_array::sizes::U1568,
    keypair_derand  = PQCP_MLKEM_NATIVE_MLKEM1024_keypair_derand,
    enc_derand      = PQCP_MLKEM_NATIVE_MLKEM1024_enc_derand,
    dec             = PQCP_MLKEM_NATIVE_MLKEM1024_dec,
    check_pk        = PQCP_MLKEM_NATIVE_MLKEM1024_check_pk,
    check_sk        = PQCP_MLKEM_NATIVE_MLKEM1024_check_sk,
}

#[cfg(test)]
mod tests {
    // Each parameter set gets the same suite of tests, generated by this macro.
    //
    // Arguments:
    //   $module  — one of mlkem512 / mlkem768 / mlkem1024
    //   $pk_len  — public-key (encapsulation key) byte length
    //   $sk_len  — secret-key (decapsulation key) byte length
    macro_rules! define_kem_tests {
        ($module:ident, $pk_len:literal, $sk_len:literal) => {
            mod $module {
                use crate::$module::{DecapsulationKey, EncapsulationKey, MlKem};
                use kem::{Decapsulate, Encapsulate, Kem, KeyExport};

                // ── Core KEM correctness ──────────────────────────────────

                /// Encapsulation followed by decapsulation must recover the
                /// same shared secret.
                #[test]
                fn roundtrip() {
                    let (dk, ek) = MlKem::generate_keypair();
                    let (ct, ss_enc) = ek.encapsulate();
                    let ss_dec = dk.decapsulate(&ct);
                    assert_eq!(ss_enc, ss_dec);
                }

                /// Decapsulating with the *wrong* secret key must not recover
                /// the sender's shared secret (FIPS 203 implicit rejection).
                #[test]
                fn wrong_key_implicit_rejection() {
                    let (dk1, _) = MlKem::generate_keypair();
                    let (_, ek2) = MlKem::generate_keypair();
                    let (ct, ss_enc) = ek2.encapsulate();
                    let ss_wrong = dk1.decapsulate(&ct);
                    assert_ne!(ss_enc, ss_wrong);
                }

                /// Flipping a bit in the ciphertext must not recover the
                /// sender's shared secret (FIPS 203 implicit rejection).
                #[test]
                fn tampered_ciphertext_implicit_rejection() {
                    let (dk, ek) = MlKem::generate_keypair();
                    let (mut ct, ss_enc) = ek.encapsulate();
                    ct.as_mut_slice()[0] ^= 0x01;
                    let ss_dec = dk.decapsulate(&ct);
                    assert_ne!(ss_enc, ss_dec);
                }

                // ── Key sizes ─────────────────────────────────────────────

                #[test]
                fn key_byte_lengths() {
                    let (dk, ek) = MlKem::generate_keypair();
                    assert_eq!(ek.to_bytes().len(), $pk_len);
                    assert_eq!(dk.as_bytes().len(), $sk_len);
                }

                // ── Serialization round-trips ─────────────────────────────

                /// A serialized then deserialized encapsulation key must be
                /// equal to the original and must still produce a ciphertext
                /// that the original decapsulation key can open.
                #[test]
                fn encapsulation_key_serialization() {
                    let (dk, ek) = MlKem::generate_keypair();
                    let ek_bytes = ek.to_bytes();
                    let ek2 = EncapsulationKey::try_from(ek_bytes.as_slice())
                        .expect("deserialization of a freshly exported key must succeed");
                    assert_eq!(ek, ek2);
                    let (ct, ss_enc) = ek2.encapsulate();
                    let ss_dec = dk.decapsulate(&ct);
                    assert_eq!(ss_enc, ss_dec);
                }

                /// A serialized then deserialized decapsulation key must still
                /// open ciphertexts produced for the corresponding
                /// encapsulation key.
                #[test]
                fn decapsulation_key_serialization() {
                    let (dk, ek) = MlKem::generate_keypair();
                    let dk2 = DecapsulationKey::try_from(dk.as_bytes())
                        .expect("deserialization of a freshly exported key must succeed");
                    let (ct, ss_enc) = ek.encapsulate();
                    let ss_dec = dk2.decapsulate(&ct);
                    assert_eq!(ss_enc, ss_dec);
                }

                // ── Invalid-length inputs ─────────────────────────────────

                #[test]
                fn encapsulation_key_wrong_length() {
                    assert!(
                        EncapsulationKey::try_from(&[0u8; $pk_len - 1][..]).is_err(),
                        "one byte short should be InvalidKey"
                    );
                    assert!(
                        EncapsulationKey::try_from(&[0u8; $pk_len + 1][..]).is_err(),
                        "one byte long should be InvalidKey"
                    );
                }

                #[test]
                fn decapsulation_key_wrong_length() {
                    assert!(
                        DecapsulationKey::try_from(&[0u8; $sk_len - 1][..]).is_err(),
                        "one byte short should be InvalidKey"
                    );
                    assert!(
                        DecapsulationKey::try_from(&[0u8; $sk_len + 1][..]).is_err(),
                        "one byte long should be InvalidKey"
                    );
                }

                // ── Key corruption rejection ──────────────────────────────

                /// Flipping a bit in the stored H(ek) section of a decapsulation
                /// key must cause `try_from` to return `Err` (FIPS 203 §7.3).
                ///
                /// H(ek) occupies the 32 bytes at `sk_len - 64`. Any single-bit
                /// change there makes the hash comparison fail.
                #[test]
                fn corrupted_decapsulation_key_rejected() {
                    let (dk, _) = MlKem::generate_keypair();
                    let mut dk_bytes = dk.as_bytes().to_vec();
                    dk_bytes[$sk_len - 64] ^= 1;
                    assert!(
                        DecapsulationKey::try_from(dk_bytes.as_slice()).is_err(),
                        "a bit-flipped H(ek) must be rejected by the hash check"
                    );
                }

                /// Corrupting an encapsulation key so that a polynomial
                /// coefficient exceeds q must cause `try_from` to return `Err`
                /// (FIPS 203 §7.2).
                ///
                /// Byte 1 holds bits [11:8] of the first coefficient in its
                /// lower nibble. Valid values are at most 0xD (q-1 = 3328 =
                /// 0xD00), so ORing with 0x0E forces the nibble to be at least
                /// 0xE (≥ 0xE00 = 3584 > q), regardless of the original value.
                #[test]
                fn corrupted_encapsulation_key_rejected() {
                    let (_, ek) = MlKem::generate_keypair();
                    let mut ek_bytes = ek.to_bytes().to_vec();
                    ek_bytes[1] |= 0x0E;
                    assert!(
                        EncapsulationKey::try_from(ek_bytes.as_slice()).is_err(),
                        "an out-of-range coefficient must be rejected by the modulus check"
                    );
                }
            }
        };
    }

    define_kem_tests!(mlkem512, 800, 1632);
    define_kem_tests!(mlkem768, 1184, 2400);
    define_kem_tests!(mlkem1024, 1568, 3168);
}
