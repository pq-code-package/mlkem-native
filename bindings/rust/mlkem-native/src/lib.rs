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
        check_sk        = $check_sk:ident $(,)?
    ) => {
        pub mod $module {
            use hybrid_array::Array;
            use kem::{
                common::{Generate, InvalidKey, KeyExport, KeySizeUser, TryKeyInit},
                Ciphertext, Decapsulate, Encapsulate, Kem, SharedKey,
            };
            use mlkem_native_sys::$sys_mod::{
                $check_pk, $check_sk, $dec, $enc_derand, $keypair_derand,
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
                    f.debug_tuple("EncapsulationKey").field(&self.0.as_ref()).finish()
                }
            }

            impl KeySizeUser for EncapsulationKey {
                type KeySize = $pk_size;
            }

            impl TryKeyInit for EncapsulationKey {
                fn new(key: &Array<u8, $pk_size>) -> Result<Self, InvalidKey> {
                    let mut arr = [0u8; $pk_len];
                    arr.copy_from_slice(key.as_slice());
                    let ek = Self(arr);
                    let ret = unsafe { $check_pk(ek.0.as_ptr()) };
                    if ret != 0 { Err(InvalidKey) } else { Ok(ek) }
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
                /// Returns the raw byte encoding of this secret key.
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
                    Ok(Self { sk, ek: EncapsulationKey(pk) })
                }
            }

            impl TryFrom<&[u8]> for DecapsulationKey {
                type Error = InvalidKey;

                /// Parse and validate a secret key from bytes.
                ///
                /// The encapsulation key is extracted from its embedded position
                /// in the secret key (per FIPS 203 §3.3).
                fn try_from(bytes: &[u8]) -> Result<Self, InvalidKey> {
                    let arr: [u8; $sk_len] = bytes.try_into().map_err(|_| InvalidKey)?;
                    let ret = unsafe { $check_sk(arr.as_ptr()) };
                    if ret != 0 {
                        return Err(InvalidKey);
                    }
                    let mut pk = [0u8; $pk_len];
                    pk.copy_from_slice(&arr[$ek_start..$ek_start + $pk_len]);
                    Ok(Self { sk: arr, ek: EncapsulationKey(pk) })
                }
            }

            impl TryFrom<&[u8]> for EncapsulationKey {
                type Error = InvalidKey;

                fn try_from(bytes: &[u8]) -> Result<Self, InvalidKey> {
                    let arr: [u8; $pk_len] = bytes.try_into().map_err(|_| InvalidKey)?;
                    let ek = Self(arr);
                    let ret = unsafe { $check_pk(ek.0.as_ptr()) };
                    if ret != 0 { Err(InvalidKey) } else { Ok(ek) }
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
