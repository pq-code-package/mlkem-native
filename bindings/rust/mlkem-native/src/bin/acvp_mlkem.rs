// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! ACVP test harness for ML-KEM using the safe `mlkem-native` Rust API.
//!
//! Usage: acvp_mlkem <512|768|1024> [encapDecap|keyGen] [AFT|VAL] {test specific arguments}
//!
//! Matches the CLI interface of test/acvp/acvp_mlkem.c, with the security
//! level prepended as an additional leading argument (since this single binary
//! covers all three parameter sets).

use std::process;

use rand_core::{TryCryptoRng, TryRng};

const SYMBYTES: usize = 32;

fn decode_hex_char(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'A'..=b'F' => Some(10 + c - b'A'),
        b'a'..=b'f' => Some(10 + c - b'a'),
        _ => None,
    }
}

/// Decode a `prefix=HEXSTRING` CLI argument into exactly `expected_len` bytes.
/// Returns `Err(())` and prints a diagnostic to stderr on failure.
fn decode_hex(prefix: &str, arg: &str, expected_len: usize) -> Result<Vec<u8>, ()> {
    let full_prefix = format!("{}=", prefix);
    let hex = match arg.strip_prefix(&full_prefix) {
        Some(h) => h,
        None => {
            eprintln!(
                "Argument {} invalid: Expected argument of the form '{}=HEX' with \
                 HEX being a hex encoding of {} bytes",
                arg, prefix, expected_len
            );
            return Err(());
        }
    };

    if hex.len() != 2 * expected_len {
        eprintln!(
            "Argument {} invalid: Expected {}=HEX with HEX being a hex encoding of {} bytes",
            arg, prefix, expected_len
        );
        return Err(());
    }

    hex.as_bytes()
        .chunks(2)
        .map(|chunk| match (decode_hex_char(chunk[0]), decode_hex_char(chunk[1])) {
            (Some(hi), Some(lo)) => Ok((hi << 4) | lo),
            _ => {
                eprintln!("Argument {} invalid: non-hex character in value", arg);
                Err(())
            }
        })
        .collect()
}

fn die_usage(msg: &str) -> ! {
    eprintln!("{}", msg);
    process::exit(1);
}

fn print_hex(name: &str, data: &[u8]) {
    print!("{}=", name);
    for b in data {
        print!("{:02X}", b);
    }
    println!();
}

/// A deterministic RNG that replays a fixed byte string exactly once.
///
/// Used to feed caller-supplied randomness into the standard `encapsulate_with_rng`
/// and `try_generate_from_rng` APIs, giving the same result as the dedicated
/// `_derand` entry points in the C library.
struct FixedRng<'a>(&'a [u8]);

impl TryRng for FixedRng<'_> {
    type Error = core::convert::Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut b = [0u8; 4];
        self.try_fill_bytes(&mut b)?;
        Ok(u32::from_le_bytes(b))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut b = [0u8; 8];
        self.try_fill_bytes(&mut b)?;
        Ok(u64::from_le_bytes(b))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        let n = dst.len();
        dst.copy_from_slice(&self.0[..n]);
        self.0 = &self.0[n..];
        Ok(())
    }
}

// Not a real CSPRNG — only used with caller-supplied test vectors where the
// ACVP protocol requires deterministic, reproduced output.
impl TryCryptoRng for FixedRng<'_> {}

/// Core ACVP logic for one security level, using only the safe mlkem-native API.
macro_rules! run_level {
    (
        module = $module:ident,
        pk_len = $pk_len:literal,
        sk_len = $sk_len:literal,
        ct_len = $ct_len:literal,
        args   = $args:expr
    ) => {{
        use mlkem_native::kem::common::{Generate, KeyExport};
        use mlkem_native::kem::{Ciphertext, Decapsulate, Decapsulator, Encapsulate};
        use mlkem_native::$module::{DecapsulationKey, EncapsulationKey, MlKem};

        let args: &[String] = $args;

        const USAGE: &str =
            "acvp_mlkem<lvl> [encapDecap|keyGen] [AFT|VAL] {test specific arguments}";
        const ENCAPS_USAGE: &str =
            "acvp_mlkem<lvl> encapDecap AFT encapsulation ek=HEX m=HEX";
        const DECAPS_USAGE: &str =
            "acvp_mlkem<lvl> encapDecap VAL decapsulation dk=HEX c=HEX";
        const EK_CHECK_USAGE: &str =
            "acvp_mlkem<lvl> encapDecap VAL encapsulationKeyCheck ek=HEX";
        const DK_CHECK_USAGE: &str =
            "acvp_mlkem<lvl> encapDecap VAL decapsulationKeyCheck dk=HEX";
        const KEYGEN_USAGE: &str = "acvp_mlkem<lvl> keyGen AFT z=HEX d=HEX";

        if args.is_empty() {
            die_usage(USAGE);
        }

        match args[0].as_str() {
            "encapDecap" => {
                let args = &args[1..];
                if args.len() < 2 {
                    die_usage(
                        "acvp_mlkem<lvl> encapDecap [AFT|VAL] \
                         [encapsulation|decapsulation|\
                         encapsulationKeyCheck|decapsulationKeyCheck] ...",
                    );
                }
                let test_type = args[0].as_str();
                let function = args[1].as_str();
                let args = &args[2..];

                match (test_type, function) {
                    ("AFT", "encapsulation") => {
                        if args.len() < 2 {
                            die_usage(ENCAPS_USAGE);
                        }
                        let ek_bytes = decode_hex("ek", &args[0], $pk_len)
                            .unwrap_or_else(|_| die_usage(ENCAPS_USAGE));
                        let m_bytes = decode_hex("m", &args[1], SYMBYTES)
                            .unwrap_or_else(|_| die_usage(ENCAPS_USAGE));
                        let ek = EncapsulationKey::try_from(ek_bytes.as_slice())
                            .unwrap_or_else(|_| die_usage(ENCAPS_USAGE));
                        let (ct, ss) = ek.encapsulate_with_rng(&mut FixedRng(&m_bytes));
                        print_hex("c", ct.as_slice());
                        print_hex("k", ss.as_slice());
                    }
                    ("VAL", "decapsulation") => {
                        if args.len() < 2 {
                            die_usage(DECAPS_USAGE);
                        }
                        let dk_bytes = decode_hex("dk", &args[0], $sk_len)
                            .unwrap_or_else(|_| die_usage(DECAPS_USAGE));
                        let c_bytes = decode_hex("c", &args[1], $ct_len)
                            .unwrap_or_else(|_| die_usage(DECAPS_USAGE));
                        let dk = DecapsulationKey::try_from(dk_bytes.as_slice())
                            .unwrap_or_else(|_| die_usage(DECAPS_USAGE));
                        let mut ct = Ciphertext::<MlKem>::default();
                        ct.as_mut_slice().copy_from_slice(&c_bytes);
                        let ss = dk.decapsulate(&ct);
                        print_hex("k", ss.as_slice());
                    }
                    ("VAL", "encapsulationKeyCheck") => {
                        if args.is_empty() {
                            die_usage(EK_CHECK_USAGE);
                        }
                        // ACVP 1.1.0.40+ sends keys of wrong length to test rejection;
                        // a decode failure is reported as testPassed=0.
                        let ek_bytes = match decode_hex("ek", &args[0], $pk_len) {
                            Ok(v) => v,
                            Err(_) => {
                                println!("testPassed=0");
                                return;
                            }
                        };
                        // Importing via try_from runs the FIPS 203 §7.2 modulus check.
                        let passed = EncapsulationKey::try_from(ek_bytes.as_slice()).is_ok();
                        println!("testPassed={}", if passed { 1 } else { 0 });
                    }
                    ("VAL", "decapsulationKeyCheck") => {
                        if args.is_empty() {
                            die_usage(DK_CHECK_USAGE);
                        }
                        // ACVP 1.1.0.40+ sends keys of wrong length to test rejection.
                        let dk_bytes = match decode_hex("dk", &args[0], $sk_len) {
                            Ok(v) => v,
                            Err(_) => {
                                println!("testPassed=0");
                                return;
                            }
                        };
                        // Importing via try_from runs the FIPS 203 §7.3 hash check.
                        let passed = DecapsulationKey::try_from(dk_bytes.as_slice()).is_ok();
                        println!("testPassed={}", if passed { 1 } else { 0 });
                    }
                    _ => die_usage(USAGE),
                }
            }
            "keyGen" => {
                let args = &args[1..];
                if args.is_empty() || args[0] != "AFT" || args.len() < 3 {
                    die_usage(KEYGEN_USAGE);
                }
                let z = decode_hex("z", &args[1], SYMBYTES)
                    .unwrap_or_else(|_| die_usage(KEYGEN_USAGE));
                let d = decode_hex("d", &args[2], SYMBYTES)
                    .unwrap_or_else(|_| die_usage(KEYGEN_USAGE));
                // coins = d || z  (matches the C reference: zd[0..32]=d, zd[32..64]=z)
                let mut coins = [0u8; 64];
                coins[..32].copy_from_slice(&d);
                coins[32..].copy_from_slice(&z);
                let dk = DecapsulationKey::try_generate_from_rng(&mut FixedRng(&coins))
                    .unwrap_or_else(|e| match e {});
                print_hex("ek", dk.encapsulation_key().to_bytes().as_slice());
                print_hex("dk", dk.as_bytes());
            }
            _ => die_usage(USAGE),
        }
    }};
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        die_usage(
            "Usage: acvp_mlkem <512|768|1024> [encapDecap|keyGen] [AFT|VAL] \
             {test specific arguments}",
        );
    }

    let level: u32 = args[1]
        .parse()
        .unwrap_or_else(|_| die_usage("Invalid security level: expected 512, 768, or 1024"));

    let rest = &args[2..];

    match level {
        512 => run_level!(
            module = mlkem512,
            pk_len = 800,
            sk_len = 1632,
            ct_len = 768,
            args   = rest
        ),
        768 => run_level!(
            module = mlkem768,
            pk_len = 1184,
            sk_len = 2400,
            ct_len = 1088,
            args   = rest
        ),
        1024 => run_level!(
            module = mlkem1024,
            pk_len = 1568,
            sk_len = 3168,
            ct_len = 1568,
            args   = rest
        ),
        _ => die_usage("Invalid security level: expected 512, 768, or 1024"),
    }
}
