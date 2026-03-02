(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-KEM x86_64 subroutine signatures for constant-time proofs.            *)
(* Trimmed version of s2n-bignum's x86/proofs/subroutine_signatures.ml.     *)
(* ========================================================================= *)

let subroutine_signatures = [
("mlkem_basemul_k2",
  ([(*args*)
     ("dst", "int16_t[static 256]", (*is const?*)"false");
     ("src1", "int16_t[static 512]", (*is const?*)"true");
     ("src2", "int16_t[static 512]", (*is const?*)"true");
     ("src2t", "int16_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("src1", "512"(* num elems *), 2(* elem bytesize *));
    ("src2", "512"(* num elems *), 2(* elem bytesize *));
    ("src2t", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("dst", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_basemul_k3",
  ([(*args*)
     ("dst", "int16_t[static 256]", (*is const?*)"false");
     ("src1", "int16_t[static 768]", (*is const?*)"true");
     ("src2", "int16_t[static 768]", (*is const?*)"true");
     ("src2t", "int16_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("src1", "768"(* num elems *), 2(* elem bytesize *));
    ("src2", "768"(* num elems *), 2(* elem bytesize *));
    ("src2t", "384"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("dst", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_basemul_k4",
  ([(*args*)
     ("dst", "int16_t[static 256]", (*is const?*)"false");
     ("src1", "int16_t[static 1024]", (*is const?*)"true");
     ("src2", "int16_t[static 1024]", (*is const?*)"true");
     ("src2t", "int16_t[static 512]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("src1", "1024"(* num elems *), 2(* elem bytesize *));
    ("src2", "1024"(* num elems *), 2(* elem bytesize *));
    ("src2t", "512"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("dst", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_frombytes",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "uint8_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "384"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_intt",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
     ("zetas", "int16_t[static 624]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("zetas", "624"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_mulcache_compute",
  ([(*args*)
     ("r", "int16_t[static 128]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
     ("zetas", "int16_t[static 624]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("zetas", "624"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "128"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_ntt",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
     ("zetas", "int16_t[static 624]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("zetas", "624"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_reduce",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_rej_uniform_VARIABLE_TIME",
  ([(*args*)
     ("res", "int16_t[static 256]", (*is const?*)"false");
     ("buf", "uint8_t*", (*is const?*)"true");
     ("buflen", "uint64_t", (*is const?*)"false");
     ("table", "uint8_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
    ("res", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_tobytes",
  ([(*args*)
     ("r", "uint8_t[static 384]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "384"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_tomont",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_unpack",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);


("mlkem_poly_decompress_d4",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "uint8_t[static 128]", (*is const?*)"true");
     ("data", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "128"(* num elems *), 1(* elem bytesize *));
    ("data", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_poly_decompress_d5",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "uint8_t[static 160]", (*is const?*)"true");
     ("data", "uint8_t[static 96]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "160"(* num elems *), 1(* elem bytesize *));
    ("data", "96"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_poly_decompress_d10",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "uint8_t[static 320]", (*is const?*)"true");
     ("data", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "320"(* num elems *), 1(* elem bytesize *));
    ("data", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_poly_decompress_d11",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "uint8_t[static 352]", (*is const?*)"true");
     ("data", "uint8_t[static 128]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "352"(* num elems *), 1(* elem bytesize *));
    ("data", "128"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);


("mlkem_poly_compress_d4",
  ([(*args*)
     ("r", "uint8_t[static 128]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
     ("data", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("data", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "128"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_poly_compress_d5",
  ([(*args*)
     ("r", "uint8_t[static 160]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
     ("data", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("data", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "160"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_poly_compress_d10",
  ([(*args*)
     ("r", "uint8_t[static 320]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
     ("data", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("data", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "320"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_poly_compress_d11",
  ([(*args*)
     ("r", "uint8_t[static 352]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
     ("data", "uint8_t[static 64]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("data", "64"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "352"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);


("keccak_f1600_x4_avx2",
  ([(*args*)
     ("bitstate_in", "uint64_t[static 100]", (*is const?*)"false");
     ("rc_pointer", "const uint64_t[static 24]", (*is const?*)"true");
     ("rho8_ptr", "const uint64_t[static 4]", (*is const?*)"true");
     ("rho56_ptr", "const uint64_t[static 4]", (*is const?*)"true")],
   "void",
   [(* input buffers *)
    ("bitstate_in", "100"(* num elems *), 8(* elem bytesize *));
    ("rc_pointer", "24"(* num elems *), 8(* elem bytesize *));
    ("rho8_ptr", "4"(* num elems *), 8(* elem bytesize *));
    ("rho56_ptr", "4"(* num elems *), 8(* elem bytesize *))],
   [(* output buffers *)
    ("bitstate_in", "100"(* num elems *), 8(* elem bytesize *))],
   [(* temporary buffers *)
   ])
);

];;
