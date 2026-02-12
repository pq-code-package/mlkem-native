(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-KEM subroutine signatures for constant-time proofs.                    *)
(* Trimmed version of s2n-bignum's arm/proofs/subroutine_signatures.ml.      *)
(* ========================================================================= *)

let subroutine_signatures = [
("mlkem_basemul_k2",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "int16_t[static 512]", (*is const?*)"true");
     ("b", "int16_t[static 512]", (*is const?*)"true");
     ("bt", "int16_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "512"(* num elems *), 2(* elem bytesize *));
    ("b", "512"(* num elems *), 2(* elem bytesize *));
    ("bt", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_basemul_k3",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "int16_t[static 768]", (*is const?*)"true");
     ("b", "int16_t[static 768]", (*is const?*)"true");
     ("bt", "int16_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "768"(* num elems *), 2(* elem bytesize *));
    ("b", "768"(* num elems *), 2(* elem bytesize *));
    ("bt", "384"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_basemul_k4",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "int16_t[static 1024]", (*is const?*)"true");
     ("b", "int16_t[static 1024]", (*is const?*)"true");
     ("bt", "int16_t[static 512]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "1024"(* num elems *), 2(* elem bytesize *));
    ("b", "1024"(* num elems *), 2(* elem bytesize *));
    ("bt", "512"(* num elems *), 2(* elem bytesize *));
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
     ("z_01234", "int16_t[static 80]", (*is const?*)"true");
     ("z_56", "int16_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("z_01234", "80"(* num elems *), 2(* elem bytesize *));
    ("z_56", "384"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_mulcache_compute",
  ([(*args*)
     ("x", "int16_t[static 128]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
     ("z", "int16_t[static 128]", (*is const?*)"true");
     ("t", "int16_t[static 128]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("z", "128"(* num elems *), 2(* elem bytesize *));
    ("t", "128"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("x", "128"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_ntt",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
     ("z_01234", "int16_t[static 80]", (*is const?*)"true");
     ("z_56", "int16_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("z_01234", "80"(* num elems *), 2(* elem bytesize *));
    ("z_56", "384"(* num elems *), 2(* elem bytesize *));
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
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("buf", "uint8_t*", (*is const?*)"true");
     ("buflen", "uint64_t", (*is const?*)"false");
     ("table", "uint8_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
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

];;
