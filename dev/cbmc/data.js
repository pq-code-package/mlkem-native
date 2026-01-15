window.BENCHMARK_DATA = {
  "lastUpdate": 1768463669692,
  "repoUrl": "https://github.com/pq-code-package/mlkem-native",
  "entries": {
    "CBMC Runtime (ML-KEM-1024)": [
      {
        "commit": {
          "author": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "committer": {
            "name": "pq-code-package",
            "username": "pq-code-package"
          },
          "id": "45915e14a00bd6d04bec0f3df1d8fac6e9e47cb9",
          "message": "CI: Comment on PRs if CBMC proofs fail",
          "timestamp": "2026-01-13T21:45:38Z",
          "url": "https://github.com/pq-code-package/mlkem-native/pull/1478/commits/45915e14a00bd6d04bec0f3df1d8fac6e9e47cb9"
        },
        "date": 1768463588638,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "mlk_poly_tomont",
            "value": 999999,
            "unit": "seconds",
            "extra": "Failed in 2 seconds"
          },
          {
            "name": "mlk_poly_tomont_native",
            "value": 999999,
            "unit": "seconds",
            "extra": "Failed in 2 seconds"
          },
          {
            "name": "mlk_poly_tobytes",
            "value": 1,
            "unit": "seconds"
          },
          {
            "name": "mlk_poly_tobytes_c",
            "value": 1,
            "unit": "seconds"
          },
          {
            "name": "mlk_poly_tobytes_native",
            "value": 3,
            "unit": "seconds"
          },
          {
            "name": "mlk_poly_tomont_c",
            "value": 2,
            "unit": "seconds"
          },
          {
            "name": "mlk_poly_tomsg",
            "value": 5,
            "unit": "seconds"
          },
          {
            "name": "poly_tobytes_native_aarch64",
            "value": 1,
            "unit": "seconds"
          },
          {
            "name": "poly_tomont_native_aarch64",
            "value": 3,
            "unit": "seconds"
          }
        ]
      }
    ]
  }
}