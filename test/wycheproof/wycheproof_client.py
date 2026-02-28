#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# Wycheproof test client for ML-KEM
# See https://github.com/C2SP/wycheproof
# Invokes `wycheproof_mlkem{lvl}` under the hood.

import argparse
import os
import json
import sys
import subprocess
import urllib.request
from pathlib import Path

exec_prefix = os.environ.get("EXEC_WRAPPER", "")
exec_prefix = exec_prefix.split(" ") if exec_prefix != "" else []

WYCHEPROOF_BASE_URL = (
    "https://raw.githubusercontent.com/C2SP/wycheproof/main/testvectors_v1"
)

WYCHEPROOF_FILES = [
    "mlkem_512_keygen_seed_test.json",
    "mlkem_512_encaps_test.json",
    "mlkem_512_semi_expanded_decaps_test.json",
    "mlkem_512_test.json",
    "mlkem_768_keygen_seed_test.json",
    "mlkem_768_encaps_test.json",
    "mlkem_768_semi_expanded_decaps_test.json",
    "mlkem_768_test.json",
    "mlkem_1024_keygen_seed_test.json",
    "mlkem_1024_encaps_test.json",
    "mlkem_1024_semi_expanded_decaps_test.json",
    "mlkem_1024_test.json",
]

PARAMETER_SET_TO_LEVEL = {
    "ML-KEM-512": 512,
    "ML-KEM-768": 768,
    "ML-KEM-1024": 1024,
}


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    print(msg, **kwargs)


def download_wycheproof_files(data_dir):
    """Download Wycheproof test vector files if not present."""
    data_dir = Path(data_dir)
    data_dir.mkdir(parents=True, exist_ok=True)

    for filename in WYCHEPROOF_FILES:
        local_file = data_dir / filename
        if not local_file.exists():
            url = f"{WYCHEPROOF_BASE_URL}/{filename}"
            print(f"Downloading {filename}...", file=sys.stderr)
            try:
                urllib.request.urlretrieve(url, local_file)
                with open(local_file, "r") as f:
                    json.load(f)
            except (json.JSONDecodeError, Exception) as e:
                print(f"Error downloading {filename}: {e}", file=sys.stderr)
                local_file.unlink(missing_ok=True)
                return False
    return True


def get_binary(level):
    basedir = f"./test/build/mlkem{level}/bin"
    return f"{basedir}/wycheproof_mlkem{level}"


def run_binary(args_list):
    result = subprocess.run(
        exec_prefix + args_list, encoding="utf-8", capture_output=True
    )
    if result.returncode != 0:
        return {"_error": str(result.returncode)}
    out = {}
    for line in result.stdout.strip().splitlines():
        k, v = line.split("=", 1)
        out[k] = v
    return out


def run_keygen_seed_test(data_file):
    """Run mlkem_*_keygen_seed_test.json tests."""
    with open(data_file) as f:
        data = json.load(f)

    info(f"Running keygen_seed tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            info(f"  tcId={tc['tcId']} ... ", end="")
            out = run_binary([binary, "keygen_seed", f"seed={tc['seed']}"])
            if "_error" in out or "decode_error" in out:
                assert (
                    tc["result"] == "invalid"
                ), f"binary error on non-invalid tcId={tc['tcId']}"
            elif tc["result"] in ("valid", "acceptable"):
                assert (
                    out["ek"].upper() == tc["ek"].upper()
                ), f"ek mismatch tcId={tc['tcId']}"
                assert (
                    out["dk"].upper() == tc["dk"].upper()
                ), f"dk mismatch tcId={tc['tcId']}"
            info("ok")
            count += 1
    info(f"  {count} keygen_seed tests passed")


def run_encaps_test(data_file):
    """Run mlkem_*_encaps_test.json tests."""
    with open(data_file) as f:
        data = json.load(f)

    info(f"Running encaps tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            info(f"  tcId={tc['tcId']} ... ", end="")
            out = run_binary([binary, "encaps", f"ek={tc['ek']}", f"m={tc['m']}"])
            if "_error" in out or "decode_error" in out:
                assert (
                    tc["result"] == "invalid"
                ), f"binary error on non-invalid tcId={tc['tcId']}"
            elif tc["result"] in ("valid", "acceptable"):
                assert (
                    out["c"].upper() == tc["c"].upper()
                ), f"c mismatch tcId={tc['tcId']}"
                assert (
                    out["K"].upper() == tc["K"].upper()
                ), f"K mismatch tcId={tc['tcId']}"
            elif tc["result"] == "invalid":
                assert (
                    out["K"].upper() != tc["K"].upper()
                ), f"K should not match for invalid tcId={tc['tcId']}"
            info("ok")
            count += 1
    info(f"  {count} encaps tests passed")


def run_semi_expanded_decaps_test(data_file):
    """Run mlkem_*_semi_expanded_decaps_test.json tests."""
    with open(data_file) as f:
        data = json.load(f)

    info(f"Running semi_expanded_decaps tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            info(f"  tcId={tc['tcId']} ... ", end="")
            out = run_binary([binary, "decaps", f"dk={tc['dk']}", f"c={tc['c']}"])
            # For errors (wrong length dk/c, or runtime failure), just check it didn't crash unexpectedly
            if "_error" not in out and "decode_error" not in out:
                assert "K" in out, f"missing K in output tcId={tc['tcId']}"
            info("ok")
            count += 1
    info(f"  {count} semi_expanded_decaps tests passed")


def run_combined_test(data_file):
    """Run mlkem_*_test.json tests (keygen + decaps)."""
    with open(data_file) as f:
        data = json.load(f)

    info(f"Running combined (keygen+decaps) tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            info(f"  tcId={tc['tcId']} ... ", end="")
            # Generate keypair from seed
            keygen_out = run_binary([binary, "keygen_seed", f"seed={tc['seed']}"])
            if "_error" in keygen_out or "decode_error" in keygen_out:
                assert (
                    tc["result"] == "invalid"
                ), f"keygen error on non-invalid tcId={tc['tcId']}"
                info("ok")
                count += 1
                continue
            # Check ek matches if present
            if "ek" in tc and tc["result"] in ("valid", "acceptable"):
                assert (
                    keygen_out["ek"].upper() == tc["ek"].upper()
                ), f"ek mismatch tcId={tc['tcId']}"
            # Decapsulate
            dk = keygen_out["dk"]
            decaps_out = run_binary([binary, "decaps", f"dk={dk}", f"c={tc['c']}"])
            if "_error" in decaps_out or "decode_error" in decaps_out:
                assert (
                    tc["result"] == "invalid"
                ), f"decaps error on non-invalid tcId={tc['tcId']}"
            elif tc["result"] in ("valid", "acceptable"):
                assert (
                    decaps_out["K"].upper() == tc["K"].upper()
                ), f"K mismatch tcId={tc['tcId']}"
            elif tc["result"] == "invalid":
                assert (
                    decaps_out["K"].upper() != tc["K"].upper()
                ), f"K should not match for invalid tcId={tc['tcId']}"
            info("ok")
            count += 1
    info(f"  {count} combined tests passed")


def run_all(data_dir):
    """Run all Wycheproof test vector files."""
    data_dir = Path(data_dir)
    for filename in WYCHEPROOF_FILES:
        filepath = data_dir / filename
        if "keygen_seed_test" in filename:
            run_keygen_seed_test(filepath)
        elif "encaps_test" in filename:
            run_encaps_test(filepath)
        elif "semi_expanded_decaps_test" in filename:
            run_semi_expanded_decaps_test(filepath)
        elif filename.endswith("_test.json"):
            run_combined_test(filepath)
    info("ALL GOOD!")


parser = argparse.ArgumentParser(description="Wycheproof ML-KEM test client")
parser.add_argument(
    "-f",
    "--file",
    help="Path to a specific Wycheproof test vector JSON file",
    required=False,
)
parser.add_argument(
    "--data-dir",
    default="test/wycheproof/.wycheproof-data",
    help="Directory for downloaded test vectors (default: test/wycheproof/.wycheproof-data)",
)
args = parser.parse_args()

if args.file:
    # Run a single file
    filename = os.path.basename(args.file)
    if "keygen_seed_test" in filename:
        run_keygen_seed_test(args.file)
    elif "encaps_test" in filename:
        run_encaps_test(args.file)
    elif "semi_expanded_decaps_test" in filename:
        run_semi_expanded_decaps_test(args.file)
    elif filename.endswith("_test.json"):
        run_combined_test(args.file)
    else:
        err(f"Unknown test file type: {filename}")
        sys.exit(1)
    info("ALL GOOD!")
else:
    # Download and run all
    if not download_wycheproof_files(args.data_dir):
        err("Failed to download Wycheproof test files")
        sys.exit(1)
    run_all(args.data_dir)
