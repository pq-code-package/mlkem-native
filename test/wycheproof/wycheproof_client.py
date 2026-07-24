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

# Pinned to a specific commit (2026-07-07).
WYCHEPROOF_COMMIT = "fc24cd5b787d8e496bff31b0468af693a652b0f2"
WYCHEPROOF_BASE_URL = (
    "https://raw.githubusercontent.com/C2SP/wycheproof"
    f"/{WYCHEPROOF_COMMIT}/testvectors_v1"
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

# Fields each test-case handler knows how to interpret. If Wycheproof adds a
# new field to a schema, an unrecognized key here means it may carry
# information we are silently failing to check; fail loudly instead.
KNOWN_FIELDS = {
    "keygen_seed": {"tcId", "comment", "result", "seed", "ek", "dk"},
    "encaps": {"tcId", "comment", "flags", "result", "ek", "m", "c", "K"},
    "semi_expanded_decaps": {
        "tcId",
        "comment",
        "flags",
        "result",
        "dk",
        "c",
        "ek",
        "K",
    },
    "combined": {"tcId", "comment", "flags", "result", "seed", "ek", "c", "K"},
}


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    print(msg, **kwargs)


def get_wycheproof_data_dir(data_dir):
    return Path(data_dir) / WYCHEPROOF_COMMIT


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
                with open(local_file, "r", encoding="utf-8") as f:
                    json.load(f)
            except (json.JSONDecodeError, Exception) as e:
                print(f"Error downloading {filename}: {e}", file=sys.stderr)
                local_file.unlink(missing_ok=True)
                return False
    return True


def check_known_fields(kind, tc):
    unknown = set(tc.keys()) - KNOWN_FIELDS[kind]
    assert not unknown, (
        f"Unrecognized field(s) {sorted(unknown)} in {kind} tcId={tc['tcId']}; "
        "Wycheproof schema may have grown a new field this client doesn't check"
    )


def get_binary(level):
    basedir = f"./test/build/mlkem{level}/bin"
    return f"{basedir}/wycheproof_mlkem{level}"


def detect_supported_modes():
    """Run wycheproof_mlkem512 --info to detect which modes are supported."""
    wycheproof_bin = "./test/build/mlkem512/bin/wycheproof_mlkem512"
    wycheproof_call = exec_prefix + [wycheproof_bin, "--info"]
    try:
        result = subprocess.run(wycheproof_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            err(
                f"Warning: {wycheproof_call} failed (rc={result.returncode}), assuming all modes supported"
            )
            return {"keygen_seed", "encaps", "decaps"}
        modes = set()
        for line in result.stdout.splitlines():
            line = line.strip()
            if line in ("keygen_seed", "encaps", "decaps"):
                modes.add(line)
        return modes
    except FileNotFoundError:
        err(f"Warning: {wycheproof_bin} not found, assuming all modes supported")
        return {"keygen_seed", "encaps", "decaps"}


# File-type → set of modes the binary must support to run those tests.
FILE_REQUIRED_MODES = {
    "keygen_seed_test": {"keygen_seed"},
    "encaps_test": {"encaps"},
    "semi_expanded_decaps_test": {"decaps"},
    # Combined test drives keygen (to derive dk from seed) then decaps.
    "_test": {"keygen_seed", "decaps"},
}


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
    with open(data_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    info(f"Running keygen_seed tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            check_known_fields("keygen_seed", tc)
            info(f"  tcId={tc['tcId']} ... ", end="")
            out = run_binary([binary, "keygen_seed", f"seed={tc['seed']}"])
            if tc["result"] == "valid":
                assert out["ek"].upper() == tc["ek"].upper(), (
                    f"ek mismatch tcId={tc['tcId']}"
                )
                assert out["dk"].upper() == tc["dk"].upper(), (
                    f"dk mismatch tcId={tc['tcId']}"
                )
            else:
                assert False, (
                    f"Unexpected result '{tc['result']}' for tcId={tc['tcId']}"
                )
            info("ok")
            count += 1
    info(f"  {count} keygen_seed tests passed")


def run_encaps_test(data_file):
    """Run mlkem_*_encaps_test.json tests."""
    with open(data_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    info(f"Running encaps tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            check_known_fields("encaps", tc)
            info(f"  tcId={tc['tcId']} ... ", end="")
            out = run_binary([binary, "encaps", f"ek={tc['ek']}", f"m={tc['m']}"])
            if tc["result"] == "invalid":
                # _error: non-zero exit code; decode_error: explicit validation failure
                assert "_error" in out or "decode_error" in out, (
                    f"binary success on invalid tcId={tc['tcId']}"
                )
            elif tc["result"] == "valid":
                assert out["c"].upper() == tc["c"].upper(), (
                    f"c mismatch tcId={tc['tcId']}"
                )
                assert out["K"].upper() == tc["K"].upper(), (
                    f"K mismatch tcId={tc['tcId']}"
                )
            else:
                assert False, (
                    f"Unsupported test result '{tc['result']}' for tcId={tc['tcId']}"
                )
            info("ok")
            count += 1
    info(f"  {count} encaps tests passed")


def run_semi_expanded_decaps_test(data_file):
    """Run mlkem_*_semi_expanded_decaps_test.json tests."""
    with open(data_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    info(f"Running semi_expanded_decaps tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            check_known_fields("semi_expanded_decaps", tc)
            info(f"  tcId={tc['tcId']} ... ", end="")
            out = run_binary([binary, "decaps", f"dk={tc['dk']}", f"c={tc['c']}"])
            if tc["result"] == "invalid":
                # _error: non-zero exit code; decode_error: explicit validation failure
                assert "_error" in out or "decode_error" in out, (
                    f"binary success on invalid tcId={tc['tcId']}"
                )
            elif tc["result"] == "valid":
                assert "K" in tc, f"missing K in test vector tcId={tc['tcId']}"
                assert out["K"].upper() == tc["K"].upper(), (
                    f"K mismatch tcId={tc['tcId']}"
                )
            else:
                assert False, (
                    f"Unsupported test result '{tc['result']}' for tcId={tc['tcId']}"
                )
            info("ok")
            count += 1
    info(f"  {count} semi_expanded_decaps tests passed")


def run_combined_test(data_file):
    """Run mlkem_*_test.json tests (keygen + decaps)."""
    with open(data_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    info(f"Running combined (keygen+decaps) tests from {data_file}")
    count = 0
    for tg in data["testGroups"]:
        level = PARAMETER_SET_TO_LEVEL[tg["parameterSet"]]
        binary = get_binary(level)
        for tc in tg["tests"]:
            check_known_fields("combined", tc)
            info(f"  tcId={tc['tcId']} ... ", end="")
            # Generate keypair from seed
            keygen_out = run_binary([binary, "keygen_seed", f"seed={tc['seed']}"])
            if "decode_error" in keygen_out:
                assert tc["result"] == "invalid", (
                    f"keygen decode error on valid tcId={tc['tcId']}"
                )
                info("ok")
                count += 1
                continue
            # Keygen succeeded — check ek
            assert "ek" in tc, f"missing ek in test vector tcId={tc['tcId']}"
            assert keygen_out["ek"].upper() == tc["ek"].upper(), (
                f"ek mismatch tcId={tc['tcId']}"
            )
            # Decapsulate
            dk = keygen_out["dk"]
            decaps_out = run_binary([binary, "decaps", f"dk={dk}", f"c={tc['c']}"])
            if tc["result"] == "invalid":
                # _error: non-zero exit code; decode_error: explicit validation failure
                assert "_error" in decaps_out or "decode_error" in decaps_out, (
                    f"binary success on invalid tcId={tc['tcId']}"
                )
            elif tc["result"] == "valid":
                assert decaps_out["K"].upper() == tc["K"].upper(), (
                    f"K mismatch tcId={tc['tcId']}"
                )
            else:
                assert False, (
                    f"Unsupported test result '{tc['result']}' for tcId={tc['tcId']}"
                )
            info("ok")
            count += 1
    info(f"  {count} combined tests passed")


def file_required_modes(filename):
    """Which API modes must be available to run tests from this file."""
    if "keygen_seed_test" in filename:
        return FILE_REQUIRED_MODES["keygen_seed_test"]
    if "encaps_test" in filename:
        return FILE_REQUIRED_MODES["encaps_test"]
    if "semi_expanded_decaps_test" in filename:
        return FILE_REQUIRED_MODES["semi_expanded_decaps_test"]
    if filename.endswith("_test.json"):
        return FILE_REQUIRED_MODES["_test"]
    return set()


def run_all(data_dir, supported_modes):
    """Run all Wycheproof test vector files."""
    data_dir = Path(data_dir)
    for filename in WYCHEPROOF_FILES:
        filepath = data_dir / filename
        required = file_required_modes(filename)
        if not required.issubset(supported_modes):
            info(f"Skipping {filename} (modes not supported in this build)")
            continue
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

supported_modes = detect_supported_modes()
info(f"Auto-detected supported modes: {sorted(supported_modes)}")

if args.file:
    # Run a single file
    filename = os.path.basename(args.file)
    required = file_required_modes(filename)
    if not required.issubset(supported_modes):
        info(f"Skipping {filename} (modes not supported in this build)")
        info("ALL GOOD!")
        sys.exit(0)
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
    data_dir = get_wycheproof_data_dir(args.data_dir)
    if not download_wycheproof_files(data_dir):
        err("Failed to download Wycheproof test files")
        sys.exit(1)
    run_all(data_dir, supported_modes)
