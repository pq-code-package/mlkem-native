# Copyright (c) 2024-2025 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

# ACVP client for ML-KEM
#
# Processes 'internalProjection.json' files from
# https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files
#
# Invokes `acvp_mlkem{lvl}` under the hood.

import os
import json
import sys
import subprocess

# Check if we need to use a wrapper for execution (e.g. QEMU)
exec_prefix = os.environ.get("EXEC_WRAPPER", "")
exec_prefix = [exec_prefix] if exec_prefix != "" else []

acvp_dir = "test/acvp_data"
acvp_keygen_jsons = [
    f"{acvp_dir}/acvp_v1.1.0.36_keygen_internalProjection.json",
    f"{acvp_dir}/acvp_v1.1.0.38_keygen_internalProjection.json",
]
acvp_encapDecap_jsons = [
    f"{acvp_dir}/acvp_v1.1.0.36_encapDecap_internalProjection.json",
    f"{acvp_dir}/acvp_v1.1.0.38_encapDecap_internalProjection.json",
]

acvp_keygen_data = []
for acvp_keygen_json in acvp_keygen_jsons:
    with open(acvp_keygen_json, "r") as f:
        acvp_keygen_data.append(json.load(f))


acvp_encapDecap_data = []
for acvp_encapDecap_json in acvp_encapDecap_jsons:
    with open(acvp_encapDecap_json, "r") as f:
        acvp_encapDecap_data.append(json.load(f))


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    print(msg, **kwargs)


def get_acvp_binary(tg):
    """Convert JSON dict for ACVP test group to suitable ACVP binary."""
    parameterSetToLevel = {
        "ML-KEM-512": 512,
        "ML-KEM-768": 768,
        "ML-KEM-1024": 1024,
    }
    level = parameterSetToLevel[tg["parameterSet"]]
    basedir = f"./test/build/mlkem{level}/bin"
    acvp_bin = f"acvp_mlkem{level}"
    return f"{basedir}/{acvp_bin}"


def run_encapDecap_test(tg, tc):
    info(f"Running encapDecap test case {tc['tcId']} ({tg['function']}) ... ", end="")
    if tg["function"] == "encapsulation":
        acvp_bin = get_acvp_binary(tg)
        acvp_call = exec_prefix + [
            acvp_bin,
            "encapDecap",
            "AFT",
            "encapsulation",
            f"ek={tc['ek']}",
            f"m={tc['m']}",
        ]
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            err("FAIL!")
            err(f"{acvp_call} failed with error code {result.returncode}")
            err(result.stderr)
            exit(1)
        # Extract results and compare to expected data
        for l in result.stdout.splitlines():
            (k, v) = l.split("=")
            if v != tc[k]:
                err("FAIL!")
                err(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
                exit(1)
        info("OK")
    elif tg["function"] == "decapsulation":
        acvp_bin = get_acvp_binary(tg)
        acvp_call = exec_prefix + [
            acvp_bin,
            "encapDecap",
            "VAL",
            "decapsulation",
            f"dk={tg['dk']}",
            f"c={tc['c']}",
        ]
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            err("FAIL!")
            err(f"{acvp_call} failed with error code {result.returncode}")
            err(result.stderr)
            exit(1)
        # Extract results and compare to expected data
        for l in result.stdout.splitlines():
            (k, v) = l.split("=")
            if v != tc[k]:
                err("FAIL!")
                err(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
                exit(1)
        info("OK")


def run_keyGen_test(tg, tc):
    info(f"Running keyGen test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)
    acvp_call = exec_prefix + [
        acvp_bin,
        "keyGen",
        "AFT",
        f"z={tc['z']}",
        f"d={tc['d']}",
    ]
    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
    if result.returncode != 0:
        err("FAIL!")
        err(f"{acvp_call} failed with error code {result.returncode}")
        err(result.stderr)
        exit(1)
    # Extract results and compare to expected data
    for l in result.stdout.splitlines():
        (k, v) = l.split("=")
        if v != tc[k]:
            err("FAIL!")
            err(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
            exit(1)
    info("OK")


for acvp_encapDecap, json_name in zip(acvp_encapDecap_data, acvp_encapDecap_jsons):
    info(f"Running ACVP tests for {json_name}")
    for tg in acvp_encapDecap["testGroups"]:
        for tc in tg["tests"]:
            run_encapDecap_test(tg, tc)

for acvp_keygen, json_name in zip(acvp_keygen_data, acvp_keygen_jsons):
    info(f"Running ACVP tests for {json_name}")
    for tg in acvp_keygen["testGroups"]:
        for tc in tg["tests"]:
            run_keyGen_test(tg, tc)
