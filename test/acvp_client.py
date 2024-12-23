# Copyright (c) 2024 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

# ACVP client for ML-KEM
#
# Processes 'internalProjection.json' files from
# https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files
#
# Invokes `acvp_mlkem{lvl}` under the hood.

import json
import os
import subprocess

acvp_dir = "test/acvp_data"
acvp_keygen_json = f"{acvp_dir}/acvp_keygen_internalProjection.json"
acvp_encapDecap_json = f"{acvp_dir}/acvp_encapDecap_internalProjection.json"

if os.environ.get("EXEC_PREFIX", "").strip() != "":
    exec_wrapper = [os.environ["EXEC_PREFIX"].strip()]
else:
    exec_wrapper = []

with open(acvp_keygen_json, "r") as f:
    acvp_keygen_data = json.load(f)

with open(acvp_encapDecap_json, "r") as f:
    acvp_encapDecap_data = json.load(f)


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
    print(f"Running encapDecap test case {tc['tcId']} ({tg['function']}) ... ", end="")
    if tg["function"] == "encapsulation":
        acvp_bin = get_acvp_binary(tg)
        acvp_call = exec_wrapper + [
            acvp_bin,
            "encapDecap",
            "AFT",
            "encapsulation",
            f"ek={tc['ek']}",
            f"m={tc['m']}",
        ]
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            print("FAIL!")
            print(f"{acvp_call} failed with error code {result.returncode}")
            print(result.stderr)
            exit(1)
        # Extract results and compare to expected data
        for l in result.stdout.splitlines():
            (k, v) = l.split("=")
            if v != tc[k]:
                print("FAIL!")
                print(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
                exit(1)
        print("OK")
    elif tg["function"] == "decapsulation":
        acvp_bin = get_acvp_binary(tg)
        acvp_call = exec_wrapper + [
            acvp_bin,
            "encapDecap",
            "VAL",
            "decapsulation",
            f"dk={tg['dk']}",
            f"c={tc['c']}",
        ]
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            print("FAIL!")
            print(f"{acvp_call} failed with error code {result.returncode}")
            print(result.stderr)
            exit(1)
        # Extract results and compare to expected data
        for l in result.stdout.splitlines():
            (k, v) = l.split("=")
            if v != tc[k]:
                print("FAIL!")
                print(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
                exit(1)
        print("OK")


def run_keyGen_test(tg, tc):
    print(f"Running keyGen test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)
    acvp_call = exec_wrapper + [
        acvp_bin,
        "keyGen",
        "AFT",
        f"z={tc['z']}",
        f"d={tc['d']}",
    ]
    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
    if result.returncode != 0:
        print("FAIL!")
        print(f"{acvp_call} failed with error code {result.returncode}")
        print(result.stderr)
        exit(1)
    # Extract results and compare to expected data
    for l in result.stdout.splitlines():
        (k, v) = l.split("=")
        if v != tc[k]:
            print("FAIL!")
            print(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
            exit(1)
    print("OK")


for tg in acvp_encapDecap_data["testGroups"]:
    for tc in tg["tests"]:
        run_encapDecap_test(tg, tc)

for tg in acvp_keygen_data["testGroups"]:
    for tc in tg["tests"]:
        run_keyGen_test(tg, tc)
