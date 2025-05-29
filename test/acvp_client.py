#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# ACVP client for ML-KEM
#
# Processes json files from
# https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files
#
# Invokes `acvp_mlkem{lvl}` under the hood.

import os
import json
import sys
import subprocess

# Check if we need to use a wrapper for execution (e.g. QEMU)
exec_prefix = os.environ.get("EXEC_WRAPPER", "")
exec_prefix = exec_prefix.split(" ") if exec_prefix != "" else []

acvp_dir = "test/acvp_data"
acvp_jsons = [
    (
        f"{acvp_dir}/acvp_v1.1.0.36_keyGen_prompt.json",
        f"{acvp_dir}/acvp_v1.1.0.36_keyGen_expectedResults.json",
    ),
    (
        f"{acvp_dir}/acvp_v1.1.0.38_keyGen_prompt.json",
        f"{acvp_dir}/acvp_v1.1.0.38_keyGen_expectedResults.json",
    ),
    (
        f"{acvp_dir}/acvp_v1.1.0.39_keyGen_prompt.json",
        f"{acvp_dir}/acvp_v1.1.0.39_keyGen_expectedResults.json",
    ),
    (
        f"{acvp_dir}/acvp_v1.1.0.36_encapDecap_prompt.json",
        f"{acvp_dir}/acvp_v1.1.0.36_encapDecap_expectedResults.json",
    ),
    (
        f"{acvp_dir}/acvp_v1.1.0.38_encapDecap_prompt.json",
        f"{acvp_dir}/acvp_v1.1.0.38_encapDecap_expectedResults.json",
    ),
    (
        f"{acvp_dir}/acvp_v1.1.0.39_encapDecap_prompt.json",
        f"{acvp_dir}/acvp_v1.1.0.39_encapDecap_expectedResults.json",
    ),
]

acvp_data = []
for prompt, expectedResults in acvp_jsons:
    with open(prompt, "r") as f:
        promptData = json.load(f)
    with open(expectedResults, "r") as f:
        expectedResultsData = json.load(f)

    acvp_data.append((promptData, expectedResultsData))


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

    results = {"tcId": tc["tcId"]}
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
        # Extract results
        for l in result.stdout.splitlines():
            (k, v) = l.split("=")
            results[k] = v
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
        # Extract results
        for l in result.stdout.splitlines():
            (k, v) = l.split("=")
            results[k] = v
    info("done")
    return results


def run_keyGen_test(tg, tc):
    info(f"Running keyGen test case {tc['tcId']} ... ", end="")
    results = {"tcId": tc["tcId"]}

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
    # Extract results
    for l in result.stdout.splitlines():
        (k, v) = l.split("=")
        results[k] = v
    info("done")
    return results


for acvp, json_name in zip(acvp_data, acvp_jsons):
    info(f"Running ACVP tests for {json_name[0]}")

    prompt, expectedResults = acvp

    assert prompt["algorithm"] == "ML-KEM"
    assert prompt["mode"] == "encapDecap" or prompt["mode"] == "keyGen"

    results = {
        "vsId": prompt["vsId"],
        "algorithm": "ML-KEM",
        "mode": prompt["mode"],
        "revision": prompt["revision"],
        "isSample": prompt["isSample"],
        "testGroups": [],
    }
    for tg in prompt["testGroups"]:
        tgResult = {
            "tgId": tg["tgId"],
            "tests": [],
        }
        results["testGroups"].append(tgResult)
        for tc in tg["tests"]:
            if prompt["mode"] == "encapDecap":
                result = run_encapDecap_test(tg, tc)
            elif prompt["mode"] == "keyGen":
                result = run_keyGen_test(tg, tc)
            tgResult["tests"].append(result)

    # Compare to expected results
    if json.dumps(results, sort_keys=True) != json.dumps(
        expectedResults, sort_keys=True
    ):
        err("FAIL!")
        err(f"Mismatching result for {json_name[0]}")
        exit(1)
    info("OK")
info("ALL GOOD!")
