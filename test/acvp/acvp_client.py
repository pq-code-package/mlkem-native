#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# ACVP client for ML-KEM
# See https://pages.nist.gov/ACVP/draft-celi-acvp-ml-kem.html and
# https://github.com/usnistgov/ACVP-Server/tree/master/gen-val/json-files
# Invokes `acvp_mlkem{lvl}` under the hood.

import argparse
import os
import json
import sys
import subprocess
import urllib.request
from pathlib import Path

# Check if we need to use a wrapper for execution (e.g. QEMU)
exec_prefix = os.environ.get("EXEC_WRAPPER", "")
exec_prefix = exec_prefix.split(" ") if exec_prefix != "" else []


def download_acvp_files(version):
    """Download ACVP test files for the specified version if not present."""
    base_url = f"https://raw.githubusercontent.com/usnistgov/ACVP-Server/{version}/gen-val/json-files"

    # Files we need to download for ML-KEM
    files_to_download = [
        "ML-KEM-keyGen-FIPS203/prompt.json",
        "ML-KEM-keyGen-FIPS203/expectedResults.json",
        "ML-KEM-encapDecap-FIPS203/prompt.json",
        "ML-KEM-encapDecap-FIPS203/expectedResults.json",
    ]

    # Create directory structure
    data_dir = Path(f"test/acvp/.acvp-data/{version}/files")
    data_dir.mkdir(parents=True, exist_ok=True)

    for file_path in files_to_download:
        local_file = data_dir / file_path
        local_file.parent.mkdir(parents=True, exist_ok=True)

        if not local_file.exists():
            url = f"{base_url}/{file_path}"
            print(f"Downloading {file_path}...", file=sys.stderr)
            try:
                urllib.request.urlretrieve(url, local_file)
                # Verify the file is valid JSON
                with open(local_file, "r") as f:
                    json.load(f)
            except json.JSONDecodeError as e:
                print(
                    f"Error: Downloaded file {file_path} is not valid JSON: {e}",
                    file=sys.stderr,
                )
                local_file.unlink(missing_ok=True)
                return False
            except Exception as e:
                print(f"Error downloading {file_path}: {e}", file=sys.stderr)
                local_file.unlink(missing_ok=True)
                return False

    return True


def loadAcvpData(prompt, expectedResults):
    with open(prompt, "r") as f:
        promptData = json.load(f)
    expectedResultsData = None
    if expectedResults is not None:
        with open(expectedResults, "r") as f:
            expectedResultsData = json.load(f)

    return (prompt, promptData, expectedResults, expectedResultsData)


ALL_ACVP_FUNCTIONS = {
    "keyGen",
    "encapsulation",
    "encapsulationKeyCheck",
    "decapsulation",
    "decapsulationKeyCheck",
}


def detect_supported_functions():
    """Run acvp_mlkem512 --info to detect which ACVP functions are supported."""
    acvp_bin = "./test/build/mlkem512/bin/acvp_mlkem512"
    acvp_call = exec_prefix + [acvp_bin, "--info"]
    try:
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            err(
                f"Warning: {acvp_call} failed (rc={result.returncode}), assuming all functions supported"
            )
            return set(ALL_ACVP_FUNCTIONS)
        functions = set()
        for line in result.stdout.splitlines():
            line = line.strip()
            if line in ALL_ACVP_FUNCTIONS:
                functions.add(line)
        return functions
    except FileNotFoundError:
        err(f"Warning: {acvp_bin} not found, assuming all functions supported")
        return set(ALL_ACVP_FUNCTIONS)


ENCAP_DECAP_FUNCTIONS = {
    "encapsulation",
    "encapsulationKeyCheck",
    "decapsulation",
    "decapsulationKeyCheck",
}


def loadDefaultAcvpData(version, supported_functions=None):
    if supported_functions is None:
        supported_functions = set(ALL_ACVP_FUNCTIONS)

    # Load a prompt whenever any of its sub-functions is compiled in.
    # Unsupported sub-functions are filtered out per test case (see
    # filter_test_cases) so result comparison stays byte-identical.
    keyGen_any = "keyGen" in supported_functions
    encapDecap_any = bool(ENCAP_DECAP_FUNCTIONS & supported_functions)

    data_dir = f"test/acvp/.acvp-data/{version}/files"
    acvp_jsons_for_version = [
        (
            "keyGen",
            keyGen_any,
            f"{data_dir}/ML-KEM-keyGen-FIPS203/prompt.json",
            f"{data_dir}/ML-KEM-keyGen-FIPS203/expectedResults.json",
        ),
        (
            "encapDecap",
            encapDecap_any,
            f"{data_dir}/ML-KEM-encapDecap-FIPS203/prompt.json",
            f"{data_dir}/ML-KEM-encapDecap-FIPS203/expectedResults.json",
        ),
    ]
    acvp_data = []
    for mode, is_supported, prompt, expectedResults in acvp_jsons_for_version:
        if not is_supported:
            warn(
                f"WARNING: Skipped {mode} ACVP prompt "
                f"(no sub-function supported by this build)."
            )
            continue
        acvp_data.append(loadAcvpData(prompt, expectedResults))
    return acvp_data


def unwrap_acvts(data):
    # ACVTS files wrap the payload as [{"acvVersion": ...}, {...}].
    return data[1] if isinstance(data, list) else data


def filter_test_cases(acvp_data, should_drop):
    """Drop cases for which should_drop(tg, tc) returns a reason (None keeps).
    Reasons are computed from the prompt but applied consistently to both
    prompt and expected data, so downstream byte-identical result comparison
    still works. Returns the list of drop reasons for reporting."""
    reasons = []
    for _, promptData, _, expectedData in acvp_data:
        drop = {}
        for tg in unwrap_acvts(promptData).get("testGroups", []):
            for tc in tg["tests"]:
                reason = should_drop(tg, tc)
                if reason is not None:
                    drop[tg["tgId"], tc["tcId"]] = reason
        for data in (promptData, expectedData):
            if data is None:
                continue
            for tg in unwrap_acvts(data).get("testGroups", []):
                tg["tests"] = [
                    tc for tc in tg["tests"] if (tg["tgId"], tc["tcId"]) not in drop
                ]
        reasons += drop.values()
    return reasons


def unsupported_function(supported_functions):
    """Return a should_drop predicate that skips encapDecap test cases whose
    tg['function'] is not in supported_functions. keyGen prompts have no
    tg['function'] field, so they are never dropped by this predicate.
    The predicate returns the bare function name so the caller can format
    a compact 'Unsupported functions: A, B, C' summary."""

    def should_drop(tg, tc):
        fn = tg.get("function")
        if fn is None or fn in supported_functions:
            return None
        return fn

    return should_drop


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    print(msg, **kwargs)


# Warnings deferred to the end of the run so they stand out after all the
# per-test-case chatter. Collected by warn(), emitted once by flush_warnings().
_warnings = []


def warn(msg):
    _warnings.append(msg)


def flush_warnings():
    if not _warnings:
        return
    err("")
    for msg in _warnings:
        err(msg)


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
        for line in result.stdout.splitlines():
            (k, v) = line.split("=")
            results[k] = v
    elif tg["function"] == "decapsulation":
        acvp_bin = get_acvp_binary(tg)
        acvp_call = exec_prefix + [
            acvp_bin,
            "encapDecap",
            "VAL",
            "decapsulation",
            f"dk={tc['dk']}",
            f"c={tc['c']}",
        ]
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            err("FAIL!")
            err(f"{acvp_call} failed with error code {result.returncode}")
            err(result.stderr)
            exit(1)
        # Extract results
        for line in result.stdout.splitlines():
            (k, v) = line.split("=")
            results[k] = v
    elif tg["function"] == "encapsulationKeyCheck":
        acvp_bin = get_acvp_binary(tg)
        acvp_call = exec_prefix + [
            acvp_bin,
            "encapDecap",
            "VAL",
            "encapsulationKeyCheck",
            f"ek={tc['ek']}",
        ]
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            err("FAIL!")
            err(f"{acvp_call} failed with error code {result.returncode}")
            err(result.stderr)
            exit(1)
        # Extract results
        for line in result.stdout.splitlines():
            (k, v) = line.split("=")
            results[k] = v == "1"

    elif tg["function"] == "decapsulationKeyCheck":
        acvp_bin = get_acvp_binary(tg)
        acvp_call = exec_prefix + [
            acvp_bin,
            "encapDecap",
            "VAL",
            "decapsulationKeyCheck",
            f"dk={tc['dk']}",
        ]
        result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
        if result.returncode != 0:
            err("FAIL!")
            err(f"{acvp_call} failed with error code {result.returncode}")
            err(result.stderr)
            exit(1)
        # Extract results
        for line in result.stdout.splitlines():
            (k, v) = line.split("=")
            results[k] = v == "1"
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
    for line in result.stdout.splitlines():
        (k, v) = line.split("=")
        results[k] = v
    info("done")
    return results


def runTestSingle(promptName, prompt, expectedResultName, expectedResult, output):
    info(f"Running ACVP tests for {promptName}")

    assert expectedResult is not None or output is not None

    # The ACVTS data structure is very slightly different from the sample files
    # in the usnistgov/ACVP-Server Github repository:
    # The prompt consists of a 2-element list, where the first element is
    # solely consisting of {"acvVersion": "1.0"} and the second element is
    # the usual prompt containing the test values.
    # See https://pages.nist.gov/ACVP/draft-celi-acvp-ml-kem.txt for details.
    # We automatically detect that case here and extract the second element
    isAcvts = False
    if type(prompt) is list:
        isAcvts = True
        assert len(prompt) == 2
        acvVersion = prompt[0]
        assert len(acvVersion) == 1
        prompt = prompt[1]

    assert prompt["algorithm"] == "ML-KEM"
    assert prompt["mode"] == "encapDecap" or prompt["mode"] == "keyGen"

    # copy top level fields into the results
    results = prompt.copy()

    results["testGroups"] = []
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

    # In case the testvectors are from the ACVTS server, it is expected
    # that the acvVersion is included in the output results.
    # See note on ACVTS data structure above.
    if isAcvts is True:
        results = [acvVersion, results]

    # Compare to expected results
    if expectedResult is not None:
        info(f"Comparing results with {expectedResultName}")
        # json.dumps() is guaranteed to preserve insertion order (since Python 3.7)
        # Enforce strictly the same order as in the expected Result
        if json.dumps(results) != json.dumps(expectedResult):
            err("FAIL!")
            err(f"Mismatching result for {promptName}")
            exit(1)
        info("OK")
    else:
        info(
            "Results could not be validated as no expected resulted were provided to --expected"
        )

    # Write results to file
    if output is not None:
        info(f"Writing results to {output}")
        with open(output, "w") as f:
            json.dump(results, f)


def runTest(data, output):
    # if output is defined we expect only one input
    assert output is None or len(data) == 1

    for promptName, prompt, expectedResultName, expectedResult in data:
        runTestSingle(promptName, prompt, expectedResultName, expectedResult, output)
    info("ALL GOOD!")


def test(prompt, expected, output, version, supported_functions=None):
    assert prompt is not None or output is None, (
        "cannot produce output if there is no input"
    )

    assert prompt is None or (output is not None or expected is not None), (
        "if there is a prompt, either output or expectedResult required"
    )

    # if prompt is passed, use it
    if prompt is not None:
        data = [loadAcvpData(prompt, expected)]
    else:
        # load data from downloaded files
        data = loadDefaultAcvpData(version, supported_functions)

    if not data:
        warn("WARNING: No ACVP tests supported by this build; no cases were run.")
        info("ALL GOOD!")
        flush_warnings()
        return

    # Filter out test cases whose ACVP function isn't compiled in.
    if supported_functions is not None:
        reasons = filter_test_cases(data, unsupported_function(supported_functions))
        if reasons:
            fns = ", ".join(sorted(set(reasons)))
            warn(
                f"WARNING: Dropped {len(reasons)} ACVP test case(s). "
                f"Unsupported functions: {fns}."
            )

    runTest(data, output)
    flush_warnings()


parser = argparse.ArgumentParser()
parser.add_argument(
    "-p", "--prompt", help="Path to prompt file in json format", required=False
)
parser.add_argument(
    "-e",
    "--expected",
    help="Path to expectedResults file in json format",
    required=False,
)
parser.add_argument(
    "-o", "--output", help="Path to output file in json format", required=False
)
parser.add_argument(
    "--version",
    "-v",
    default="v1.1.0.41",
    help="ACVP test vector version (default: v1.1.0.41)",
)
args = parser.parse_args()

if args.prompt is None:
    print(f"Using ACVP test vectors version {args.version}", file=sys.stderr)

    # Download files if needed
    if not download_acvp_files(args.version):
        print("Failed to download ACVP test files", file=sys.stderr)
        sys.exit(1)

supported_functions = detect_supported_functions()
info(f"Auto-detected supported ACVP functions: {sorted(supported_functions)}")

test(args.prompt, args.expected, args.output, args.version, supported_functions)
