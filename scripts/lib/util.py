# Copyright (c) 2024 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

import os
import sys
import logging
from enum import Enum
from functools import reduce


class SCHEME(Enum):
    MLKEM512 = 1
    MLKEM768 = 2
    MLKEM1024 = 3

    def __str__(self):
        if self == SCHEME.MLKEM512:
            return "ML-KEM-512"
        if self == SCHEME.MLKEM768:
            return "ML-KEM-768"
        if self == SCHEME.MLKEM1024:
            return "ML-KEM-1024"

    def suffix(self):
        if self == SCHEME.MLKEM512:
            return "512"
        if self == SCHEME.MLKEM768:
            return "768"
        if self == SCHEME.MLKEM1024:
            return "1024"


class TEST_TYPES(Enum):
    FUNC = 1
    BENCH = 2
    NISTKAT = 3
    KAT = 4
    BENCH_COMPONENTS = 5
    ACVP = 6
    BRING_YOUR_OWN_FIPS202 = 7
    CUSTOM_BACKEND = 8
    MLKEM_NATIVE_AS_CODE_PACKAGE = 9
    MONOLITHIC_BUILD = 10

    def is_benchmark(self):
        return self in [TEST_TYPES.BENCH, TEST_TYPES.BENCH_COMPONENTS]

    def is_example(self):
        return self in TEST_TYPES.examples()

    @staticmethod
    def examples():
        return [
            TEST_TYPES.BRING_YOUR_OWN_FIPS202,
            TEST_TYPES.CUSTOM_BACKEND,
            TEST_TYPES.MLKEM_NATIVE_AS_CODE_PACKAGE,
            TEST_TYPES.MONOLITHIC_BUILD,
        ]

    @staticmethod
    def from_string(s):
        for e in TEST_TYPES.examples():
            if str.lower(e.name) == str.lower(s):
                return e
        raise Exception(
            f"Could not find example {s}. Examples: {list(map(lambda e: str.lower(e.name), TEST_TYPES.examples()))}"
        )

    def desc(self):
        if self == TEST_TYPES.FUNC:
            return "Functional Test"
        if self == TEST_TYPES.BENCH:
            return "Benchmark"
        if self == TEST_TYPES.BENCH_COMPONENTS:
            return "Benchmark Components"
        if self == TEST_TYPES.NISTKAT:
            return "Nistkat Test"
        if self == TEST_TYPES.KAT:
            return "Kat Test"
        if self == TEST_TYPES.ACVP:
            return "ACVP Test"
        if self == TEST_TYPES.BRING_YOUR_OWN_FIPS202:
            return "Example (Bring-Your-Own-FIPS202)"
        if self == TEST_TYPES.CUSTOM_BACKEND:
            return "Example (Custom Backend)"
        if self == TEST_TYPES.MLKEM_NATIVE_AS_CODE_PACKAGE:
            return "Example (mlkem-native as code package)"
        if self == TEST_TYPES.MONOLITHIC_BUILD:
            return "Example (monolithic build)"

    def make_dir(self):
        if self == TEST_TYPES.BRING_YOUR_OWN_FIPS202:
            return "examples/bring_your_own_fips202"
        if self == TEST_TYPES.CUSTOM_BACKEND:
            return "examples/custom_backend"
        if self == TEST_TYPES.MLKEM_NATIVE_AS_CODE_PACKAGE:
            return "examples/mlkem_native_as_code_package"
        if self == TEST_TYPES.MONOLITHIC_BUILD:
            return "examples/monolithic_build"
        return ""

    def make_target(self):
        if self == TEST_TYPES.FUNC:
            return "func"
        if self == TEST_TYPES.BENCH:
            return "bench"
        if self == TEST_TYPES.BENCH_COMPONENTS:
            return "bench_components"
        if self == TEST_TYPES.NISTKAT:
            return "nistkat"
        if self == TEST_TYPES.KAT:
            return "kat"
        if self == TEST_TYPES.ACVP:
            return "acvp"
        if self == TEST_TYPES.BRING_YOUR_OWN_FIPS202:
            return ""
        if self == TEST_TYPES.CUSTOM_BACKEND:
            return ""
        if self == TEST_TYPES.MLKEM_NATIVE_AS_CODE_PACKAGE:
            return ""
        if self == TEST_TYPES.MONOLITHIC_BUILD:
            return ""

    def make_run_target(self, scheme):
        t = self.make_target()
        if t == "":
            run_t = "run"
        else:
            run_t = f"run_{t}"
        if scheme is not None:
            return f"{run_t}_{scheme.suffix()}"
        else:
            return run_t


def dict2str(dict):
    s = ""
    for k, v in dict.items():
        s += f"{k}={v} "
    return s


def github_log(msg):
    if os.environ.get("GITHUB_ENV") is None:
        return
    print(msg)


def github_summary(title, test_label, results):
    """Generate summary for GitHub CI"""
    summary_file = os.environ.get("GITHUB_STEP_SUMMARY")

    res = list(results.values())

    if isinstance(results[SCHEME.MLKEM512], str):
        summaries = list(
            map(
                lambda s: f" {s} |",
                reduce(
                    lambda acc, s: [
                        line1 + " | " + line2 for line1, line2 in zip(acc, s)
                    ],
                    [s.splitlines() for s in res],
                ),
            )
        )
        summaries = [f"| {test_label} |" + summaries[0]] + [
            "| |" + x for x in summaries[1:]
        ]
    else:
        summaries = [
            reduce(
                lambda acc, b: f"{acc} " + (":x: |" if b else ":white_check_mark: |"),
                res,
                f"| {test_label} |",
            )
        ]

    def find_last_consecutive_match(l, s):
        for i, v in enumerate(l[s + 1 :]):
            if not v.startswith("|") or not v.endswith("|"):
                return i + 1
        return len(l)

    def add_summaries(fn, title, summaries):
        summary_title = "| Tests |"
        summary_table_format = "| ----- |"
        for s in SCHEME:
            summary_title += f" {s} |"
            summary_table_format += " ----- |"

        with open(fn, "r") as f:
            pre_summaries = [x for x in f.read().splitlines() if x]
            if title in pre_summaries:
                if summary_title not in pre_summaries:
                    summaries = [summary_title, summary_table_format] + summaries
                    pre_summaries = (
                        pre_summaries[: pre_summaries.index(title) + 1]
                        + summaries
                        + pre_summaries[pre_summaries.index(title) + 1 :]
                    )
                else:
                    i = find_last_consecutive_match(
                        pre_summaries, pre_summaries.index(title)
                    )
                    pre_summaries = pre_summaries[:i] + summaries + pre_summaries[i:]
                return ("w", pre_summaries)
            else:
                pre_summaries = [
                    title,
                    summary_title,
                    summary_table_format,
                ] + summaries
                return ("a", pre_summaries)

    if summary_file is not None:
        (access_mode, summaries) = add_summaries(summary_file, title, summaries)
        with open(summary_file, access_mode) as f:
            print("\n".join(summaries), file=f)


logging.basicConfig(
    stream=sys.stdout, format="%(levelname)-5s > %(name)-40s %(message)s"
)


def config_logger(verbose):
    logger = logging.getLogger()

    if verbose:
        logger.setLevel(logging.DEBUG)
    else:
        logger.setLevel(logging.INFO)


def logger(test_type, scheme, cross_prefix, opt):
    """Emit line indicating the processing of the given test"""
    compile_mode = "cross" if cross_prefix else "native"
    if opt is None:
        opt_label = ""
    elif opt is True:
        opt_label = " opt"
    else:
        opt_label = " no_opt"

    if test_type.is_example():
        sz = 40
    else:
        sz = 18

    return logging.getLogger(
        "{0:<{1}} {2:<11} {3:<17}".format(
            (test_type.desc()),
            sz,
            str(scheme),
            "({}{}):".format(compile_mode, opt_label),
        )
    )
