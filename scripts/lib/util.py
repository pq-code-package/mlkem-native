# SPDX-License-Identifier: Apache-2.0

import os
import sys
import hashlib
import logging
from enum import IntEnum
from typing import TypedDict
from functools import reduce
import yaml


def sha256sum(result: bytes) -> str:
    m = hashlib.sha256()
    m.update(result)
    return m.hexdigest()


class SCHEME(IntEnum):
    MLKEM512 = 1
    MLKEM768 = 2
    MLKEM1024 = 3

    def __str__(self):
        match self:
            case SCHEME.MLKEM512:
                return "ML-KEM-512"
            case SCHEME.MLKEM768:
                return "ML-KEM-768"
            case SCHEME.MLKEM1024:
                return "ML-KEM-1024"

    def __iter__(self):
        return self

    def __next__(self):
        return self + 1

    def suffix(self):
        return self.name.removeprefix("MLKEM")


class TEST_TYPES(IntEnum):
    MLKEM = 1
    BENCH = 2
    NISTKAT = 3
    KAT = 4
    BENCH_COMPONENTS = 5

    def __str__(self):
        return self.name.lower()

    def desc(self):
        match self:
            case TEST_TYPES.MLKEM:
                return "Functional Test"
            case TEST_TYPES.BENCH:
                return "Benchmark"
            case TEST_TYPES.BENCH_COMPONENTS:
                return "Benchmark Components"
            case TEST_TYPES.NISTKAT:
                return "Nistkat Test"
            case TEST_TYPES.KAT:
                return "Kat Test"

    def bin(self):
        match self:
            case TEST_TYPES.MLKEM:
                return "test_mlkem"
            case TEST_TYPES.BENCH:
                return "bench_mlkem"
            case TEST_TYPES.BENCH_COMPONENTS:
                return "bench_components_mlkem"
            case TEST_TYPES.NISTKAT:
                return "gen_NISTKAT"
            case TEST_TYPES.KAT:
                return "gen_KAT"

    def bin_path(self, scheme: SCHEME):
        return f"test/build/{scheme.name.lower()}/bin/{self.bin()}{scheme.suffix()}"


def parse_meta(scheme: SCHEME, field: str) -> str:
    with open("META.yml", "r") as f:
        meta = yaml.safe_load(f)
    return meta["implementations"][int(scheme) - 1][field]


def github_summary(title: str, test: TEST_TYPES, results: TypedDict):
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
        summaries = [f"| {test.desc()} |" + summaries[0]] + [
            "| |" + x for x in summaries[1:]
        ]
    else:
        summaries = [
            reduce(
                lambda acc, b: f"{acc} " + (":x: |" if b else ":white_check_mark: |"),
                res,
                f"| {test.desc()} |",
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


def config_logger(verbose):
    logging.basicConfig(format="%(levelname)-5s > %(name)-40s %(message)s")

    logger = logging.getLogger()

    if verbose:
        logger.setLevel(logging.DEBUG)
    else:
        logger.setLevel(logging.INFO)


def logger(test_type: TEST_TYPES, scheme: SCHEME, cross_prefix: str, opt: bool):
    compile_mode = "cross" if cross_prefix else "native"
    implementation = "opt" if opt else "no_opt"

    return logging.getLogger(
        f"{test_type.desc():<15} {str(scheme):<11} ({compile_mode:<6}, {implementation:>6})"
    )
