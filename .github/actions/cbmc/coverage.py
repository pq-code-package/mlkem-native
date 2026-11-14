#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Join CBMC coverage by parameter set and report it on a pull request."""

import argparse
import json
import os
import pathlib
import subprocess
import sys
import tempfile


COMMENT_TAG = "<!-- cbmc-coverage-report -->"
HIT = "hit"
MISSED = "missed"
BOTH = "both"
COVERED = {HIT, BOTH}
VALID_STATUSES = {HIT, MISSED, BOTH}


def get_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reports-dir", required=True, type=pathlib.Path)
    parser.add_argument("--output-dir", required=True, type=pathlib.Path)
    parser.add_argument("--exceptions", required=True, type=pathlib.Path)
    parser.add_argument(
        "--parameter-set",
        action="append",
        required=True,
        metavar="VALUE=LABEL",
        help="Expected parameter set and its display label",
    )
    parser.add_argument(
        "--expected-variant",
        action="append",
        required=True,
        help="Variant expected for every parameter set",
    )
    return parser.parse_args()


def parse_parameter_sets(values):
    parameter_sets = {}
    for value in values:
        key, separator, label = value.partition("=")
        if not separator or not key or not label:
            raise ValueError(f"Invalid parameter set specification: {value}")
        if key in parameter_sets:
            raise ValueError(f"Duplicate parameter set specification: {key}")
        parameter_sets[key] = label
    return parameter_sets


def load_json(path):
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def find_reports(root):
    reports = {}
    for metadata_path in root.rglob("metadata.json"):
        metadata = load_json(metadata_path)
        if metadata.get("schema") != 1:
            raise ValueError(f"Unsupported metadata schema in {metadata_path}")
        key = metadata["parameter_set"], metadata["variant"]
        if key in reports:
            raise ValueError(f"Duplicate coverage report for {key[0]} ({key[1]})")
        coverage_path = metadata_path.parent / "json" / "viewer-coverage.json"
        if not coverage_path.is_file():
            raise FileNotFoundError(f"Missing coverage data: {coverage_path}")
        reports[key] = coverage_path
    return reports


def combine_status(left, right):
    if left not in VALID_STATUSES or right not in VALID_STATUSES:
        raise ValueError(f"Invalid coverage status: {left}, {right}")
    if left == right:
        return left
    return BOTH


def merge_coverage(paths):
    coverage = {}
    for path in paths:
        data = load_json(path)["viewer-coverage"]["coverage"]
        for filename, functions in data.items():
            merged_functions = coverage.setdefault(filename, {})
            for function, lines in functions.items():
                merged_lines = merged_functions.setdefault(function, {})
                for line, status in lines.items():
                    if line in merged_lines:
                        status = combine_status(merged_lines[line], status)
                    elif status not in VALID_STATUSES:
                        raise ValueError(f"Invalid coverage status: {status}")
                    merged_lines[line] = status
    return coverage


def summarize(statuses):
    statuses = list(statuses)
    total = len(statuses)
    hit = sum(status in COVERED for status in statuses)
    return {
        "hit": hit,
        "total": total,
        "percentage": hit / total if total else 1.0,
    }


def build_viewer_coverage(coverage):
    function_coverage = {}
    line_coverage = {}
    for filename, functions in coverage.items():
        function_coverage[filename] = {}
        line_coverage[filename] = {}
        for function, lines in functions.items():
            function_coverage[filename][function] = summarize(lines.values())
            for line, status in lines.items():
                current = line_coverage[filename].get(line)
                line_coverage[filename][line] = (
                    combine_status(current, status) if current else status
                )

    overall = summarize(
        status for lines in line_coverage.values() for status in lines.values()
    )
    return {
        "viewer-coverage": {
            "coverage": coverage,
            "function_coverage": function_coverage,
            "line_coverage": line_coverage,
            "overall_coverage": overall,
        }
    }


def load_exceptions(path):
    data = load_json(path)
    if data.get("schema") != 1:
        raise ValueError(f"Unsupported exception schema in {path}")
    exceptions = {}
    for exception in data.get("exceptions", []):
        key = exception["file"], str(exception["line"])
        if key in exceptions:
            raise ValueError(f"Duplicate coverage exception: {key[0]}:{key[1]}")
        exceptions[key] = exception["reason"]
    return exceptions


def missed_lines(viewer_coverage):
    lines = viewer_coverage["viewer-coverage"]["line_coverage"]
    return {
        (filename, line)
        for filename, statuses in lines.items()
        for line, status in statuses.items()
        if status == MISSED
    }


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2, sort_keys=True)
        handle.write("\n")


def get_pr_number():
    event_path = os.environ.get("GITHUB_EVENT_PATH")
    if not event_path or not os.path.exists(event_path):
        return None
    return load_json(pathlib.Path(event_path)).get("pull_request", {}).get("number")


def render_comment(results):
    lines = [
        COMMENT_TAG,
        "## CBMC proof coverage",
        "",
        "Coverage reports are joined within each parameter set. Reports from "
        "different parameter sets are not mixed.",
        "",
        "| Parameter set | Covered lines | Excluded | Result |",
        "|---------------|--------------:|---------:|:------:|",
    ]
    for result in results:
        status = "✅" if not result["missed"] else "❌"
        lines.append(
            f"| {result['label']} | {result['covered']}/{result['required']} | "
            f"{len(result['excluded'])} | {status} |"
        )

    excluded = [
        (result["label"], item) for result in results for item in result["excluded"]
    ]
    missed = [
        (result["label"], item) for result in results for item in result["missed"]
    ]
    if excluded:
        lines += ["", "<details>", "<summary>Excluded unreachable lines</summary>", ""]
        for label, item in excluded:
            lines.append(
                f"- {label}: `{item['file']}:{item['line']}` — {item['reason']}"
            )
        lines += ["", "</details>"]
    if missed:
        lines += ["", "### Uncovered lines", ""]
        for label, item in missed:
            lines.append(f"- {label}: `{item['file']}:{item['line']}`")
    return "\n".join(lines)


def post_or_update_comment(pr_number, body):
    repository = os.environ.get("GITHUB_REPOSITORY")
    if not repository:
        raise ValueError("GITHUB_REPOSITORY is not set")
    result = subprocess.run(
        [
            "gh",
            "api",
            f"repos/{repository}/issues/{pr_number}/comments",
            "--jq",
            f'.[] | select(.body | startswith("{COMMENT_TAG}")) | .id',
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    existing_id = result.stdout.strip().splitlines()

    with tempfile.NamedTemporaryFile(mode="w", suffix=".md", delete=False) as handle:
        handle.write(body)
        body_path = handle.name
    try:
        if existing_id:
            endpoint = f"repos/{repository}/issues/comments/{existing_id[0]}"
            method = "PATCH"
        else:
            endpoint = f"repos/{repository}/issues/{pr_number}/comments"
            method = "POST"
        subprocess.run(
            ["gh", "api", endpoint, "-X", method, "-F", f"body=@{body_path}"],
            check=True,
        )
    finally:
        os.unlink(body_path)


def main():
    args = get_args()
    parameter_sets = parse_parameter_sets(args.parameter_set)
    reports = find_reports(args.reports_dir)
    exceptions = load_exceptions(args.exceptions)
    expected_variants = set(args.expected_variant)
    results = []

    for parameter_set, label in parameter_sets.items():
        variants = {
            variant
            for report_parameter_set, variant in reports
            if report_parameter_set == parameter_set
        }
        if variants != expected_variants:
            raise ValueError(
                f"Coverage reports for {parameter_set}: expected variants "
                f"{sorted(expected_variants)}, found {sorted(variants)}"
            )
        paths = [reports[(parameter_set, variant)] for variant in sorted(variants)]
        viewer_coverage = build_viewer_coverage(merge_coverage(paths))
        write_json(
            args.output_dir / parameter_set / "viewer-coverage.json",
            viewer_coverage,
        )

        misses = missed_lines(viewer_coverage)
        excluded_keys = misses & exceptions.keys()
        unexpected = misses - exceptions.keys()
        overall = viewer_coverage["viewer-coverage"]["overall_coverage"]
        results.append(
            {
                "parameter_set": parameter_set,
                "label": label,
                "covered": overall["hit"],
                "required": overall["total"] - len(excluded_keys),
                "excluded": [
                    {
                        "file": filename,
                        "line": int(line),
                        "reason": exceptions[(filename, line)],
                    }
                    for filename, line in sorted(excluded_keys)
                ],
                "missed": [
                    {"file": filename, "line": int(line)}
                    for filename, line in sorted(unexpected)
                ],
            }
        )

    write_json(args.output_dir / "summary.json", {"schema": 1, "results": results})
    comment = render_comment(results)
    print(comment)
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        with open(summary_path, "a", encoding="utf-8") as handle:
            handle.write(comment)
            handle.write("\n")
    pr_number = get_pr_number()
    if pr_number:
        post_or_update_comment(pr_number, comment)

    if any(result["missed"] for result in results):
        sys.exit(1)


if __name__ == "__main__":
    try:
        main()
    except (
        json.JSONDecodeError,
        KeyError,
        OSError,
        subprocess.CalledProcessError,
        ValueError,
    ) as error:
        print(f"coverage-report: {error}", file=sys.stderr)
        sys.exit(1)
