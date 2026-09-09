#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""CBMC proof results reporter for GitHub Actions."""

import argparse
import base64
import json
import os
import subprocess
import tempfile
from collections import namedtuple

# GitHub context
GITHUB_REPOSITORY = os.environ.get("GITHUB_REPOSITORY", "")
GITHUB_REF = os.environ.get("GITHUB_REF", "")
GITHUB_SHA = os.environ.get("GITHUB_SHA", "")[:7]

COMMENT_TAG = "cbmc-report"

# Status symbols
OK = "✅"
WARN = "⚠️"
FAIL = "❌"

ProofResult = namedtuple(
    "ProofResult", ["name", "dm", "solver", "status", "current", "previous", "change"]
)


def get_args():
    parser = argparse.ArgumentParser(description="CBMC proof results reporter")
    parser.add_argument("--results-json", required=True)
    parser.add_argument("--mlkem-k", required=True, choices=["2", "3", "4"])
    parser.add_argument("--min-runtime", type=int, default=20)
    parser.add_argument("--regression-threshold", type=float, default=1.5)
    parser.add_argument("--gh-pages-branch", default="gh-pages")
    parser.add_argument("--data-dir", default="dev/cbmc")
    return parser.parse_args()


def get_pr_number():
    """Get PR number from GitHub event."""
    event_path = os.environ.get("GITHUB_EVENT_PATH")
    if not event_path or not os.path.exists(event_path):
        return None
    with open(event_path) as f:
        event = json.load(f)
    return event.get("pull_request", {}).get("number")


def fetch_baseline(cfg):
    """Fetch baseline data from gh-pages branch."""
    baseline_file = f"{cfg.data_dir}/mlkem-{cfg.param_set}.json"
    subprocess.run(
        ["git", "fetch", "origin", cfg.gh_pages_branch, "--depth=1"],
        capture_output=True,
    )
    result = subprocess.run(
        ["git", "show", f"origin/{cfg.gh_pages_branch}:{baseline_file}"],
        capture_output=True,
        text=True,
    )
    if result.returncode == 0 and result.stdout.strip():
        return json.loads(result.stdout)
    return None


def render_table(rows):
    """Render a markdown table from ProofResult rows."""
    lines = [
        "| Proof | DM | Solver | Status | Current | Previous | Change |",
        "|-------|----|--------|--------|---------|----------|--------|",
    ]
    previous_name = None
    for row in rows:
        name = f"`{row.name}`" if row.name != previous_name else ""
        previous_name = row.name
        lines.append(
            f"| {name} | {row.dm} | {row.solver} | {row.status} | "
            f"{row.current} | {row.previous} | {row.change} |"
        )
    return lines


def config_key(r):
    """Return the proof configuration identity used for baseline matching."""
    return r["name"], r["dm"], r["solver"]


def index_baseline(baseline):
    """Index configured baselines exactly and old baselines by proof name."""
    by_config = {}
    by_name = {}
    for result in (baseline or {}).get("runtimes", []):
        has_dm = "dm" in result
        has_solver = "solver" in result
        if has_dm != has_solver:
            raise ValueError(f"Incomplete baseline configuration for {result['name']}")
        if has_dm:
            by_config[config_key(result)] = result
            continue
        if result["name"] in by_name:
            raise ValueError(
                f"Multiple baselines without configurations for {result['name']}"
            )
        by_name[result["name"]] = result
    return by_config, by_name


def classify_proof(r, baseline_by_config, baseline_by_name, cfg):
    """Classify a single proof result, returning (ProofResult, is_alert)."""
    name, dm, solver = config_key(r)
    base = baseline_by_config.get((name, dm, solver), baseline_by_name.get(name, {}))
    base_val, base_failed = base.get("value"), base.get("status") == "failed"
    base_omitted = base.get("status") == "omitted"
    base_inconclusive = base.get("status") == "inconclusive"
    solver_display = solver
    if r.get("default", False):
        solver_display += "*"
    if r.get("exploratory", False):
        solver_display += " (explore)"

    # The solver did not refute a property, but it also did not prove it.
    if r.get("status") == "inconclusive":
        prev = (
            f"{base_val}s"
            if base_val
            else "failed"
            if base_failed
            else "inconclusive"
            if base_inconclusive
            else "omitted"
            if base_omitted
            else "-"
        )
        return (
            ProofResult(name, dm, solver_display, WARN, "?", prev, "inconclusive"),
            True,
        )

    if r.get("status") == "failed":
        prev = "failed" if base_failed else (f"{base_val}s" if base_val else "-")
        if base_omitted:
            prev = "omitted"
        return ProofResult(name, dm, solver_display, FAIL, "-", prev, "-"), True

    cur_val = r["value"]
    if base_failed:
        return (
            ProofResult(name, dm, solver_display, OK, f"{cur_val}s", "failed", "fixed"),
            False,
        )
    if base_omitted:
        return (
            ProofResult(name, dm, solver_display, OK, f"{cur_val}s", "omitted", "new"),
            False,
        )
    if base_val is None:
        return (
            ProofResult(name, dm, solver_display, OK, f"{cur_val}s", "-", "new"),
            False,
        )

    ratio = cur_val / base_val if base_val > 0 else 1
    change = f"{(ratio - 1) * 100:+.0f}%" if base_val > 0 else "-"
    is_regression = cur_val >= cfg.min_runtime and ratio >= cfg.regression_threshold
    status = WARN if is_regression else OK
    return (
        ProofResult(
            name,
            dm,
            solver_display,
            status,
            f"{cur_val}s",
            f"{base_val}s",
            change,
        ),
        is_regression,
    )


def is_default_result(result):
    """Recognize explicit defaults and unique legacy results."""
    if "default" in result:
        return result["default"]
    return "dm" not in result and "solver" not in result


def compute_total_runtime(data):
    """Compute total runtime from successful default configurations."""
    if not data:
        return None
    return sum(
        r["value"]
        for r in data.get("runtimes", [])
        if r.get("status") not in ("failed", "omitted", "inconclusive")
        and "value" in r
        and is_default_result(r)
    )


def build_comment(current, baseline, cfg):
    """Build the PR comment markdown."""
    baseline_by_config, baseline_by_name = index_baseline(baseline)
    executed = [r for r in current.get("runtimes", []) if r.get("status") != "omitted"]
    alerts, all_rows = [], []

    for r in executed:
        result, is_alert = classify_proof(r, baseline_by_config, baseline_by_name, cfg)
        all_rows.append(result)
        if is_alert:
            alerts.append(result)

    def sort_key(r):
        return (r.name, r.dm, r.solver)

    all_rows.sort(key=sort_key)
    alerts.sort(key=sort_key)

    # Compute total runtimes and add as first row
    cur_total = compute_total_runtime(current)
    base_total = compute_total_runtime(baseline)
    if base_total and base_total > 0:
        total_ratio = cur_total / base_total
        total_change = f"{(total_ratio - 1) * 100:+.1f}%"
        total_status = WARN if total_ratio >= 1.25 else OK
    else:
        total_change = "-"
        total_status = OK
    total_row = ProofResult(
        "**TOTAL**",
        "-",
        "-",
        total_status,
        f"{cur_total}s",
        f"{base_total}s" if base_total else "-",
        total_change,
    )
    all_rows.insert(0, total_row)
    if total_status == WARN:
        alerts.insert(0, total_row)

    lines = [
        f"<!-- {COMMENT_TAG}(start): mlkem-{cfg.param_set} -->",
        f"## CBMC Results (ML-KEM-{cfg.param_set})",
        "",
        "`*` default.",
        "",
    ]

    if alerts:
        lines += [f"{WARN} **Attention Required**", ""] + render_table(alerts) + [""]

    total = len(executed)
    configuration_label = "configuration" if total == 1 else "configurations"
    lines += (
        [
            "<details>",
            f"<summary>Full Results ({total} {configuration_label})</summary>",
            "",
        ]
        + render_table(all_rows)
        + [
            "",
            "</details>",
            "",
            f"<!-- {COMMENT_TAG}(end): mlkem-{cfg.param_set} -->",
        ]
    )
    return "\n".join(lines)


def post_or_update_comment(pr_number, body, cfg):
    """Post or update PR comment."""
    tag = f"<!-- {COMMENT_TAG}(start): mlkem-{cfg.param_set} -->"
    result = subprocess.run(
        [
            "gh",
            "api",
            f"repos/{GITHUB_REPOSITORY}/issues/{pr_number}/comments",
            "--jq",
            f'.[] | select(.body | startswith("{tag}")) | .id',
        ],
        capture_output=True,
        text=True,
    )
    existing_id = (
        result.stdout.strip().split("\n")[0]
        if result.returncode == 0 and result.stdout.strip()
        else None
    )

    with tempfile.NamedTemporaryFile(mode="w", suffix=".md", delete=False) as f:
        f.write(body)
        tmp_path = f.name

    try:
        if existing_id:
            subprocess.run(
                [
                    "gh",
                    "api",
                    f"repos/{GITHUB_REPOSITORY}/issues/comments/{existing_id}",
                    "-X",
                    "PATCH",
                    "-F",
                    f"body=@{tmp_path}",
                ],
                check=True,
            )
            print(f"Updated existing comment {existing_id}")
        else:
            subprocess.run(
                [
                    "gh",
                    "api",
                    f"repos/{GITHUB_REPOSITORY}/issues/{pr_number}/comments",
                    "-X",
                    "POST",
                    "-F",
                    f"body=@{tmp_path}",
                ],
                check=True,
            )
            print("Created new comment")
    finally:
        os.unlink(tmp_path)


def push_to_gh_pages(current, cfg):
    """Push results to gh-pages branch using GitHub Contents API."""
    file_path = f"{cfg.data_dir}/mlkem-{cfg.param_set}.json"
    content_b64 = base64.b64encode(json.dumps(current, indent=2).encode()).decode()

    result = subprocess.run(
        [
            "gh",
            "api",
            f"repos/{GITHUB_REPOSITORY}/contents/{file_path}?ref={cfg.gh_pages_branch}",
            "--jq",
            ".sha",
        ],
        capture_output=True,
        text=True,
    )
    sha = result.stdout.strip() if result.returncode == 0 else ""

    cmd = [
        "gh",
        "api",
        f"repos/{GITHUB_REPOSITORY}/contents/{file_path}",
        "-X",
        "PUT",
        "-F",
        f"message=Update CBMC results for ML-KEM-{cfg.param_set} ({GITHUB_SHA})",
        "-F",
        f"content={content_b64}",
        "-F",
        f"branch={cfg.gh_pages_branch}",
    ]
    if sha:
        cmd.extend(["-F", f"sha={sha}"])

    subprocess.run(cmd, check=True)
    print(f"Pushed results to {cfg.gh_pages_branch}")


def main():
    args = get_args()
    args.param_set = {"2": "512", "3": "768", "4": "1024"}[args.mlkem_k]

    with open(args.results_json) as f:
        current = json.load(f)
    baseline = fetch_baseline(args)

    pr_number = get_pr_number()
    if pr_number:
        post_or_update_comment(pr_number, build_comment(current, baseline, args), args)
    elif GITHUB_REF in ("refs/heads/main", "refs/heads/master"):
        push_to_gh_pages(current, args)
    else:
        print(f"Not a PR and not main branch ({GITHUB_REF}), skipping")


if __name__ == "__main__":
    main()
