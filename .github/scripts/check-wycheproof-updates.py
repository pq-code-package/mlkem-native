#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#
# CI helper: compare the Wycheproof commit pinned by the test client against the
# upstream default branch and, if the tracked test vectors have changed, open
# (or refresh) a tracking issue in $GITHUB_REPOSITORY.
#
# Only testvectors_v1 files whose name begins with VECTOR_PREFIX are considered;
# all other vectors are ignored.
#

import json
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path

WYCHEPROOF_REPO = "C2SP/wycheproof"
DEFAULT_BRANCH = "main"
CONTENTS_URL = f"https://api.github.com/repos/{WYCHEPROOF_REPO}/contents/testvectors_v1"
COMMIT_URL = f"https://api.github.com/repos/{WYCHEPROOF_REPO}/commits/{DEFAULT_BRANCH}"

# Only testvectors_v1 files with this filename prefix are tracked.
# To port to another scheme, change the prefix (e.g. "mldsa_").
VECTOR_PREFIX = "mlkem_"

# Tracking issue label (used to dedupe).
ISSUE_LABEL = "wycheproof-update"

# Repository to open the tracking issue in, and the client holding the pin.
REPO = os.environ["GITHUB_REPOSITORY"]
CLIENT = Path(__file__).resolve().parents[2] / "test/wycheproof/wycheproof_client.py"


def request(method, url, data=None):
    """Issue a GitHub API request and return the parsed JSON body (or None)."""
    headers = {"Accept": "application/vnd.github+json"}
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    body = None
    if data is not None:
        body = json.dumps(data).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=body, headers=headers, method=method)
    with urllib.request.urlopen(req) as resp:
        raw = resp.read()
        return json.loads(raw) if raw else None


def read_pinned_commit():
    text = CLIENT.read_text(encoding="utf-8")
    m = re.search(r'^WYCHEPROOF_COMMIT\s*=\s*"([0-9a-f]{40})"', text, re.MULTILINE)
    if not m:
        sys.exit(f"Could not find WYCHEPROOF_COMMIT in {CLIENT}")
    return m.group(1)


def tracked_blobs(ref):
    """Return {filename: blob_sha} for tracked files in testvectors_v1 at ref."""
    entries = request("GET", f"{CONTENTS_URL}?ref={ref}")
    return {
        e["name"]: e["sha"]
        for e in entries
        if e["type"] == "file" and e["name"].startswith(VECTOR_PREFIX)
    }


def build_report():
    """Return (report_text, has_updates, head_sha, head_date)."""
    pinned_commit = read_pinned_commit()
    pinned = tracked_blobs(pinned_commit)
    latest = tracked_blobs(DEFAULT_BRANCH)
    commit = request("GET", COMMIT_URL)
    head = commit["sha"]
    head_date = commit["commit"]["committer"]["date"][:10]

    changed = sorted(f for f in pinned.keys() & latest.keys() if pinned[f] != latest[f])
    added = sorted(latest.keys() - pinned.keys())
    removed = sorted(pinned.keys() - latest.keys())

    lines = [
        f"Pinned commit:    {pinned_commit}",
        f"Upstream {DEFAULT_BRANCH} HEAD: {head} ({head_date})",
        f"Compare: https://github.com/{WYCHEPROOF_REPO}/compare/{pinned_commit}...{head}",
        "",
    ]
    if not (changed or added or removed):
        lines.append("Test vectors are up to date.")
        return "\n".join(lines), False, head, head_date

    lines.append("Test vector updates detected upstream:")
    for f in changed:
        lines.append(f"  changed: {f}")
    for f in added:
        lines.append(f"  added:   {f}")
    for f in removed:
        lines.append(f"  removed: {f}")
    lines.append("")
    lines.append(
        f"To adopt, set WYCHEPROOF_COMMIT to {head} in "
        "test/wycheproof/wycheproof_client.py"
    )
    if added:
        lines.append("and add the new file(s) to WYCHEPROOF_FILES.")
    return "\n".join(lines), True, head, head_date


def ensure_label():
    """Create the tracking label if it does not already exist."""
    try:
        request(
            "POST",
            f"https://api.github.com/repos/{REPO}/labels",
            {
                "name": ISSUE_LABEL,
                "color": "ededed",
                "description": "Upstream Wycheproof vector update tracking",
            },
        )
    except urllib.error.HTTPError as e:
        if e.code != 422:  # 422 == label already exists
            raise


def upsert_issue(report, head, head_date):
    """Open the tracking issue, or refresh it if one is already open."""
    title = f"Update Wycheproof test vectors to {head[:7]} ({head_date})"
    body = (
        "New test vectors have landed on the "
        f"[{WYCHEPROOF_REPO}](https://github.com/{WYCHEPROOF_REPO}) default branch "
        "since the commit pinned in `test/wycheproof/wycheproof_client.py`.\n\n"
        f"```\n{report}\n```\n\n"
        "_Opened and refreshed automatically by the `Wycheproof updates` workflow._"
    )
    ensure_label()
    open_issues = request(
        "GET",
        f"https://api.github.com/repos/{REPO}/issues"
        f"?state=open&labels={ISSUE_LABEL}&per_page=1",
    )
    if open_issues:
        number = open_issues[0]["number"]
        request(
            "PATCH",
            f"https://api.github.com/repos/{REPO}/issues/{number}",
            {"title": title, "body": body},
        )
        print(f"Updated existing issue #{number}")
    else:
        created = request(
            "POST",
            f"https://api.github.com/repos/{REPO}/issues",
            {"title": title, "body": body, "labels": [ISSUE_LABEL]},
        )
        print(f"Opened issue #{created['number']}")


def main():
    report, has_updates, head, head_date = build_report()
    print(report)
    if has_updates:
        upsert_issue(report, head, head_date)


if __name__ == "__main__":
    main()
