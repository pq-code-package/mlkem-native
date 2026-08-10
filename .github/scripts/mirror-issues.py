#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#
# CI helper: mirror the sibling repository's issues and merged pull requests
# flagged as needing a port into $GITHUB_REPOSITORY.
#
# Open issues become mirror issues; merged pull requests become port issues.
# Anything else carrying the label is skipped, so a labelled pull request is
# picked up by a later run once it merges.
#
# This runs in the target repository and only ever writes there, so the default
# GITHUB_TOKEN suffices; the sibling repository is only read.
#

import json
import os
import re
import urllib.parse
import urllib.request

# Sibling repository, and the label marking its issues as needing a port here.
SOURCE_REPO = "pq-code-package/mldsa-native"
SOURCE_LABEL = "needs-mlkem-native-port"

# Labels applied to the issues created here, also used to find them again.
MIRROR_LABEL = "mldsa-native-mirror"
PORT_LABEL = "mldsa-native-port"

TARGET_REPO = os.environ["GITHUB_REPOSITORY"]
API = "https://api.github.com"

SOURCE_URL_RE = re.compile(rf"https://github\.com/{SOURCE_REPO}/(?:issues|pull)/(\d+)")


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


def issues(repo, **params):
    """Yield every entry of the paginated issue list for repo."""
    page = 1
    while True:
        query = urllib.parse.urlencode({**params, "per_page": 100, "page": page})
        batch = request("GET", f"{API}/repos/{repo}/issues?{query}")
        if not batch:
            return
        yield from batch
        if len(batch) < 100:
            return
        page += 1


def already_mirrored():
    """Return the source numbers that already have an issue here."""
    numbers = set()
    for label in (MIRROR_LABEL, PORT_LABEL):
        for issue in issues(TARGET_REPO, state="all", labels=label):
            body = issue.get("body") or ""
            numbers.update(int(n) for n in SOURCE_URL_RE.findall(body))
    return numbers


def needs_mirror(entry):
    """Mirror open issues and merged pull requests, and nothing else."""
    pull_request = entry.get("pull_request")
    if pull_request is None:
        return entry["state"] == "open"
    return pull_request.get("merged_at") is not None


def mirror(entry):
    if "pull_request" in entry:
        title = f"Port: {entry['title']}"
        body = f"- Port of {entry['html_url']}"
        label = PORT_LABEL
    else:
        title = entry["title"]
        body = f"- Mirror issue of {entry['html_url']}"
        label = MIRROR_LABEL
    created = request(
        "POST",
        f"{API}/repos/{TARGET_REPO}/issues",
        {"title": title, "body": body, "labels": [label]},
    )
    print(f"Created #{created['number']} from {entry['html_url']}")


def main():
    seen = already_mirrored()
    todo = [
        e
        for e in issues(SOURCE_REPO, state="all", labels=SOURCE_LABEL)
        if e["number"] not in seen and needs_mirror(e)
    ]
    if not todo:
        print(f"Nothing new to mirror from {SOURCE_REPO} ('{SOURCE_LABEL}').")
        return
    for entry in todo:
        mirror(entry)


if __name__ == "__main__":
    main()
