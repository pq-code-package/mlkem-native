# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Check Markdown links and publish the results to a pull request.

Run from the repository root in GitHub Actions.

    python3 .github/scripts/markdown-links.py check REPORT.json
        Run markdown-link-check and fail on broken internal links.
    python3 .github/scripts/markdown-links.py comment REPORT.json
        Create or update the same-repository PR comment from the report.
"""

import html
import json
import os
import re
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

MARKER = "<!-- markdown-links -->"
MAX_ROWS = 40


def is_internal(link):
    # The checker resolves paths and fragments against the local checkout.
    return link.lower().startswith("file:") or not (
        link.startswith("//") or re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", link)
    )


def check_file(filename):
    with tempfile.TemporaryDirectory() as tmpdir:
        output = Path(tmpdir) / "report.xml"
        result = subprocess.run(
            [
                "markdown-link-check",
                "--quiet",
                "--config",
                ".github/mlc_config.json",
                "--reporters",
                "junit",
                "--junit-output",
                str(output),
                "--",
                f"./{filename}",
            ]
        )
        # Exit 1 also means a dead link was found. Require a complete report
        # before using the per-link results to decide what fails the job.
        suite = ET.parse(output).getroot().find("testsuite")
        if (
            result.returncode not in (0, 1)
            or suite is None
            or suite.find("./properties/property[@name='file']").get("value")
            != f"./{filename}"
            or suite.find("./testcase/error[@type='ProcessingError']") is not None
            or (result.returncode == 1) != (int(suite.get("failures")) > 0)
        ):
            raise RuntimeError(f"Markdown link checker failed for {filename!r}")

        findings = []
        for case in suite.findall("testcase"):
            props = {
                prop.get("name"): prop.get("value")
                for prop in case.findall("./properties/property")
            }
            if props["status"] in ("dead", "error"):
                findings.append((filename, props["url"], props.get("statusCode", "")))
        return findings


def check_links(output):
    files = subprocess.check_output(["git", "ls-files", "-z", "--", "*.md"])
    filenames = map(os.fsdecode, files.split(b"\0")[:-1])
    with ThreadPoolExecutor(max_workers=16) as pool:
        findings = [row for rows in pool.map(check_file, filenames) for row in rows]

    report = {}
    for key, internal in (("errors", True), ("warnings", False)):
        rows = [row for row in findings if is_internal(row[1]) == internal]
        report[key] = {
            "count": len(rows),
            "rows": [[field[:320] for field in row] for row in rows[:MAX_ROWS]],
        }
    if os.getenv("PR_NUMBER"):
        output.write_text(json.dumps(report), encoding="utf-8")
    else:
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
            summary.write(render_report(report))
    return int(report["errors"]["count"] != 0)


def render_report(report):
    lines = ["## Markdown link check", ""]
    for key, label, icon in (
        ("errors", "Broken internal links", "❌"),
        ("warnings", "Unreachable external links", "⚠️"),
    ):
        count = report[key]["count"]
        rows = report[key]["rows"]
        if type(count) is not int or not 0 <= len(rows) <= min(count, MAX_ROWS):
            raise ValueError(f"Invalid Markdown link report section: {key}")
        if count == 0:
            continue
        lines += [f"**{label} ({count})**", "", "<pre>"]
        size = 0
        shown = 0
        for file, link, status in rows:
            text = f"{file[:320]} → {link[:320]}"
            if status.isascii() and status.isdecimal() and len(status) == 3:
                text += f" ({status})"
            text = "".join(c if c.isprintable() else " " for c in text)
            line = f"{icon} {html.escape(text, quote=False)}"
            size += len(line.encode("utf-8")) + 1
            if size > 28_000:
                break
            lines.append(line)
            shown += 1
        lines += ["</pre>", ""]
        if count > shown:
            lines += [f"Showing {shown} of {count}.", ""]
    if len(lines) == 2:
        lines += ["✅ No broken Markdown links found.", ""]
    return "\n".join(lines)


def gh_api(path, *args):
    return subprocess.check_output(["gh", "api", path, *args])


def comment(report_file):
    if not report_file.is_file():
        return
    report = json.loads(report_file.read_text(encoding="utf-8"))
    repo = os.environ["GITHUB_REPOSITORY"]
    number = int(os.environ["PR_NUMBER"])

    # A rerun can check a commit that has since been replaced on the PR.
    pr = json.loads(gh_api(f"repos/{repo}/pulls/{number}"))
    head = pr["head"]
    if (
        pr["state"] != "open"
        or not head["repo"]
        or head["repo"]["full_name"] != repo
        or head["sha"] != os.environ["PR_HEAD_SHA"]
    ):
        print("Markdown link report does not match the current pull request head")
        return

    comments = f"repos/{repo}/issues/{number}/comments"
    matches = gh_api(
        comments,
        "--paginate",
        "--jq",
        f'.[] | select(.user.login == "github-actions[bot]" and '
        f'(.body | startswith("{MARKER}\\n"))) | .id',
    ).splitlines()
    if matches:
        path = f"repos/{repo}/issues/comments/{int(matches[0])}"
        method = "PATCH"
    elif report["errors"]["count"] or report["warnings"]["count"]:
        path = comments
        method = "POST"
    else:
        return
    body = f"{MARKER}\n{render_report(report)}"
    gh_api(path, "--method", method, "--raw-field", f"body={body}")


if __name__ == "__main__":
    if sys.argv[1] == "check":
        raise SystemExit(check_links(Path(sys.argv[2])))
    elif sys.argv[1] == "comment":
        comment(Path(sys.argv[2]))
    else:
        raise SystemExit(f"Unknown command: {sys.argv[1]}")
