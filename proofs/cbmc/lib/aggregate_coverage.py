#!/usr/bin/env python3
#
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

"""Join the cbmc-viewer reports produced by one CBMC proof run."""

import argparse
import json
import pathlib
import subprocess
import sys


def get_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=pathlib.Path)
    parser.add_argument("--reportdir", required=True, type=pathlib.Path)
    parser.add_argument("--srcdir", required=True, type=pathlib.Path)
    return parser.parse_args()


def load_manifest(path):
    with path.open(encoding="utf-8") as handle:
        manifest = json.load(handle)
    if manifest.get("schema") != 2:
        raise ValueError(f"Unsupported coverage manifest schema in {path}")
    reports = manifest.get("reports")
    if not isinstance(reports, list) or not reports:
        raise ValueError(f"Coverage manifest {path} has no reports")
    return manifest


def report_inputs(manifest):
    coverage_files = []
    source_files = []
    missing = []
    for report in manifest["reports"]:
        report_dir = pathlib.Path(report["directory"])
        coverage = report_dir / "json" / "viewer-coverage.json"
        source = report_dir / "json" / "viewer-source.json"
        coverage_files.append(coverage)
        source_files.append(source)
        missing.extend(path for path in (coverage, source) if not path.is_file())

    if missing:
        joined = "\n".join(str(path) for path in missing)
        raise FileNotFoundError(f"Missing coverage report inputs:\n{joined}")
    return coverage_files, source_files


def main():
    args = get_args()
    manifest = load_manifest(args.manifest)
    coverage_files, source_files = report_inputs(manifest)

    command = [
        "cbmc-viewer",
        "--viewer-coverage",
        *map(str, coverage_files),
        "--viewer-source",
        *map(str, source_files),
        "--srcdir",
        str(args.srcdir),
        "--reportdir",
        str(args.reportdir),
    ]
    subprocess.run(command, check=True)

    metadata = {
        "schema": 2,
        "parameter_set": manifest["parameter_set"],
        "variant": manifest["variant"],
        "data_model": manifest["data_model"],
        "configurations": len(manifest["reports"]),
    }
    with (args.reportdir / "metadata.json").open("w", encoding="utf-8") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)
        handle.write("\n")


if __name__ == "__main__":
    try:
        main()
    except (KeyError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"aggregate-coverage: {error}", file=sys.stderr)
        sys.exit(1)
