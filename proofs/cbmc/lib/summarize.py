# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

import argparse
import json
import logging
import os
import sys


DESCRIPTION = """Print 2 tables in GitHub-flavored Markdown that summarize
an execution of CBMC proofs."""


def get_args():
    """Parse arguments for summarize script."""
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    for arg in [
        {
            "flags": ["--run-file"],
            "help": "path to the Litani run.json file",
            "required": True,
        },
        {
            "flags": ["--output-result-json"],
            "help": "path to export result JSON",
            "required": False,
        },
    ]:
        flags = arg.pop("flags")
        parser.add_argument(*flags, **arg)
    return parser.parse_args()


def _get_max_length_per_column_list(data):
    ret = [len(item) + 1 for item in data[0]]
    for row in data[1:]:
        for idx, item in enumerate(row):
            ret[idx] = max(ret[idx], len(item) + 1)
    return ret


def _get_table_header_separator(max_length_per_column_list):
    line_sep = ""
    for max_length_of_word_in_col in max_length_per_column_list:
        line_sep += "|" + "-" * (max_length_of_word_in_col + 1)
    line_sep += "|\n"
    return line_sep


def _get_entries(max_length_per_column_list, row_data):
    entries = []
    for row in row_data:
        entry = ""
        for idx, word in enumerate(row):
            max_length_of_word_in_col = max_length_per_column_list[idx]
            space_formatted_word = (max_length_of_word_in_col - len(word)) * " "
            entry += "| " + word + space_formatted_word
        entry += "|\n"
        entries.append(entry)
    return entries


def _get_rendered_table(data):
    table = []
    max_length_per_column_list = _get_max_length_per_column_list(data)
    entries = _get_entries(max_length_per_column_list, data)
    for idx, entry in enumerate(entries):
        if idx == 1:
            line_sep = _get_table_header_separator(max_length_per_column_list)
            table.append(line_sep)
        table.append(entry)
    table.append("\n")
    return "".join(table)


def _split_pipeline_name(pipeline_name):
    """Split `<PROOF_UID>__<DM>__<SOLVER>` into its components."""
    if "__" not in pipeline_name:
        return None, None, None
    parts = pipeline_name.rsplit("__", 2)
    if len(parts) == 3:
        return tuple(parts)
    # Compatibility with run files from before DM became a proof dimension.
    proof_uid, solver = parts
    legacy_profiles = {
        "Z3": "z3",
        "BITWUZLA": "bitwuzla",
        "CVC5": "cvc5_arrays_exp",
    }
    return proof_uid, "LP64", legacy_profiles.get(solver, solver)


# Marker emitted by cbmc when the SMT backend returned `unknown` on the
# verification query. cbmc still exits non-zero (cprover-status: ERROR)
# in this case, so the pipeline shows up as `fail` in litani; but no
# property was actually refuted -- the solver simply could not decide.
# We surface this as a distinct "Inconclusive" outcome.
_SOLVER_UNKNOWN_MARKER = 'SMT2 solver returned "unknown"'


def _is_solver_inconclusive(stdout_file):
    """Return True iff the cbmc safety-check job's stdout-file (result.xml)
    contains the cbmc message indicating the SMT backend returned `unknown`.
    """
    if not stdout_file:
        return False
    try:
        with open(stdout_file, encoding="utf-8", errors="replace") as f:
            return _SOLVER_UNKNOWN_MARKER in f.read()
    except OSError:
        return False


def _parse_proof_pipeline(proof_pipeline):
    """Parse a single proof pipeline, returning
    (name, dm, solver, status, duration, has_timeout)."""
    duration = 0
    has_timeout = False
    inconclusive = False
    has_other_failure = False
    for stage in proof_pipeline["ci_stages"]:
        for job in stage["jobs"]:
            if job.get("timeout_reached", False):
                has_timeout = True
            if "duration" in job:
                duration += int(job["duration"])
            # Identify the safety-check job by its description suffix.
            # Litani stores both description and stdout_file under
            # wrapper_arguments (the args passed to `litani add-job`).
            wa = job.get("wrapper_arguments") or {}
            desc = wa.get("description") or ""
            job_inconclusive = desc.endswith(
                ": checking safety properties"
            ) and _is_solver_inconclusive(wa.get("stdout_file"))
            if job_inconclusive:
                inconclusive = True
            if job.get("outcome") in ("fail", "fail_ignored") and not job_inconclusive:
                has_other_failure = True

    if has_timeout:
        status = "Timeout"
    elif proof_pipeline["status"] == "fail" and inconclusive and not has_other_failure:
        status = "Inconclusive"
    else:
        status = proof_pipeline["status"].title()
    name, dm, solver = _split_pipeline_name(proof_pipeline["name"])
    return name, dm, solver, status, duration, has_timeout


def _get_proof_records(
    run_dict,
    omitted_configs=None,
    default_configs=None,
    exploratory_configs=None,
):
    """Return normalized records for every selected proof configuration."""
    default_configs = set(default_configs or ())
    exploratory_configs = set(exploratory_configs or ())
    records = []
    for proof_pipeline in run_dict["pipelines"]:
        if proof_pipeline["name"] == "print_tool_versions":
            continue

        name, dm, solver, status, duration, has_timeout = _parse_proof_pipeline(
            proof_pipeline
        )
        if name is None:
            name, dm, solver = proof_pipeline["name"], "-", "-"
        key = (name, dm, solver)
        records.append(
            {
                "name": name,
                "dm": dm,
                "solver": solver,
                "status": status.replace("_", " "),
                "duration": "TIMEOUT" if has_timeout else str(duration),
                "duration_seconds": duration,
                "default": key in default_configs,
                "exploratory": key in exploratory_configs,
            }
        )

    for name, dm, solver in omitted_configs or ():
        key = (name, dm, solver)
        records.append(
            {
                "name": name,
                "dm": dm,
                "solver": solver,
                "status": "-",
                "duration": "",
                "duration_seconds": None,
                "default": key in default_configs,
                "exploratory": False,
            }
        )

    records.sort(key=lambda record: (record["name"], record["dm"], record["solver"]))
    return records


def _get_status_and_proof_summaries(
    run_dict,
    omitted_configs=None,
    default_configs=None,
    exploratory_configs=None,
):
    """Create status and per-configuration Markdown table data."""
    records = _get_proof_records(
        run_dict, omitted_configs, default_configs, exploratory_configs
    )
    count_statuses = {}

    for record in records:
        if record["status"] == "-":
            count_statuses["Omitted"] = count_statuses.get("Omitted", 0) + 1
            continue
        count_statuses[record["status"]] = count_statuses.get(record["status"], 0) + 1

    proofs = [["Proof", "DM", "Solver", "Status", "Duration (in s)"]]
    for record in records:
        solver = record["solver"]
        if record["default"]:
            solver += "*"
        if record["exploratory"]:
            solver += " (explore)"
        proofs.append(
            [
                record["name"],
                record["dm"],
                solver,
                record["status"],
                record["duration"],
            ]
        )

    statuses = [["Status", "Count"]]
    for status, count in count_statuses.items():
        statuses.append([status, str(count)])
    return [statuses, proofs]


def export_result_json(
    output_path,
    run_file,
    omitted_configs=None,
    default_configs=None,
    exploratory_configs=None,
):
    """Export JSON with summary, failures, and runtimes."""
    if output_path is None:
        return

    with open(run_file, encoding="utf-8") as f:
        run_dict = json.load(f)

    records = _get_proof_records(
        run_dict, omitted_configs, default_configs, exploratory_configs
    )
    failures, runtimes = [], []
    for record in records:
        name = record["name"]
        dm = record["dm"]
        solver = record["solver"]
        status = record["status"]
        duration = record["duration"]
        metadata = {
            "name": name,
            "dm": dm,
            "solver": solver,
            "default": record["default"],
            "exploratory": record["exploratory"],
        }

        if status == "-":
            runtimes.append(metadata | {"status": "omitted"})
            continue

        if status == "Inconclusive":
            runtimes.append(metadata | {"status": "inconclusive", "duration": duration})
            continue

        if status != "Success":
            failures.append(metadata | {"status": status, "duration": duration})

        runtime = metadata | {"unit": "seconds"}
        if status == "Success":
            runtime["value"] = record["duration_seconds"]
        else:
            runtime["status"] = "failed"
        runtimes.append(runtime)

    total = len(runtimes)
    failed = sum(1 for f in failures if f["status"] != "Timeout")
    timeout = sum(1 for f in failures if f["status"] == "Timeout")
    omitted = sum(1 for r in runtimes if r.get("status") == "omitted")
    inconclusive = sum(1 for r in runtimes if r.get("status") == "inconclusive")

    result = {
        "mlkem_k": os.getenv("MLKEM_K", "unknown"),
        "summary": {
            "total": total,
            "success": total - failed - timeout - omitted - inconclusive,
            "failed": failed,
            "timeout": timeout,
            "omitted": omitted,
            "inconclusive": inconclusive,
        },
        "failures": failures,
        "runtimes": runtimes,
    }

    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)


def print_proof_results(
    out_file,
    omitted_configs=None,
    default_configs=None,
    exploratory_configs=None,
):
    """
    Print 2 strings that summarize the proof results.
    When printing, each string will render as a GitHub flavored Markdown table.
    """
    output = (
        "## Summary of CBMC proof results\n\n"
        "`*` default; `(explore)` undeclared configuration.\n\n"
    )
    with open(out_file, encoding="utf-8") as run_json:
        run_dict = json.load(run_json)
    status_table, proof_table = _get_status_and_proof_summaries(
        run_dict, omitted_configs, default_configs, exploratory_configs
    )
    for summary in (status_table, proof_table):
        output += _get_rendered_table(summary)

    print(output)
    sys.stdout.flush()

    github_summary_file = os.getenv("GITHUB_STEP_SUMMARY")
    if github_summary_file:
        with open(github_summary_file, "a") as handle:
            print(output, file=handle)
            handle.flush()
    else:
        logging.warning("$GITHUB_STEP_SUMMARY not set, not writing summary file")

    msg = (
        "Click the 'Summary' button to view a Markdown table "
        "summarizing all proof results"
    )

    # Inconclusive proofs did not refute a property, but they also did not
    # prove it and therefore fail the run.
    proof_statuses = [row[3] for row in proof_table[1:] if any(row)]
    has_timeout = any(s == "Timeout" for s in proof_statuses)
    has_real_failure = any(s == "Fail" for s in proof_statuses)
    has_inconclusive = any(s == "Inconclusive" for s in proof_statuses)
    has_tool_version_failure = any(
        pipeline["name"] == "print_tool_versions" and pipeline["status"] == "fail"
        for pipeline in run_dict["pipelines"]
    )

    if has_timeout or has_real_failure or has_inconclusive or has_tool_version_failure:
        logging.error("Not all CBMC jobs passed.")
        if has_timeout:
            logging.error("Some proofs timed out.")
        if has_inconclusive:
            logging.error(
                "Some (proof, DM, solver-profile) configurations were inconclusive "
                "(solver returned 'unknown')."
            )
        if has_tool_version_failure:
            logging.error("Printing tool versions failed.")
        logging.error(msg)
        sys.exit(1)
    logging.info(msg)


if __name__ == "__main__":
    args = get_args()
    logging.basicConfig(format="%(levelname)s: %(message)s")
    try:
        export_result_json(args.output_result_json, args.run_file)
        print_proof_results(args.run_file)
    except Exception as ex:  # pylint: disable=broad-except
        logging.critical("Could not print results. Exception: %s", str(ex))
