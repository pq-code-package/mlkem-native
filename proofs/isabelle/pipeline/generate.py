#!/usr/bin/env python3
"""Generate preprocessed C and corresponding Isabelle theory files for proofs/isabelle."""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from pathlib import Path
from typing import Iterable


def run(cmd: list[str], cwd: Path | None = None) -> str:
    proc = subprocess.run(cmd, cwd=str(cwd) if cwd else None, text=True, capture_output=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"Command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        )
    return proc.stdout


def find_compile_command(
    repo_root: Path,
    build_dir: Path,
    source: str,
    parameter_set: int,
    opt: int,
    auto: int,
) -> list[str]:
    object_target = f"{build_dir}/mlkem{parameter_set}/{source}.o"
    out = run(
        [
            "make",
            "-C",
            str(repo_root),
            "-n",
            f"BUILD_DIR={build_dir}",
            f"PARAMETER_SET={parameter_set}",
            f"OPT={opt}",
            f"AUTO={auto}",
            object_target,
        ]
    )

    compile_line = None
    for line in out.splitlines():
        stripped = line.strip()
        if " -c " in stripped and " -o " in stripped and stripped.endswith(source):
            compile_line = stripped
    if compile_line is None:
        raise RuntimeError(
            "Could not locate compile command in make -n output for "
            f"source {source}."
        )
    return shlex.split(compile_line)


def extract_cpp_flags(tokens: list[str], source: str) -> list[str]:
    keep = []
    i = 1
    while i < len(tokens):
        tok = tokens[i]

        if tok in {"-c", "-S", "-o"}:
            if tok == "-o":
                i += 2
            else:
                i += 1
            continue

        if tok == source or tok.endswith(f"/{source}"):
            i += 1
            continue

        if tok in {"-D", "-U", "-I", "-include", "-isystem", "-std"}:
            if i + 1 >= len(tokens):
                raise RuntimeError(f"Missing argument after {tok}")
            keep.extend([tok, tokens[i + 1]])
            i += 2
            continue

        if tok.startswith(("-D", "-U", "-I", "-include", "-isystem", "-std=")):
            keep.append(tok)
            i += 1
            continue

        if tok in {"-nostdinc", "-nostdinc++"}:
            keep.append(tok)
            i += 1
            continue

        i += 1

    return keep


def render_template(path: Path, replacements: dict[str, str]) -> str:
    content = path.read_text()
    for key, value in replacements.items():
        content = content.replace("{" + key + "}", value)
    return content


def quote_isabelle_string(raw: str) -> str:
    escaped = raw.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{escaped}"'


def render_manifest_text(manifest_cfg: dict) -> str:
    functions = list(manifest_cfg.get("functions", []))
    types = list(manifest_cfg.get("types", []))
    if not functions and not types:
        raise RuntimeError("manifest must contain at least one of: functions, types")

    lines: list[str] = []
    if functions:
        lines.append("functions:")
        lines.extend(f"- {name}" for name in functions)
        lines.append("")
    if types:
        lines.append("types:")
        lines.extend(f"- {name}" for name in types)
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def maybe_write_manifest_cfg(
    proof_root: Path, unit_name: str, manifest_cfg: dict | None, action: str, label: str
) -> str | None:
    if not manifest_cfg:
        return None

    output_rel = manifest_cfg.get("output")
    if not output_rel:
        raise RuntimeError(f"[{unit_name}] {label}.output is required")

    if action in {"preprocess", "theory", "all"}:
        manifest_text = render_manifest_text(manifest_cfg)
        out_path = proof_root / output_rel
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(manifest_text)
        print(f"[{unit_name}] wrote {out_path}")

    return output_rel


def mk_micro_c_file_options(unit: dict, manifest_output: str | None) -> str:
    parts: list[str] = []
    prefix = unit.get("prefix")
    if prefix:
        parts.append(f"prefix: {prefix}")
    addr_ty = unit.get("addr_ty")
    if addr_ty:
        parts.append(f"addr: {addr_ty}")
    gv_ty = unit.get("gv_ty")
    if gv_ty:
        parts.append(f"gv: {gv_ty}")
    if manifest_output:
        parts.append(f"manifest: {quote_isabelle_string(manifest_output)}")
    if not parts:
        return ""
    return " ".join(parts) + " "


def iter_units(config_units: list[dict], unit_filter: str | None) -> Iterable[dict]:
    for unit in config_units:
        if unit_filter is None or unit["name"] == unit_filter:
            yield unit


def _find_function_with_body(source: str, name: str) -> str:
    needle = f"{name}("
    pos = 0
    while True:
        i = source.find(needle, pos)
        if i < 0:
            raise RuntimeError(f"Could not find function definition for {name}")

        line_start = source.rfind("\n", 0, i)
        line_start = 0 if line_start < 0 else line_start + 1

        semi = source.find(";", i)
        brace = source.find("{", i)
        if brace < 0:
            raise RuntimeError(f"No function body found for {name}")
        if semi >= 0 and semi < brace:
            # Prototype/call-site; keep searching.
            pos = semi + 1
            continue

        depth = 0
        j = brace
        in_str = None
        in_line_comment = False
        in_block_comment = False

        while j < len(source):
            ch = source[j]
            nxt = source[j + 1] if j + 1 < len(source) else ""

            if in_line_comment:
                if ch == "\n":
                    in_line_comment = False
                j += 1
                continue

            if in_block_comment:
                if ch == "*" and nxt == "/":
                    in_block_comment = False
                    j += 2
                else:
                    j += 1
                continue

            if in_str is not None:
                if ch == "\\":
                    j += 2
                    continue
                if ch == in_str:
                    in_str = None
                j += 1
                continue

            if ch == "/" and nxt == "/":
                in_line_comment = True
                j += 2
                continue

            if ch == "/" and nxt == "*":
                in_block_comment = True
                j += 2
                continue

            if ch in {'"', "'"}:
                in_str = ch
                j += 1
                continue

            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = j + 1
                    return source[line_start:end].strip() + "\n"
            j += 1

        raise RuntimeError(f"Unbalanced braces while parsing {name}")


def extract_function_subset(preprocessed: str, extract_cfg: dict) -> str:
    functions = extract_cfg.get("functions", [])
    if not functions:
        raise RuntimeError("extract.mode=function_subset requires a non-empty functions list")

    preamble_lines = extract_cfg.get("preamble", [])
    out_parts = []
    if preamble_lines:
        out_parts.append("\n".join(preamble_lines).rstrip() + "\n\n")

    for fn in functions:
        out_parts.append(_find_function_with_body(preprocessed, fn).rstrip() + "\n\n")

    return "".join(out_parts).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--proof-root", required=True, type=Path)
    parser.add_argument("--unit", default=None)
    parser.add_argument("--parameter-set", type=int, default=None)
    parser.add_argument("--opt", type=int, default=0)
    parser.add_argument("--auto", type=int, default=0)
    parser.add_argument("--action", choices=["flags", "preprocess", "theory", "correctness", "all"], default="all")
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    proof_root = args.proof_root.resolve()
    pipeline_dir = proof_root / "pipeline"
    units_path = pipeline_dir / "units.json"
    cfg = json.loads(units_path.read_text())

    build_dir = proof_root / "generated" / "make-build"
    build_dir.mkdir(parents=True, exist_ok=True)

    template_path = pipeline_dir / "templates" / "definitions.thy.tpl"
    correctness_template_path = pipeline_dir / "templates" / "functional_correctness.thy.tpl"

    selected = list(iter_units(cfg["units"], args.unit))
    if not selected:
        raise RuntimeError("No units selected. Check --unit or pipeline/units.json")

    for unit in selected:
        source = unit["source"]
        param_set = args.parameter_set if args.parameter_set is not None else int(unit.get("parameter_set", 512))
        manifest_output = maybe_write_manifest_cfg(
            proof_root, unit["name"], unit.get("manifest"), args.action, "manifest"
        )
        type_manifest_output = maybe_write_manifest_cfg(
            proof_root, unit["name"], unit.get("type_manifest"), args.action, "type_manifest"
        )
        micro_c_file_options = mk_micro_c_file_options(unit, manifest_output)

        compile_tokens = find_compile_command(
            repo_root=repo_root,
            build_dir=build_dir,
            source=source,
            parameter_set=param_set,
            opt=args.opt,
            auto=args.auto,
        )
        compiler = compile_tokens[0]
        cpp_flags = extract_cpp_flags(compile_tokens, source)
        cpp_overrides = unit.get("cpp_overrides", [])
        if cpp_overrides:
            cpp_flags = [*cpp_flags, *cpp_overrides]

        if args.action in {"flags", "all"}:
            print(f"[{unit['name']}] compiler: {compiler}")
            print(f"[{unit['name']}] parameter_set: {param_set}, opt={args.opt}, auto={args.auto}")
            print(f"[{unit['name']}] cpp flags: {' '.join(cpp_flags)}")

        pre_out = proof_root / unit["output_c"]
        thy_out = proof_root / unit["output_theory"]

        if args.action in {"preprocess", "all"}:
            pre_out.parent.mkdir(parents=True, exist_ok=True)
            src_abs = repo_root / source
            preprocessed = run([compiler, "-E", "-P", *cpp_flags, str(src_abs)], cwd=repo_root)
            extract_cfg = unit.get("extract")
            if extract_cfg:
                mode = extract_cfg.get("mode")
                if mode == "function_subset":
                    preprocessed = extract_function_subset(preprocessed, extract_cfg)
                else:
                    raise RuntimeError(f"Unsupported extract mode: {mode}")
            banner = (
                "/* Auto-generated by proofs/isabelle/pipeline/generate.py. */\n"
                f"/* Source: {source}; PARAMETER_SET={param_set}; OPT={args.opt}; AUTO={args.auto} */\n\n"
            )
            pre_out.write_text(banner + preprocessed)
            print(f"[{unit['name']}] wrote {pre_out}")

        if args.action in {"theory", "all"}:
            thy_out.parent.mkdir(parents=True, exist_ok=True)
            rendered = render_template(
                template_path,
                {
                    "THEORY_NAME": unit["theory_name"],
                    "SOURCE_FILE": source,
                    "PREPROCESSED_FILE": unit["output_c"],
                    "ISABELLE_PRELUDE": ("\n".join(unit.get("isabelle_prelude", [])) + "\n\n") if unit.get("isabelle_prelude") else "",
                    "ISABELLE_POSTLUDE": ("\n".join(unit.get("isabelle_postlude", [])) + "\n") if unit.get("isabelle_postlude") else "",
                    "MICRO_C_FILE_OPTIONS": micro_c_file_options,
                    "TYPE_MANIFEST_OUTPUT": type_manifest_output or "",
                },
            )
            thy_out.write_text(rendered)
            print(f"[{unit['name']}] wrote {thy_out}")

        if args.action in {"correctness", "all"}:
            out_fc = unit.get("output_correctness_theory")
            name_fc = unit.get("correctness_theory_name")
            if out_fc and name_fc:
                out_fc_path = proof_root / out_fc
                out_fc_path.parent.mkdir(parents=True, exist_ok=True)
                rendered_fc = render_template(
                    correctness_template_path,
                    {
                        "CORRECTNESS_THEORY_NAME": name_fc,
                        "DEFINITIONS_THEORY_NAME": unit["theory_name"],
                        "SOURCE_FILE": source,
                    },
                )
                out_fc_path.write_text(rendered_fc)
                print(f"[{unit['name']}] wrote {out_fc_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
