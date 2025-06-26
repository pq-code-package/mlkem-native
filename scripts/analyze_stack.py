#!/usr/bin/env python3

import argparse
import glob
import os
import platform
import subprocess
import sys
import tempfile


def parse_su_files(build_dir):
    """Parse GCC stack usage (.su) files"""
    stack_usage = {}
    su_files = glob.glob(os.path.join(build_dir, "**", "*.su"), recursive=True)

    for su_file in su_files:
        with open(su_file, "r") as f:
                content = f.read()

        for line_num, line in enumerate(content.splitlines(), 1):
            line = line.strip()
            if not line:
                continue

            # Parse format: filename:line:column:function_name size qualifier
            parts = line.split()
            if len(parts) < 3:
                raise ValueError(
                    f"Unexpected .su file format in {su_file}:{line_num}: "
                    f"Expected at least 3 parts, got {len(parts)} in line: '{line}'"
                )

            location_func = parts[0]
            size_str = parts[1]
            qualifier = parts[2] if len(parts) > 2 else "static"

            # Extract function name from location:function format
            if ":" in location_func:
                func_name = location_func.split(":")[-1]
            else:
                func_name = location_func

            size = int(size_str)
            stack_usage[func_name] = {
                "size": size,
                "qualifier": qualifier,
            }

    return stack_usage

def run_valgrind_massif_per_api(stack_test_binary):
    """Run valgrind massif with API-level stack analysis using dedicated test binary"""
    # Determine parameter set from binary path
    if "stack_test512" in stack_test_binary:
        param_set = "512"
    elif "stack_test768" in stack_test_binary:
        param_set = "768"
    elif "stack_test1024" in stack_test_binary:
        param_set = "1024"
    else:
        return (
            False,
            "Could not determine ML-KEM parameter set from stack test binary path",
        )

    api_results = {}
    api_names = ["keygen", "encaps", "decaps"]
    api_display_names = [
        f"ML-KEM{param_set}-KeyGen",
        f"ML-KEM{param_set}-Encaps",
        f"ML-KEM{param_set}-Decaps",
    ]

    with tempfile.NamedTemporaryFile(mode="w+", suffix=".massif") as temp_file:
        massif_output = temp_file.name

        for api_name in api_names:
            cmd = [
                "valgrind",
                "--tool=massif",
                "--stacks=yes",
                f"--massif-out-file={massif_output}",
                "--quiet",
                stack_test_binary,
                api_name,
            ]

            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

            if result.returncode != 0:
                return (
                    False,
                    f"Valgrind massif failed for {api_name} with return code {result.returncode}: {result.stderr}",
                )

            try:
                with open(massif_output, "r") as f:
                    massif_content = f.read()
            except (OSError, IOError) as e:
                return False, f"Failed to read massif output file: {e}"

            peak_stack = 0
            for line in massif_content.split("\n"):
                if line.startswith("mem_stacks_B="):
                    try:
                        stack_bytes = int(line.split("=")[1])
                        peak_stack = max(peak_stack, stack_bytes)
                    except (ValueError, IndexError):
                        # Individual line parsing can fail, continue with other lines
                        continue

            api_results[api_name] = peak_stack

        # Format results
        result_lines = []
        for i, api_name in enumerate(api_names):
            stack_usage = api_results[api_name]
            display_name = api_display_names[i]
            if stack_usage > 0:
                result_lines.append(f"  {display_name:20}: {stack_usage:,} bytes")
            else:
                result_lines.append(f"  {display_name:20}: measurement failed")

        total_max = max(api_results.values())
        result_lines.append(
            f"  {'Peak':20}: {total_max:,} bytes (maximum across all APIs)"
        )

        return (
            True,
            f"API-specific stack usage (measured with valgrind massif):\n"
            + "\n".join(result_lines),
        )


def run_runtime_analysis(binary_path):
    """Run runtime stack analysis"""
    try:
        # Test the stack test binary with keygen argument
        test_result = subprocess.run(
            [binary_path, "keygen"], capture_output=True, text=True, timeout=30
        )
        if test_result.returncode != 0:
            return False, f"Stack test binary execution failed: {test_result.stderr}"
    except subprocess.TimeoutExpired:
        return False, "Binary execution timeout"
    except Exception as e:
        return False, str(e)

    # On Linux, try to use valgrind massif for runtime stack analysis
    if platform.system() == "Linux":
        try:
            subprocess.run(["valgrind", "--version"], capture_output=True, check=True)
            return run_valgrind_massif_per_api(binary_path)
        except (subprocess.CalledProcessError, FileNotFoundError):
            return (
                True,
                "Binary executed successfully (valgrind not available for runtime analysis)",
            )
    else:
        return (
            True,
            "Binary executed successfully (detailed runtime stack analysis requires valgrind on Linux)",
        )


def analyze_stack_usage(binary_path, build_dir, show_per_function=False):
    """Analyze stack usage for a binary"""
    print(f"Analyzing stack usage for: {binary_path}")
    print("=" * 50)

    # Static Analysis
    print("Static Analysis (GCC -fstack-usage):")
    print("-" * 40)

    stack_usage = parse_su_files(build_dir)

    # Sort by stack size
    sorted_functions = sorted(
        stack_usage.items(), key=lambda x: x[1]["size"], reverse=True
    )

    if show_per_function:
        for func_name, info in sorted_functions[:20]:  # Show top 20
            print(f"{func_name:50} {info['size']:6} bytes {info['qualifier']}")

        if len(sorted_functions) > 20:
            print(f"... and {len(sorted_functions) - 20} more functions")

    print(f"Total functions analyzed: {len(sorted_functions)}")

    if sorted_functions:
        # Always show the largest function for summary
        top_func, top_info = sorted_functions[0]
        print(
            f"Largest function: {top_func} ({top_info['size']:,} bytes {top_info['qualifier']})"
        )

    # Runtime Analysis
    print("\nRuntime Analysis:")
    print("-" * 40)

    success, message = run_runtime_analysis(binary_path)
    print(f"Runtime analysis: {message}")

    print()  # Empty line for spacing

    return success


def main():
    parser = argparse.ArgumentParser(
        description="Analyze stack usage of ML-KEM binaries"
    )
    parser.add_argument("binary", help="Path to the binary to analyze")
    parser.add_argument(
        "--build-dir", default="test/build", help="Build directory containing .su files"
    )
    parser.add_argument(
        "--per-function",
        action="store_true",
        help="Show per-function stack usage details",
    )

    args = parser.parse_args()

    if not os.path.exists(args.binary):
        print(f"Error: Binary not found: {args.binary}")
        return 1

    if not os.path.exists(args.build_dir):
        print(f"Error: Build directory not found: {args.build_dir}")
        return 1

    success = analyze_stack_usage(args.binary, args.build_dir, args.per_function)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
