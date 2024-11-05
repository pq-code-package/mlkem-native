# SPDX-License-Identifier: Apache-2.0

import platform
import os
import sys
import io
import logging
import subprocess
from functools import reduce
from typing import Optional, Callable, TypedDict
from util import (
    TEST_TYPES,
    SCHEME,
    sha256sum,
    parse_meta,
    config_logger,
    github_summary,
    logger,
)
import copy


class State(object):

    def __init__(self):
        self.verbose = False
        self.cross_prefix = ""
        self.cflags = ""
        self.arch_flags = ""
        self.auto = True
        self.compile = True
        self.run = True

    def compile_schemes(
        self,
        test_type: TEST_TYPES,
        opt: bool,
        extra_make_envs={},
        extra_make_args=[],
    ):
        """compile or cross compile with some extra environment variables and makefile arguments"""

        log = logger(test_type, "Compiling", self.cross_prefix, opt)

        def dict2str(dict):
            s = ""
            for k, v in dict.items():
                s += f"{k}={v} "
            return s

        make_envs = (
            {"CFLAGS": f"{self.cflags}"} if self.cflags is not None else {}
        ) | (
            {"ARCH_FLAGS": f"{self.arch_flags}"} if self.arch_flags is not None else {}
        )
        extra_make_envs.update(make_envs)

        extra_make_args = extra_make_args + list(
            set([f"OPT={int(opt)}", f"AUTO={int(self.auto)}"]) - set(extra_make_args)
        )

        args = [
            "make",
            f"CROSS_PREFIX={self.cross_prefix}",
            f"{test_type}",
        ] + extra_make_args

        log.info(dict2str(extra_make_envs) + " ".join(args))

        p = subprocess.run(
            args,
            stdout=subprocess.DEVNULL if not self.verbose else None,
            env=os.environ.copy() | extra_make_envs,
        )

        if p.returncode != 0:
            log.error(f"make failed: {p.returncode}")
            sys.exit(1)

    def run_scheme(
        self,
        test_type: TEST_TYPES,
        scheme: SCHEME,
        opt: bool,
        run_as_root=False,
        exec_wrapper=None,
    ) -> bytes:
        """Run the binary in all different ways"""
        log = logger(test_type, scheme, self.cross_prefix, opt)
        bin = test_type.bin_path(scheme)
        if not os.path.isfile(bin):
            log.error(f"{bin} does not exists")
            sys.exit(1)

        cmd = [f"./{bin}"]
        if self.cross_prefix and platform.system() != "Darwin":
            log.info(f"Emulating {bin} with QEMU")
            if "x86_64" in self.cross_prefix:
                cmd = ["qemu-x86_64"] + cmd
            elif "aarch64" in self.cross_prefix:
                cmd = ["qemu-aarch64"] + cmd
            else:
                log.info(
                    f"Emulation for {self.cross_prefix} on {platform.system()} not supported"
                )

        if run_as_root:
            log.info(
                f"Running {bin} as root -- you may need to enter your root password."
            )
            cmd = ["sudo"] + cmd

        if exec_wrapper:
            log.info(f"Running {bin} with customized wrapper.")
            exec_wrapper = exec_wrapper.split(" ")
            cmd = exec_wrapper + cmd

        log.info(" ".join(cmd))
        result = subprocess.run(
            cmd,
            capture_output=True,
            universal_newlines=False,
        )

        if result.returncode != 0:
            log.error(
                f"Running '{cmd}' failed: {result.returncode} {result.stderr.decode()}"
            )
            sys.exit(1)

        return result.stdout

    def run_schemes(
        self,
        test_type: TEST_TYPES,
        opt: bool,
        run_as_root=False,
        exec_wrapper=None,
        actual_proc: Callable[[bytes], str] = None,
        expect_proc: Callable[[SCHEME], str] = None,
    ) -> TypedDict:
        fail = False
        results = {}
        for scheme in SCHEME:
            log = logger(test_type, scheme, self.cross_prefix, opt)
            result = self.run_scheme(
                test_type,
                scheme,
                opt,
                run_as_root,
                exec_wrapper,
            )

            if actual_proc is not None and expect_proc is not None:
                actual = actual_proc(result)
                expect = expect_proc(scheme)
                f = actual != expect
                fail = fail or f
                if f:
                    log.error(
                        f"{scheme} failed, expecting {expect}, but getting {actual}"
                    )
                else:
                    log.info(f"{scheme} passed")
                results[scheme] = f
            else:
                log.info(f"{scheme}")
                log.info(f"\n{result.decode()}")
                results[scheme] = result.decode()

        title = (
            "## "
            + ("Cross" if self.cross_prefix else "Native")
            + " "
            + ("Opt" if opt else "Non-opt")
            + " Tests"
        )
        github_summary(title, test_type, results)

        if fail:
            sys.exit(1)

        if actual_proc is not None and expect_proc is not None:
            return fail
        else:
            return results

    def test(
        self,
        test_type: TEST_TYPES,
        opt: bool,
        extra_make_envs={},
        extra_make_args=[],
        actual_proc: Callable[[bytes], str] = None,
        expect_proc: Callable[[SCHEME], str] = None,
        run_as_root: bool = False,
        exec_wrapper: str = None,
    ):
        config_logger(self.verbose)

        if self.compile:
            self.compile_schemes(
                test_type,
                opt,
                extra_make_envs,
                extra_make_args,
            )

        results = None
        if self.run:
            results = self.run_schemes(
                test_type,
                opt,
                run_as_root,
                exec_wrapper,
                actual_proc,
                expect_proc,
            )

        return results


"""
Underlying functional tests

"""


class Tests:
    def func(self, state: State, opt: bool):
        """Underlying function for functional test"""

        def expect(scheme: SCHEME) -> str:
            sk_bytes = parse_meta(scheme, "length-secret-key")
            pk_bytes = parse_meta(scheme, "length-public-key")
            ct_bytes = parse_meta(scheme, "length-ciphertext")

            return (
                f"CRYPTO_SECRETKEYBYTES:  {sk_bytes}\n"
                + f"CRYPTO_PUBLICKEYBYTES:  {pk_bytes}\n"
                + f"CRYPTO_CIPHERTEXTBYTES: {ct_bytes}\n"
            )

        state.test(
            TEST_TYPES.MLKEM,
            opt,
            actual_proc=lambda result: str(result, encoding="utf-8"),
            expect_proc=expect,
        )

    def nistkat(self, state: State, opt: bool):
        """Underlying function for nistkat test"""

        state.test(
            TEST_TYPES.NISTKAT,
            opt,
            actual_proc=sha256sum,
            expect_proc=lambda scheme: parse_meta(scheme, "nistkat-sha256"),
        )

    def kat(self, state: State, opt: bool):
        """Underlying function for kat test"""

        state.test(
            TEST_TYPES.KAT,
            opt,
            actual_proc=sha256sum,
            expect_proc=lambda scheme: parse_meta(scheme, "kat-sha256"),
        )

    def bench(
        self,
        state: State,
        opt: bool,
        cycles: str,
        output,
        run_as_root: bool,
        exec_wrapper: str,
        mac_taskpolicy,
        components,
    ):
        config_logger(state.verbose)

        if components is False:
            bench_type = TEST_TYPES.BENCH
        else:
            bench_type = TEST_TYPES.BENCH_COMPONENTS
            output = False

        if mac_taskpolicy:
            if exec_wrapper:
                logging.error(f"cannot set both --mac-taskpolicy and --exec-wrapper")
                sys.exit(1)
            else:
                exec_wrapper = f"taskpolicy -c {mac_taskpolicy}"

        results = state.test(
            bench_type,
            opt,
            extra_make_args=[f"CYCLES={cycles}"],
            run_as_root=run_as_root,
            exec_wrapper=exec_wrapper,
        )

        if results is not None and output is not None and components is False:
            import json

            with open(output, "w") as f:
                v = []
                for scheme in results:
                    schemeStr = str(scheme)
                    r = results[scheme]

                    # The first 3 lines of the output are expected to be
                    # keypair cycles=X
                    # encaps cycles=X
                    # decaps cycles=X

                    lines = [line for line in r.splitlines() if "=" in line]

                    d = {k.strip(): int(v) for k, v in (l.split("=") for l in lines)}
                    for primitive in ["keypair", "encaps", "decaps"]:
                        v.append(
                            {
                                "name": f"{schemeStr} {primitive}",
                                "unit": "cycles",
                                "value": d[f"{primitive} cycles"],
                            }
                        )
                f.write(json.dumps(v))

    def all(self, state: State, opt: str, func: bool, kat: bool, nistkat: bool):
        compile_mode = "cross" if state.cross_prefix else "native"

        gh_env = os.environ.get("GITHUB_ENV")

        tests = [
            *([self.func] if func else []),
            *([self.nistkat] if nistkat else []),
            *([self.kat] if kat else []),
        ]

        exit_code = 0

        if state.compile:
            _state = copy.deepcopy(state)
            _state.run = False

            def _compile(opt: bool):
                opt_label = "opt" if opt else "no-opt"
                for f in tests:
                    if gh_env is not None:
                        print(
                            f"::group::compile {compile_mode} {opt_label} {f.__name__.removeprefix('_')} test"
                        )

                    try:
                        f(_state, opt)
                        print("")
                    except SystemExit as e:
                        exit_code = exit_code or e

                    if gh_env is not None:
                        print(f"::endgroup::")
                    sys.stdout.flush()

            if opt.lower() == "all" or opt.lower() == "no_opt":
                _compile(False)

            if opt.lower() == "all" or opt.lower() == "opt":
                _compile(True)

        if state.run:
            _state = state
            _state.compile = False

            def _run(f, _state: State, opt: bool):
                opt_label = "opt" if opt else "no-opt"
                if gh_env is not None:
                    print(
                        f"::group::run {compile_mode} {opt_label} {f.__name__.removeprefix('_')} test"
                    )

                try:
                    f(_state, opt)
                except SystemExit as e:
                    exit_code = exit_code or e

                if gh_env is not None:
                    print(f"::endgroup::")
                sys.stdout.flush()

            for f in tests:
                if opt.lower() == "all" or opt.lower() == "no_opt":
                    _run(f, _state, False)
                if opt.lower() == "all" or opt.lower() == "opt":
                    _run(f, _state, True)

        exit(exit_code)
