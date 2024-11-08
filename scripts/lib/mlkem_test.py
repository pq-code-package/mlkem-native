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

gh_env = os.environ.get("GITHUB_ENV")


class CompileOptions(object):

    def __init__(
        self, cross_prefix: str, cflags: str, arch_flags: str, auto: bool, verbose: bool
    ):
        self.cross_prefix = cross_prefix
        self.cflags = cflags
        self.arch_flags = arch_flags
        self.auto = auto
        self.verbose = verbose


class Options(object):
    def __init__(self):
        self.cross_prefix = ""
        self.cflags = ""
        self.arch_flags = ""
        self.auto = True
        self.verbose = False
        self.opt = "ALL"
        self.compile = True
        self.run = True


class Base:

    def __init__(self, test_type: TEST_TYPES, copts: CompileOptions, opt: bool):
        self.test_type = test_type
        self.cross_prefix = copts.cross_prefix
        self.cflags = copts.cflags
        self.arch_flags = copts.arch_flags
        self.auto = copts.auto
        self.verbose = copts.verbose
        self.opt = opt
        self.compile_mode = "Cross" if self.cross_prefix else "Native"
        self.opt_label = "opt" if self.opt else "no_opt"

    def compile_schemes(
        self,
        extra_make_envs={},
        extra_make_args=[],
    ):
        """compile or cross compile with some extra environment variables and makefile arguments"""

        if gh_env is not None:
            print(
                f"::group::compile {self.compile_mode} {self.opt_label} {self.test_type.desc()}"
            )

        log = logger(self.test_type, "Compile", self.cross_prefix, self.opt)

        def dict2str(dict):
            s = ""
            for k, v in dict.items():
                s += f"{k}={v} "
            return s

        extra_make_args = extra_make_args + list(
            set([f"OPT={int(self.opt)}", f"AUTO={int(self.auto)}"])
            - set(extra_make_args)
        )

        args = [
            "make",
            f"CROSS_PREFIX={self.cross_prefix}",
            f"{self.test_type}",
        ] + extra_make_args

        make_envs = (
            {"CFLAGS": f"{self.cflags}"} if self.cflags is not None else {}
        ) | (
            {"ARCH_FLAGS": f"{self.arch_flags}"} if self.arch_flags is not None else {}
        )
        extra_make_envs.update(make_envs)

        log.info(dict2str(extra_make_envs) + " ".join(args))

        p = subprocess.run(
            args,
            stdout=subprocess.DEVNULL if not self.verbose else None,
            env=os.environ.copy() | extra_make_envs,
        )

        if p.returncode != 0:
            log.error(f"make failed: {p.returncode}")

        if gh_env is not None:
            print(f"::endgroup::")

        if p.returncode != 0:
            sys.exit(1)

    def run_scheme(
        self,
        scheme: SCHEME,
        actual_proc: Callable[[bytes], str] = None,
        expect_proc: Callable[[SCHEME], str] = None,
        run_as_root=False,
        exec_wrapper=None,
    ):
        """Run the binary in all different ways"""
        log = logger(self.test_type, scheme, self.cross_prefix, self.opt)

        bin = self.test_type.bin_path(scheme)
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
                    f"Emulation for {self.cross_prefix} on {platform.system()} not supported",
                )

        if run_as_root:
            log.info(
                f"Running {bin} as root -- you may need to enter your root password.",
            )
            cmd = ["sudo"] + cmd

        if exec_wrapper:
            log.info(f"Running {bin} with customized wrapper.")
            exec_wrapper = exec_wrapper.split(" ")
            cmd = exec_wrapper + cmd

        log.debug(" ".join(cmd))

        p = subprocess.run(
            cmd,
            capture_output=True,
            universal_newlines=False,
        )

        result = None

        if p.returncode != 0:
            log.error(
                f"Running '{cmd}' failed: {p.returncode} {p.stderr.decode()}",
            )
        elif actual_proc is not None and expect_proc is not None:
            actual = actual_proc(p.stdout)
            expect = expect_proc(scheme)
            result = actual != expect
            if result:
                log.error(f"failed, expecting {expect}, but getting {actual}")
            else:
                log.info(f"passed")
        else:
            log.info(f"{p.stdout.decode()}")
            result = p.stdout.decode()

        if p.returncode != 0:
            exit(p.returncode)
        else:
            return result


class Test_Implementations:
    def __init__(self, test_type: TEST_TYPES, copts: CompileOptions):
        self.test_type = test_type
        self.ts = {}
        self.ts["opt"] = Base(test_type, copts, True)
        self.ts["no_opt"] = Base(test_type, copts, False)

    def compile(
        self,
        opt: bool,
        extra_make_envs={},
        extra_make_args=[],
    ):
        self.ts["opt" if opt else "no_opt"].compile_schemes(
            extra_make_envs,
            extra_make_args,
        )

    def run_schemes(
        self,
        opt: bool,
        actual_proc: Callable[[bytes], str] = None,
        expect_proc: Callable[[SCHEME], str] = None,
        run_as_root=False,
        exec_wrapper=None,
    ) -> TypedDict:
        results = {}

        k = "opt" if opt else "no_opt"

        if gh_env is not None:
            print(f"::group::run {self.ts[k].compile_mode} {k} {self.test_type.desc()}")

        results[k] = {}
        for scheme in SCHEME:
            result = self.ts[k].run_scheme(
                scheme,
                actual_proc,
                expect_proc,
                run_as_root,
                exec_wrapper,
            )

            results[k][scheme] = result

        title = "## " + (self.ts[k].compile_mode) + " " + (k.capitalize()) + " Tests"
        github_summary(title, self.test_type, results[k])

        if gh_env is not None:
            print(f"::endgroup::")

        if actual_proc is not None and expect_proc is not None:
            return reduce(
                lambda acc, c: acc or c,
                [r for rs in results.values() for r in rs.values()],
                False,
            )
        else:
            return results


"""
Underlying functional tests

"""


class Tests:
    def __init__(self, opts: Options):
        copts = CompileOptions(
            opts.cross_prefix, opts.cflags, opts.arch_flags, opts.auto, opts.verbose
        )
        self.opt = opts.opt

        self.verbose = opts.verbose
        self._func = Test_Implementations(TEST_TYPES.MLKEM, copts)
        self._nistkat = Test_Implementations(TEST_TYPES.NISTKAT, copts)
        self._kat = Test_Implementations(TEST_TYPES.KAT, copts)
        self._bench = Test_Implementations(TEST_TYPES.BENCH, copts)
        self._bench_components = Test_Implementations(
            TEST_TYPES.BENCH_COMPONENTS, copts
        )

        self.compile_mode = "Cross" if opts.cross_prefix else "Native"
        self.compile = opts.compile
        self.run = opts.run

    def _run_func(self, opt: bool):
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

        return self._func.run_schemes(
            opt,
            actual_proc=lambda result: str(result, encoding="utf-8"),
            expect_proc=expect,
        )

    def func(self):
        config_logger(self.verbose)

        def _func(opt: bool):

            if self.compile:
                self._func.compile(opt)
            if self.run:
                return self._run_func(opt)

        fail = False
        if self.opt.lower() == "all" or self.opt.lower() == "no_opt":
            fail = fail or _func(False)
        if self.opt.lower() == "all" or self.opt.lower() == "opt":
            fail = fail or _func(True)

        if fail:
            exit(1)

    def _run_nistkat(self, opt: bool):
        return self._nistkat.run_schemes(
            opt,
            actual_proc=sha256sum,
            expect_proc=lambda scheme: parse_meta(scheme, "nistkat-sha256"),
        )

    def nistkat(self):
        config_logger(self.verbose)

        def _nistkat(opt: bool):
            if self.compile:
                self._nistkat.compile(opt)
            if self.run:
                return self._run_nistkat(opt)

        fail = False
        if self.opt.lower() == "all" or self.opt.lower() == "no_opt":
            fail = fail or _nistkat(False)
        if self.opt.lower() == "all" or self.opt.lower() == "opt":
            fail = fail or _nistkat(True)

        if fail:
            exit(1)

    def _run_kat(self, opt: bool):
        return self._kat.run_schemes(
            opt,
            actual_proc=sha256sum,
            expect_proc=lambda scheme: parse_meta(scheme, "kat-sha256"),
        )

    def kat(self):
        config_logger(self.verbose)

        def _kat(opt: bool):
            if self.compile:
                self._kat.compile(opt)
            if self.run:
                return self._run_kat(opt)

        fail = False

        if self.opt.lower() == "all" or self.opt.lower() == "no_opt":
            fail = fail or _kat(False)
        if self.opt.lower() == "all" or self.opt.lower() == "opt":
            fail = fail or _kat(True)

        if fail:
            exit(1)

    def _run_bench(
        self, t: Test_Implementations, opt: bool, run_as_root: bool, exec_wrapper: str
    ) -> TypedDict:
        return t.run_schemes(
            opt,
            run_as_root=run_as_root,
            exec_wrapper=exec_wrapper,
        )

    def bench(
        self,
        cycles: str,
        output,
        run_as_root: bool,
        exec_wrapper: str,
        mac_taskpolicy,
        components,
    ):
        config_logger(self.verbose)

        if components is False:
            t = self._bench
        else:
            t = self._bench_components
            output = False

        if mac_taskpolicy:
            if exec_wrapper:
                logging.error(f"cannot set both --mac-taskpolicy and --exec-wrapper")
                sys.exit(1)
            else:
                exec_wrapper = f"taskpolicy -c {mac_taskpolicy}"

        if self.compile:
            t.compile(self.opt, extra_make_args=[f"CYCLES={cycles}"])

        if self.run:
            if self.opt.lower() == "all":
                # NOTE: We haven't yet decided how to output both opt/no-opt benchmark results
                self._run_bench(t, False, run_as_root, exec_wrapper)
                resultss = self._run_bench(t, True, run_as_root, exec_wrapper)
            else:
                resultss = self._run_bench(
                    t,
                    True if self.opt.lower() == "opt" else False,
                    run_as_root,
                    exec_wrapper,
                )

        if resultss is None:
            exit(0)

        # NOTE: There will only be one items in resultss, as we haven't yet decided how to write both opt/no-opt benchmark results
        for k, results in resultss.items():
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

                        d = {
                            k.strip(): int(v) for k, v in (l.split("=") for l in lines)
                        }
                        for primitive in ["keypair", "encaps", "decaps"]:
                            v.append(
                                {
                                    "name": f"{schemeStr} {primitive}",
                                    "unit": "cycles",
                                    "value": d[f"{primitive} cycles"],
                                }
                            )
                    f.write(json.dumps(v))

    def all(self, func: bool, kat: bool, nistkat: bool):
        config_logger(self.verbose)

        exit_code = 0

        def all(opt: bool):
            if self.compile:
                compiles = [
                    *([self._func.compile] if func else []),
                    *([self._nistkat.compile] if nistkat else []),
                    *([self._kat.compile] if kat else []),
                ]

                for f in compiles:
                    try:
                        f(opt)
                    except SystemExit as e:
                        exit_code = exit_code or e

                    sys.stdout.flush()

            if self.run:
                runs = [
                    *([self._run_func] if func else []),
                    *([self._run_nistkat] if nistkat else []),
                    *([self._run_kat] if kat else []),
                ]

                for f in runs:
                    try:
                        f(opt)
                    except SystemExit as e:
                        exit_code = exit_code or e

                    sys.stdout.flush()

        if self.opt.lower() == "all" or self.opt.lower() == "no_opt":
            all(False)
        if self.opt.lower() == "all" or self.opt.lower() == "opt":
            all(True)

        exit(exit_code)
