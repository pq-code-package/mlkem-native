# SPDX-License-Identifier: Apache-2.0

import os
import sys
import io
import logging
import subprocess
import json
from functools import reduce, partial
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
        self.i = 0  # counter for ACVP test

    def compile_schemes(
        self,
        extra_make_envs={},
        extra_make_args=[],
    ):
        """compile or cross compile with some extra environment variables and makefile arguments"""

        if gh_env is not None:
            compile_mode = "Cross" if self.cross_prefix else "Native"
            print(f"::group::compile {compile_mode} {self.opt} {self.test_type.desc()}")

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
        expect_proc: Callable[[SCHEME, str], tuple[bool, str]] = None,
        prefix: [str] = [],
        extra_args: [str] = [],
    ):
        """Run the binary in all different ways"""
        log = logger(self.test_type, scheme, self.cross_prefix, self.opt, self.i)
        self.i += 1

        bin = self.test_type.bin_path(scheme, self.opt)
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

        cmd = prefix + cmd + extra_args

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
            result, err = expect_proc(scheme, actual)
            if result:
                log.error(f"{err}")
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
    def __init__(
        self,
        test_type: TEST_TYPES,
        copts: CompileOptions,
    ):
        self.compile_mode = "Cross" if copts.cross_prefix else "Native"
        self.test_type = test_type
        self.ts = {}
        self.ts["no_opt"] = Base(test_type, copts, False)
        self.ts["opt"] = Base(test_type, copts, True)

    def compile(
        self,
        opt: str,
        extra_make_envs={},
        extra_make_args=[],
    ):
        if opt.lower() == "all" or opt.lower() == "no_opt":
            self.ts["no_opt"].compile_schemes(
                extra_make_envs,
                extra_make_args,
            )
        if opt.lower() == "all" or opt.lower() == "opt":
            self.ts["opt"].compile_schemes(
                extra_make_envs,
                extra_make_args,
            )

    def run_scheme(
        self,
        opt: str,
        scheme: SCHEME,
        actual_proc: Callable[[bytes], str] = None,
        expect_proc: Callable[[SCHEME, str], tuple[bool, str]] = None,
        prefix: [str] = [],
        extra_args: [str] = [],
    ) -> TypedDict:
        results = {}
        if opt.lower() == "all":
            results["no_opt"] = {}
            results["no_opt"][scheme] = self.ts["no_opt"].run_scheme(
                scheme, actual_proc, expect_proc, prefix, extra_args
            )
            results["opt"] = {}
            results["opt"][scheme] = self.ts["opt"].run_scheme(
                scheme, actual_proc, expect_proc, prefix, extra_args
            )
        else:
            results[opt.lower()] = {}
            results[opt.lower()][scheme] = self.ts[opt.lower()].run_scheme(
                scheme, actual_proc, expect_proc, prefix, extra_args
            )
        return results

    def run_schemes(
        self,
        opt: str,
        actual_proc: Callable[[bytes], str] = None,
        expect_proc: Callable[[SCHEME, str], tuple[bool, str]] = None,
        prefix: [str] = [],
        extra_args: [str] = [],
    ) -> TypedDict:
        results = {}

        def run(opt: bool):
            k = "opt" if opt else "no_opt"
            results[k] = {}
            for scheme in SCHEME:
                result = self.ts[k].run_scheme(
                    scheme, actual_proc, expect_proc, prefix, extra_args
                )

                results[k][scheme] = result

            title = "## " + (self.compile_mode) + " " + (k.capitalize()) + " Tests"
            github_summary(title, self.test_type.desc(), results[k])

        if opt.lower() == "all" or opt.lower() == "no_opt":
            run(False)
        if opt.lower() == "all" or opt.lower() == "opt":
            run(True)

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
        self._acvp = Test_Implementations(TEST_TYPES.ACVP, copts)
        self._bench = Test_Implementations(TEST_TYPES.BENCH, copts)
        self._bench_components = Test_Implementations(
            TEST_TYPES.BENCH_COMPONENTS, copts
        )

        self.compile = opts.compile
        self.run = opts.run

    def _run_func(self):
        """Underlying function for functional test"""

        def expect(scheme: SCHEME, actual: str) -> tuple[bool, str]:
            sk_bytes = parse_meta(scheme, "length-secret-key")
            pk_bytes = parse_meta(scheme, "length-public-key")
            ct_bytes = parse_meta(scheme, "length-ciphertext")

            expect = (
                f"CRYPTO_SECRETKEYBYTES:  {sk_bytes}\n"
                + f"CRYPTO_PUBLICKEYBYTES:  {pk_bytes}\n"
                + f"CRYPTO_CIPHERTEXTBYTES: {ct_bytes}\n"
            )

            fail = expect != actual
            return (
                fail,
                "Failed, expecting {expect}, but getting {actual}" if fail else "",
            )

        return self._func.run_schemes(
            self.opt,
            actual_proc=lambda result: str(result, encoding="utf-8"),
            expect_proc=expect,
        )

    def func(self):
        config_logger(self.verbose)

        if self.compile:
            self._func.compile(self.opt)
        if self.run:
            fail = self._run_func()
            if fail:
                exit(1)

    def _run_nistkat(self):
        def expect_proc(scheme: SCHEME, actual: str) -> tuple[bool, str]:
            expect = parse_meta(scheme, "nistkat-sha256")
            fail = expect != actual

            return (
                fail,
                f"Failed, expect {expet} but getting {actual}" if fail else "",
            )

        return self._nistkat.run_schemes(
            self.opt,
            actual_proc=sha256sum,
            expect_proc=expect_proc,
        )

    def nistkat(self):
        config_logger(self.verbose)

        if self.compile:
            self._nistkat.compile(self.opt)
        if self.run:
            fail = self._run_nistkat()
            if fail:
                exit(1)

    def _run_kat(self):
        def expect_proc(scheme: SCHEME, actual: str) -> tuple[bool, str]:
            expect = parse_meta(scheme, "kat-sha256")
            fail = expect != actual

            return (
                fail,
                f"Failed, expect {expet} but getting {actual}" if fail else "",
            )

        return self._kat.run_schemes(
            self.opt,
            actual_proc=sha256sum,
            expect_proc=expect_proc,
        )

    def kat(self):
        config_logger(self.verbose)

        if self.compile:
            self._kat.compile(self.opt)
        if self.run:
            fail = self._run_kat()
            if fail:
                exit(1)

    def _run_acvp(self, acvp_dir: str = "test/acvp_data"):
        acvp_keygen_json = f"{acvp_dir}/acvp_keygen_internalProjection.json"
        acvp_encapDecap_json = f"{acvp_dir}/acvp_encapDecap_internalProjection.json"

        with open(acvp_keygen_json, "r") as f:
            acvp_keygen_data = json.load(f)

        with open(acvp_encapDecap_json, "r") as f:
            acvp_encapDecap_data = json.load(f)

        def actual_proc(bs: bytes) -> str:
            return bs.decode("utf-8")

        def _expect_proc(
            tc: TypedDict, scheme: SCHEME, actual: str
        ) -> tuple[bool, str]:
            fail = False
            err = ""
            for l in actual.splitlines():
                (k, v) = l.split("=")
                if v != tc[k]:
                    fail = True
                    err = (
                        err
                        + f"Failed, Mismatching result for {k}: expect {tc[k]}, but got {v}\n"
                    )
            return (fail, err)

        def init_results() -> TypedDict:
            results = {}
            if self.opt.lower() == "all":
                results["no_opt"] = {}
                for s in SCHEME:
                    results["no_opt"][s] = False
                results["opt"] = {}
                for s in SCHEME:
                    results["opt"][s] = False
            else:
                results[self.opt.lower()] = {}
                for s in SCHEME:
                    results[self.opt.lower()][s] = False
            return results

        results = init_results()
        # encapDecap
        for i, tg in enumerate(acvp_encapDecap_data["testGroups"]):
            scheme = SCHEME.from_str(tg["parameterSet"])

            for tc in tg["tests"]:
                if tg["function"] == "encapsulation":
                    extra_args = [
                        "encapDecap",
                        "AFT",
                        "encapsulation",
                        f"ek={tc['ek']}",
                        f"m={tc['m']}",
                    ]

                elif tg["function"] == "decapsulation":
                    extra_args = [
                        "encapDecap",
                        "VAL",
                        "decapsulation",
                        f"dk={tg['dk']}",
                        f"c={tc['c']}",
                    ]

                rs = self._acvp.run_scheme(
                    self.opt,
                    scheme,
                    extra_args=extra_args,
                    actual_proc=actual_proc,
                    expect_proc=partial(_expect_proc, tc),
                )
                for k, r in rs.items():
                    results[k][scheme] = results[k][scheme] or r[scheme]

        for k, result in results.items():
            title = (
                "## " + (self._acvp.compile_mode) + " " + (k.capitalize()) + " Tests"
            )
            github_summary(title, f"{TEST_TYPES.ACVP.desc()} encapDecap", result)

        results = init_results()

        for i, tg in enumerate(acvp_keygen_data["testGroups"]):
            scheme = SCHEME.from_str(tg["parameterSet"])

            for tc in tg["tests"]:
                extra_args = [
                    "keyGen",
                    "AFT",
                    f"z={tc['z']}",
                    f"d={tc['d']}",
                ]

                rs = self._acvp.run_scheme(
                    self.opt,
                    scheme,
                    extra_args=extra_args,
                    actual_proc=actual_proc,
                    expect_proc=partial(_expect_proc, tc),
                )
                for k, r in rs.items():
                    results[k][scheme] = results[k][scheme] or r[scheme]

        for k, result in results.items():
            title = (
                "## " + (self._acvp.compile_mode) + " " + (k.capitalize()) + " Tests"
            )
            github_summary(title, f"{TEST_TYPES.ACVP.desc()} keyGen", result)

    def acvp(self, acvp_dir: str):
        config_logger(self.verbose)

        if self.compile:
            self._acvp.compile(self.opt)
        if self.run:
            self._run_acvp(acvp_dir)

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

        prefix = []
        if run_as_root:
            logging.info(
                f"Running {bin} as root -- you may need to enter your root password.",
            )
            prefix.append("sudo")

        if exec_wrapper:
            logging.info(f"Running with customized wrapper.")
            exec_wrapper = exec_wrapper.split(" ")
            prefix = prefix + exec_wrapper

        if self.run:
            resultss = t.run_schemes(
                self.opt,
                prefix=prefix,
            )

        if resultss is None:
            exit(0)

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

    def all(self, func: bool, kat: bool, nistkat: bool, acvp: bool):
        config_logger(self.verbose)

        exit_code = 0

        if self.compile:
            compiles = [
                *([self._func.compile] if func else []),
                *([self._nistkat.compile] if nistkat else []),
                *([self._kat.compile] if kat else []),
                *([self._acvp.compile] if acvp else []),
            ]

            def _compile(opt: str):
                for f in compiles:
                    if gh_env is not None:
                        print(
                            f"::group::compile {compile_mode} {opt_label} {f.__name__.removeprefix('_')} test"
                        )
                    try:
                        f(opt)
                    except SystemExit as e:
                        exit_code = exit_code or e

                    if gh_env is not None:
                        print("::endgroup::")
                    sys.stdout.flush()

            if self.opt.lower() == "all":
                _compile("no_opt")
                _compile("opt")
            else:
                _compile(self.opt)

        if self.run:
            runs = [
                *([self._run_func] if func else []),
                *([self._run_nistkat] if nistkat else []),
                *([self._run_kat] if kat else []),
                *([self._run_acvp] if acvp else []),
            ]

            for f in runs:
                if gh_env is not None:
                    print(
                        f"::group::run {compile_mode} {self.opt} {f.__name__.removeprefix('_')} test"
                    )

                try:
                    f()
                except SystemExit as e:
                    exit_code = exit_code or e

                if gh_env is not None:
                    print(f"::endgroup::")
                sys.stdout.flush()

        exit(exit_code)
