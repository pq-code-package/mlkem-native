# Copyright (c) 2024 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

import platform
import os
import sys
import io
import logging
import subprocess
from functools import reduce, partial
from util import (
    TEST_TYPES,
    SCHEME,
    sha256sum,
    parse_meta,
    config_logger,
    github_summary,
    logger,
)
import json

gh_env = os.environ.get("GITHUB_ENV")


class Args:
    """Helper functions for working with command line parameters"""

    @staticmethod
    def cmd_prefix(args):
        res = []
        if args.run_as_root is True:
            res += ["sudo"]
        if args.exec_wrapper is not None:
            res += args.exec_wrapper.split(" ")
        if args.mac_taskpolicy is not None:
            res += ["taskpolicy", "-c", f"{mac_taskpolicy}"]

        return res

    @staticmethod
    def do_opt_all(args):
        return args.opt.lower() == ["all"]

    @staticmethod
    def do_opt(args):
        return args.opt.lower() in ["all", "opt"]

    @staticmethod
    def do_no_opt(args):
        return args.opt.lower() in ["all", "no_opt"]

    @staticmethod
    def compile_mode(args):
        return "Cross" if args.cross_prefix is not None else "Native"


class Base:

    def __init__(self, test_type: TEST_TYPES, args, opt):
        self.args = args
        self.test_type = test_type
        self.opt = opt
        self.opt_label = "opt" if self.opt else "no_opt"
        self.i = 0

    def compile_schemes(
        self,
        extra_make_envs=None,
        extra_make_args=None,
    ):
        """compile or cross compile with some extra environment variables and makefile arguments"""
        if extra_make_envs is None:
            extra_make_envs = {}
        if extra_make_args is None:
            extra_make_args = []

        if gh_env is not None:
            print(
                f"::group::compile {Args.compile_mode(self.args)} {self.opt_label} {self.test_type.desc()}"
            )

        log = logger(self.test_type, "Compile", self.args.cross_prefix, self.opt)

        def dict2str(dict):
            s = ""
            for k, v in dict.items():
                s += f"{k}={v} "
            return s

        extra_make_args = extra_make_args + list(
            set([f"OPT={int(self.opt)}", f"AUTO={int(self.args.auto)}"])
            - set(extra_make_args)
        )

        args = [
            "make",
            f"CROSS_PREFIX={self.args.cross_prefix}",
            f"{self.test_type.make_target()}",
        ] + extra_make_args

        env = os.environ.copy()
        if self.args.cflags is not None:
            env["CFLAGS"] = self.args.cflags

        env.update(extra_make_envs)

        log.info(dict2str(extra_make_envs) + " ".join(args))

        p = subprocess.run(
            args,
            stdout=subprocess.DEVNULL if not self.args.verbose else None,
            env=env,
        )

        if p.returncode != 0:
            log.error(f"make failed: {p.returncode}")

        if gh_env is not None:
            print(f"::endgroup::")

        if p.returncode != 0:
            sys.exit(1)

    def run_scheme(
        self,
        scheme,
        check_proc=None,
    ):
        """Run the binary in all different ways

        Arguments:

        - scheme: Scheme to test
        - check_proc: Callable to process and check the raw byte-output
            of the test run with.
        """

        log = logger(self.test_type, scheme, self.args.cross_prefix, self.opt, self.i)
        self.i += 1

        bin = self.test_type.bin_path(scheme)
        if not os.path.isfile(bin):
            log.error(f"{bin} does not exists")
            sys.exit(1)

        cmd = Args.cmd_prefix(self.args) + [f"{bin}"]

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
        elif check_proc is not None:
            result, err = check_proc(scheme, p.stdout)
            if result:
                log.error(f"{err}")
            else:
                log.info(f"passed")
        else:
            log.info(f"\n{p.stdout.decode()}")
            result = p.stdout.decode()

        if p.returncode != 0:
            exit(p.returncode)
        else:
            return result


class Test_Implementations:
    def __init__(self, test_type: TEST_TYPES, args):
        self.args = args
        self.test_type = test_type
        self.ts = {}
        self.ts["opt"] = Base(test_type, args, True)
        self.ts["no_opt"] = Base(test_type, args, False)

    def compile(
        self,
        opt,
        extra_make_envs=None,
        extra_make_args=None,
    ):
        self.ts["opt" if opt else "no_opt"].compile_schemes(
            extra_make_envs,
            extra_make_args,
        )

    def run_scheme(
        self,
        opt,
        scheme,
        check_proc=None,
    ):
        """Arguments:

        - opt: Whether build should include native backends or not
        - scheme: Scheme to run
        - check_proc: Callable to process and check the
            raw byte-output of the test run with.
        """

        # Returns TypedDict
        k = "opt" if opt else "no_opt"

        results = {}
        results[k] = {}
        results[k][scheme] = self.ts[k].run_scheme(scheme, check_proc)

        return results

    def run_schemes(self, opt, check_proc=None):
        """Arguments:

        - opt: Whether native backends should be enabled
        - check_proc: Functionto process and check the raw byte-output
                      of the test run with.
        """

        # Returns
        results = {}

        k = "opt" if opt else "no_opt"

        if gh_env is not None:
            print(
                f"::group::run {Args.compile_mode(self.args)} {k} {self.test_type.desc()}"
            )

        results[k] = {}
        for scheme in SCHEME:
            result = self.ts[k].run_scheme(
                scheme,
                check_proc,
            )

            results[k][scheme] = result

        title = (
            "## " + (Args.compile_mode(self.args)) + " " + (k.capitalize()) + " Tests"
        )
        github_summary(title, self.test_type.desc(), results[k])

        if gh_env is not None:
            print(f"::endgroup::")

        ## TODO What is happening here?
        if check_proc is not None:
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
    def __init__(self, args):
        self.args = args

        self._func = Test_Implementations(TEST_TYPES.MLKEM, args)
        self._nistkat = Test_Implementations(TEST_TYPES.NISTKAT, args)
        self._kat = Test_Implementations(TEST_TYPES.KAT, args)
        self._acvp = Test_Implementations(TEST_TYPES.ACVP, args)
        self._bench = Test_Implementations(TEST_TYPES.BENCH, args)
        self._bench_components = Test_Implementations(TEST_TYPES.BENCH_COMPONENTS, args)

    def _run_func(self, opt):
        """Underlying function for functional test"""

        def expect(scheme, raw):
            """Checks whether the hashed output of the scheme matches the META.yml"""

            actual = str(raw, encoding="utf-8")

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
                f"Failed, expecting {expect}, but getting {actual}" if fail else "",
            )

        return self._func.run_schemes(
            opt,
            check_proc=expect,
        )

    def func(self):
        config_logger(self.args.verbose)

        def _func(opt):

            if self.args.compile:
                self._func.compile(opt)
            if self.args.run:
                return self._run_func(opt)

        fail = False
        if Args.do_no_opt(self.args):
            fail = fail or _func(False)
        if Args.do_opt(self.args):
            fail = fail or _func(True)

        if fail:
            exit(1)

    def _run_nistkat(self, opt):
        def check_proc(scheme, raw):
            """Checks whether the hashed output of the scheme matches the META.yml"""

            actual = sha256sum(raw)
            expect = parse_meta(scheme, "nistkat-sha256")
            fail = expect != actual

            return (
                fail,
                f"Failed, expecting {expect}, but getting {actual}" if fail else "",
            )

        return self._nistkat.run_schemes(
            opt,
            check_proc=check_proc,
        )

    def nistkat(self):
        config_logger(self.args.verbose)

        def _nistkat(opt):
            if self.args.compile:
                self._nistkat.compile(opt)
            if self.args.run:
                return self._run_nistkat(opt)

        fail = False
        if Args.do_no_opt(self.args):
            fail = fail or _nistkat(False)
        if Args.do_opt(self.args):
            fail = fail or _nistkat(True)

        if fail:
            exit(1)

    def _run_kat(self, opt):
        def check_proc(scheme, raw):
            """Checks whether the hashed output of the scheme matches the META.yml"""
            actual = sha256sum(raw)
            expect = parse_meta(scheme, "kat-sha256")
            fail = expect != actual

            return (
                fail,
                f"Failed, expecting {expect}, but getting {actual}" if fail else "",
            )

        return self._kat.run_schemes(
            opt,
            check_proc=check_proc,
        )

    def kat(self):
        config_logger(self.args.verbose)

        def _kat(opt):
            if self.args.compile:
                self._kat.compile(opt)
            if self.args.run:
                return self._run_kat(opt)

        fail = False

        if Args.do_no_opt(self.args):
            fail = fail or _kat(False)
        if Args.do_opt(self.args):
            fail = fail or _kat(True)

        if fail:
            exit(1)

    def _run_acvp(self, opt):

        opt_label = "opt" if opt else "no_opt"
        log = logger(
            TEST_TYPES.ACVP, "Run", self._acvp.ts[opt_label].args.cross_prefix, opt
        )

        if gh_env is not None:
            print(
                f"::group::run {Args.compile_mode(self.args)} {opt_label} {TEST_TYPES.ACVP.desc()}"
            )

        env_update = {"EXEC_WRAPPER": " ".join(Args.cmd_prefix(self.args))}
        env = os.environ.copy()
        env.update(env_update)

        def dict2str(dict):
            s = ""
            for k, v in dict.items():
                s += f"{k}={v} "
            return s

        args = ["make", "run_acvp"]
        log.info(dict2str(env_update) + " ".join(args))

        p = subprocess.run(
            args,
            capture_output=True,
            universal_newlines=False,
            env=env,
        )
        fail = p.returncode != 0
        if fail is True:
            log.error(p.stderr.decode())
            log.error(f"ACVP test failed: {p.returncode}")

        results = {}
        results[opt_label] = {}
        for s in SCHEME:
            results[opt_label][s] = fail

        if gh_env is not None:
            print(f"::endgroup::")

        for k, result in results.items():
            title = (
                "## "
                + (Args.compile_mode(self.args))
                + " "
                + (k.capitalize())
                + " Tests"
            )
            github_summary(title, f"{TEST_TYPES.ACVP.desc()}", result)

        return fail

    def acvp(self):
        acvp_dir = self.args.acvp_dir
        config_logger(self.args.verbose)

        def _acvp(opt):
            if self.args.compile:
                self._acvp.compile(opt)
            if self.args.run:
                return self._run_acvp(opt)

        fail = False

        if Args.do_no_opt(self.args):
            fail = fail or _acvp(False)
        if Args.do_opt(self.args):
            fail = fail or _acvp(True)

        if fail:
            exit(1)

    def _run_bench(
        self,
        t,  # Testmplementations
        opt,
    ):
        return t.run_schemes(opt)

    def bench(self):
        cycles = self.args.cycles
        output = self.args.output
        components = self.args.components

        config_logger(self.args.verbose)

        if components is False:
            t = self._bench
        else:
            t = self._bench_components
            output = False

        # NOTE: We haven't yet decided how to output both opt/no-opt benchmark results
        if Args.do_opt_all(self.args):
            if self.args.compile:
                t.compile(False, extra_make_args=[f"CYCLES={cycles}"])
            if self.args.run:
                self._run_bench(t, False)
            if self.args.compile:
                t.compile(True, extra_make_args=[f"CYCLES={cycles}"])
            if self.args.run:
                resultss = self._run_bench(t, True)
        else:
            if self.args.compile:
                t.compile(
                    Args.do_opt(self.args),
                    extra_make_args=[f"CYCLES={cycles}"],
                )
            if self.args.run:
                resultss = self._run_bench(
                    t,
                    Args.do_opt(self.args),
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

    def all(self):
        func = self.args.func
        kat = self.args.kat
        nistkat = self.args.nistkat
        acvp = self.args.acvp

        config_logger(self.args.verbose)

        def all(opt):
            code = 0
            if self.args.compile:
                compiles = [
                    *([self._func.compile] if func else []),
                    *([self._nistkat.compile] if nistkat else []),
                    *([self._kat.compile] if kat else []),
                    *([self._acvp.compile] if acvp else []),
                ]

                for f in compiles:
                    try:
                        f(opt)
                    except SystemExit as e:
                        code = code or e

                    sys.stdout.flush()

            if self.args.run:
                runs = [
                    *([self._run_func] if func else []),
                    *([self._run_nistkat] if nistkat else []),
                    *([self._run_kat] if kat else []),
                    *([self._run_acvp] if acvp else []),
                ]

                for f in runs:
                    try:
                        code = code or int(f(opt))
                    except SystemExit as e:
                        code = code or e

                    sys.stdout.flush()
            return code

        exit_code = 0

        if Args.do_no_opt(self.args):
            exit_code = exit_code or all(False)
        if Args.do_opt(self.args):
            exit_code = exit_code or all(True)

        exit(exit_code)

    def cbmc(self):
        config_logger(self.args.verbose)

        def run_cbmc(mlkem_k):
            envvars = {"MLKEM_K": mlkem_k}
            cpucount = os.cpu_count()
            p = subprocess.Popen(
                [
                    "python3",
                    "run-cbmc-proofs.py",
                    "--summarize",
                    "--no-coverage",
                    f"-j{cpucount}",
                ],
                cwd="cbmc",
                env=os.environ.copy() | envvars,
            )
            p.communicate()
            assert p.returncode == 0

        k = self.args.k
        if k == "ALL":
            run_cbmc("2")
            run_cbmc("3")
            run_cbmc("4")
        else:
            run_cbmc(k)
