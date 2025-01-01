# Copyright (c) 2024 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

import os
import sys
import subprocess
from functools import reduce
from .util import (
    TEST_TYPES,
    SCHEME,
    config_logger,
    github_summary,
    logger,
    dict2str,
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
        if args.exec_wrapper is not None and args.exec_wrapper != "":
            res += args.exec_wrapper.split(" ")
        if args.mac_taskpolicy is not None:
            res += ["taskpolicy", "-c", f"{mac_taskpolicy}"]

        return res

    @staticmethod
    def make_j(args):
        if args.j is None:
            return []
        return [f"-j{args.j}"]

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

    def compile_schemes(self):
        """compile or cross compile with some extra environment variables and makefile arguments"""

        if gh_env is not None:
            print(
                f"::group::compile {Args.compile_mode(self.args)} {self.opt_label} {self.test_type.desc()}"
            )

        log = logger(self.test_type, "Compile", self.args.cross_prefix, self.opt)

        extra_make_args = [f"OPT={int(self.opt)}", f"AUTO={int(self.args.auto)}"]
        if self.test_type.is_benchmark() is True:
            extra_make_args += [f"CYCLES={self.args.cycles}"]
        extra_make_args += Args.make_j(self.args)

        args = ["make", self.test_type.make_target()] + extra_make_args

        env_update = {}
        if self.args.cflags is not None and self.args.cflags != "":
            env_update["CFLAGS"] = self.args.cflags
        if self.args.cross_prefix is not None and self.args.cross_prefix != "":
            env_update["CROSS_PREFIX"] = self.args.cross_prefix

        env = os.environ.copy()
        env.update(env_update)

        log.info(dict2str(env_update) + " ".join(args))

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
        suppress_output=True,
    ):
        """Run the binary in all different ways

        Arguments:

        - scheme: Scheme to test
        - suppress_output: Indicate whether to suppress or print-and-return the output
        """

        if scheme is None:
            scheme_str = "All"
        else:
            scheme_str = str(scheme)

        log = logger(self.test_type, scheme_str, self.args.cross_prefix, self.opt)

        args = ["make", self.test_type.make_run_target(scheme)] + Args.make_j(self.args)

        env_update = {}
        if len(Args.cmd_prefix(self.args)) > 0:
            env_update["EXEC_WRAPPER"] = " ".join(Args.cmd_prefix(self.args))

        env = os.environ.copy()
        env.update(env_update)

        cmd_str = dict2str(env_update) + " ".join(args)
        log.info(cmd_str)

        p = subprocess.run(args, capture_output=True, universal_newlines=False, env=env)

        result = None

        if p.returncode != 0:
            log.error(f"'{cmd_str}' failed with with {p.returncode}")
            log.error(p.stderr.decode())
        elif suppress_output is True:
            if self.args.verbose is True:
                log.info(p.stdout.decode())
            result = False
        else:
            result = p.stdout.decode()
            log.info(result)

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
    ):
        self.ts["opt" if opt else "no_opt"].compile_schemes()

    def run_scheme(
        self,
        opt,
        scheme,
        suppress_output=True,
    ):
        """Arguments:

        - opt: Whether build should include native backends or not
        - scheme: Scheme to run
        - suppress_output: Indicate whether to suppress or print-and-return the output
        """

        k = "opt" if opt else "no_opt"

        results = {}
        results[k] = {}
        results[k][scheme] = self.ts[k].run_scheme(scheme, suppress_output)

        return results

    def run_schemes(self, opt, suppress_output=True):
        """Arguments:

        - opt: Whether native backends should be enabled
        - suppress_output: Indicate whether to suppress or print-and-return the output
        """

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
                suppress_output,
            )

            results[k][scheme] = result

        title = (
            "## " + (Args.compile_mode(self.args)) + " " + (k.capitalize()) + " Tests"
        )
        github_summary(title, self.test_type.desc(), results[k])

        if gh_env is not None:
            print(f"::endgroup::")

        ## TODO What is happening here?
        if suppress_output is True:
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

    def func(self):
        config_logger(self.args.verbose)

        def _func(opt):
            self._func.compile(opt)
            if self.args.run:
                return self._func.run_schemes(opt)

        fail = False
        if Args.do_no_opt(self.args):
            fail = fail or _func(False)
        if Args.do_opt(self.args):
            fail = fail or _func(True)

        if fail:
            exit(1)

    def nistkat(self):
        config_logger(self.args.verbose)

        def _nistkat(opt):
            self._nistkat.compile(opt)
            if self.args.run:
                return self._nistkat.run_schemes(opt)

        fail = False
        if Args.do_no_opt(self.args):
            fail = fail or _nistkat(False)
        if Args.do_opt(self.args):
            fail = fail or _nistkat(True)

        if fail:
            exit(1)

    def kat(self):
        config_logger(self.args.verbose)

        def _kat(opt):
            self._kat.compile(opt)
            if self.args.run:
                return self._kat.run_schemes(opt)

        fail = False

        if Args.do_no_opt(self.args):
            fail = fail or _kat(False)
        if Args.do_opt(self.args):
            fail = fail or _kat(True)

        if fail:
            exit(1)

    def acvp(self):
        config_logger(self.args.verbose)

        def _acvp(opt):
            self._acvp.compile(opt)
            if self.args.run:
                return self._acvp.run_scheme(opt, None)

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
        return t.run_schemes(opt, suppress_output=False)

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
            t.compile(False)
            if self.args.run:
                self._run_bench(t, False)
            t.compile(True)
            if self.args.run:
                resultss = self._run_bench(t, True)
        else:
            t.compile(
                Args.do_opt(self.args),
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
                    *([self._func.run_schemes] if func else []),
                    *([self._nistkat.run_schemes] if nistkat else []),
                    *([self._kat.run_schemes] if kat else []),
                    *([self._acvp.run_schemes] if acvp else []),
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
            p = subprocess.Popen(
                [
                    "python3",
                    "run-cbmc-proofs.py",
                    "--summarize",
                    "--no-coverage",
                ]
                + Args.make_j(self.args),
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
