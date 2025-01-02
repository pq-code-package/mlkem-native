# Copyright (c) 2024 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

import os
import subprocess
from functools import reduce
from .util import (
    TEST_TYPES,
    SCHEME,
    config_logger,
    github_summary,
    github_log,
    logger,
    dict2str,
)
import json


class Tests:
    def __init__(self, args):
        config_logger(args.verbose)
        self.args = args
        self.failed = []

    def fail(self, info):
        self.failed.append(info)

    def check_fail(self):
        num_failed = len(self.failed)
        if num_failed > 0:
            print(f"{num_failed} tests FAILED")
            for info in self.failed:
                print(f"* {info}")
            exit(1)
        print("All good!")
        exit(0)

    def cmd_prefix(self):
        res = []
        if self.args.run_as_root is True:
            res += ["sudo"]
        if self.args.exec_wrapper is not None and self.args.exec_wrapper != "":
            res += self.args.exec_wrapper.split(" ")
        if self.args.mac_taskpolicy is not None:
            res += ["taskpolicy", "-c", f"{mac_taskpolicy}"]

        return res

    def make_j(self):
        if self.args.j is None or int(self.args.j) == 1:
            return []
        return [f"-j{self.args.j}"]

    def do_opt_all(self):
        return self.args.opt.lower() == ["all"]

    def do_opt(self):
        return self.args.opt.lower() in ["all", "opt"]

    def do_no_opt(self):
        return self.args.opt.lower() in ["all", "no_opt"]

    def compile_mode(self):
        return "Cross" if self.args.cross_prefix is not None else "Native"

    def _compile_schemes(self, test_type, opt):
        """compile or cross compile with some extra environment variables and makefile arguments"""

        opt_label = "opt" if opt else "no_opt"

        github_log(
            f"::group::compile {self.compile_mode()} {opt_label} {test_type.desc()}"
        )

        log = logger(test_type, "Compile", self.args.cross_prefix, opt)

        extra_make_args = [f"OPT={int(opt)}", f"AUTO={int(self.args.auto)}"]
        if test_type.is_benchmark() is True:
            extra_make_args += [f"CYCLES={self.args.cycles}"]
        extra_make_args += self.make_j()

        args = ["make", test_type.make_target()] + extra_make_args

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
            self.fail(f"Compilation for ({test_type},{opt_label})")

        github_log("::endgroup::")

    def _run_scheme(
        self,
        test_type,
        opt,
        scheme,
        suppress_output=True,
    ):
        """Run the binary in all different ways

        Arguments:

        - scheme: Scheme to test
        - suppress_output: Indicate whether to suppress or print-and-return the output
        """

        opt_label = "opt" if opt else "no_opt"

        if scheme is None:
            scheme_str = "All"
        else:
            scheme_str = str(scheme)

        log = logger(test_type, scheme_str, self.args.cross_prefix, opt)

        args = ["make", test_type.make_run_target(scheme)]
        if test_type.is_benchmark() is False:
            args += self.make_j()

        env_update = {}
        if len(self.cmd_prefix()) > 0:
            env_update["EXEC_WRAPPER"] = " ".join(self.cmd_prefix())

        env = os.environ.copy()
        env.update(env_update)

        cmd_str = dict2str(env_update) + " ".join(args)
        log.info(cmd_str)

        p = subprocess.run(args, capture_output=True, universal_newlines=False, env=env)

        if p.returncode != 0:
            log.error(f"'{cmd_str}' failed with with {p.returncode}")
            log.error(p.stderr.decode())
            self.fail(f"{test_type.desc()} ({opt_label}, {scheme_str})")
            return True  # Failure
        elif suppress_output is True:
            if self.args.verbose is True:
                log.info(p.stdout.decode())
            return False  # No failure
        else:
            result = p.stdout.decode()
            log.info(result)
            return result

    def _run_schemes(self, test_type, opt, suppress_output=True):
        """Arguments:

        - opt: Whether native backends should be enabled
        - suppress_output: Indicate whether to suppress or print-and-return the output
        """

        results = {}

        k = "opt" if opt else "no_opt"

        github_log(f"::group::run {self.compile_mode()} {k} {test_type.desc()}")

        results[k] = {}
        for scheme in SCHEME:
            result = self._run_scheme(
                test_type,
                opt,
                scheme,
                suppress_output,
            )

            results[k][scheme] = result

        title = "## " + (self.compile_mode()) + " " + (k.capitalize()) + " Tests"
        github_summary(title, test_type.desc(), results[k])

        github_log("::endgroup::")

        if suppress_output is True:
            # In this case, we only gather success/failure booleans
            return reduce(
                lambda acc, c: acc or c,
                [r for rs in results.values() for r in rs.values()],
                False,
            )
        else:
            return results

    def func(self):
        def _func(opt):
            self._compile_schemes(TEST_TYPES.FUNC, opt)
            if self.args.run:
                self._run_schemes(TEST_TYPES.FUNC, opt)

        if self.do_no_opt():
            _func(False)
        if self.do_opt():
            _func(True)

        self.check_fail()

    def nistkat(self):
        def _nistkat(opt):
            self._compile_schemes(TEST_TYPES.NISTKAT, opt)
            if self.args.run:
                self._run_schemes(TEST_TYPES.NISTKAT, opt)

        if self.do_no_opt():
            _nistkat(False)
        if self.do_opt():
            _nistkat(True)

        self.check_fail()

    def kat(self):
        def _kat(opt):
            self._compile_schemes(TEST_TYPES.KAT, opt)
            if self.args.run:
                self._run_schemes(TEST_TYPES.KAT, opt)

        if self.do_no_opt():
            _kat(False)
        if self.do_opt():
            _kat(True)

        self.check_fail()

    def acvp(self):
        def _acvp(opt):
            self._compile_schemes(TEST_TYPES.ACVP, opt)
            if self.args.run:
                self._run_scheme(TEST_TYPES.ACVP, opt, None)

        if self.do_no_opt():
            _acvp(False)
        if self.do_opt():
            _acvp(True)

        self.check_fail()

    def bench(self):
        output = self.args.output
        components = self.args.components

        if components is False:
            test_type = TEST_TYPES.BENCH
        else:
            test_type = TEST_TYPES.BENCH_COMPONENTS
            output = False

        # NOTE: We haven't yet decided how to output both opt/no-opt benchmark results
        if self.do_opt_all():
            self._compile_schemes(test_type, False)
            if self.args.run:
                self._run_schemes(test_type, False, suppress_output=False)
            self._compile_schemes(test_type, True)
            if self.args.run:
                resultss = self._run_schemes(test_type, True, suppress_output=False)
        else:
            self._compile_schemes(test_type, self.do_opt())
            if self.args.run:
                resultss = self._run_schemes(
                    test_type, self.do_opt(), suppress_output=False
                )

        if resultss is None:
            exit(0)

        # NOTE: There will only be one items in resultss, as we haven't yet decided how to write both opt/no-opt benchmark results
        for k, results in resultss.items():
            if not (results is not None and output is not None and components is False):
                continue

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

            with open(output, "w") as f:
                f.write(json.dumps(v))

    def all(self):
        func = self.args.func
        kat = self.args.kat
        nistkat = self.args.nistkat
        acvp = self.args.acvp

        def _all(opt):
            if func is True:
                self._compile_schemes(TEST_TYPES.FUNC, opt)
            if kat is True:
                self._compile_schemes(TEST_TYPES.KAT, opt)
            if nistkat is True:
                self._compile_schemes(TEST_TYPES.NISTKAT, opt)
            if acvp is True:
                self._compile_schemes(TEST_TYPES.ACVP, opt)

            if self.args.run is False:
                return

            if func is True:
                self._run_schemes(TEST_TYPES.FUNC, opt)
            if kat is True:
                self._run_schemes(TEST_TYPES.KAT, opt)
            if nistkat is True:
                self._run_schemes(TEST_TYPES.NISTKAT, opt)
            if acvp is True:
                self._run_schemes(TEST_TYPES.ACVP, opt)

        if self.do_no_opt():
            _all(False)
        if self.do_opt():
            _all(True)

        self.check_fail()

    def cbmc(self):
        def run_cbmc(mlkem_k):
            envvars = {"MLKEM_K": mlkem_k}
            p = subprocess.Popen(
                [
                    "python3",
                    "run-cbmc-proofs.py",
                    "--summarize",
                    "--no-coverage",
                ]
                + self.make_j(),
                cwd="cbmc",
                env=os.environ.copy() | envvars,
            )
            p.communicate()

            if p.returncode != 0:
                self.fail(f"CBMC proofs for k={mlkem_k}")

        k = self.args.k
        if k == "ALL":
            run_cbmc("2")
            run_cbmc("3")
            run_cbmc("4")
        else:
            run_cbmc(k)

        self.check_fail()
