# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Host-only regression tests for NUCLEO-N657X0-Q helper modules."""

import os
import struct
import unittest
from unittest import mock

import exec_wrapper
import flexmem_configure
from nucleo_host.argv_blob import ARGV_BLOCK_SIZE, pack_cmdline
from nucleo_host.flexmem import PLATFORM_MK, flexmem_config_build_instructions
from nucleo_host.gdb_script import build_run_script, restore_argv_command
from nucleo_host.results import fault_info_from_gdb
from nucleo_host.results import gdb_load_failed
from nucleo_host.results import gdb_load_failed_before_target_output
from nucleo_host.results import parse_exit_sentinel
from nucleo_host.results import split_stdout_capture
from nucleo_host.symbols import parse_nm_symbol, parse_readelf_symbol


class NucleoHostTest(unittest.TestCase):
    """Exercise debugger-independent helper behavior without board access."""

    def test_pack_cmdline_uses_absolute_string_pointers(self):
        """The argv table uses absolute target string pointers."""
        blob = pack_cmdline(["prog", "--flag"], 0x20000000)

        argc, arg0, arg1 = struct.unpack_from("<III", blob)

        self.assertEqual(len(blob), ARGV_BLOCK_SIZE)
        self.assertEqual(argc, 2)
        self.assertEqual(arg0, 0x2000000C)
        self.assertEqual(arg1, 0x20000011)
        self.assertEqual(blob[12:24], b"prog\x00--flag\x00")

    def test_pack_cmdline_rejects_oversized_blob(self):
        """Oversized argv payloads fail before GDB writes target memory."""
        with self.assertRaisesRegex(ValueError, "exceeds"):
            pack_cmdline(["x" * ARGV_BLOCK_SIZE], 0x20000000)

    def test_parse_exit_sentinel(self):
        """Exit sentinels are recognized and malformed codes map to failure."""
        self.assertEqual(parse_exit_sentinel("[[MLKEM-EXIT:0]]\n"), (True, 0))
        self.assertEqual(
            parse_exit_sentinel("[[MLKEM-EXIT:not-an-int]]\n"), (True, 1)
        )
        self.assertEqual(parse_exit_sentinel("ordinary output"), (False, None))

    def test_split_stdout_capture_removes_exit_sentinel(self):
        """RAM stdout dumps are decoded with the exit sentinel stripped out."""
        output, exit_code = split_stdout_capture(
            b"hello\n[[MLKEM-EXIT:7]]\nworld\n"
        )

        self.assertEqual(output, "hello\nworld\n")
        self.assertEqual(exit_code, 7)

    def test_parse_nm_symbol(self):
        """The nm parser returns the exact requested symbol address."""
        nm_output = "00000000 T Reset_Handler\n30000000 B mlk_cmdline_block\n"

        self.assertEqual(
            parse_nm_symbol(nm_output, "mlk_cmdline_block"), "0x30000000"
        )
        self.assertIsNone(parse_nm_symbol(nm_output, "missing"))

    def test_parse_readelf_symbol(self):
        """The readelf parser returns only exact symbol hits."""
        readelf_output = (
            "   42: 00001234     8 FUNC    GLOBAL DEFAULT    1 __wrap_main\n"
        )

        self.assertEqual(
            parse_readelf_symbol(readelf_output, "__wrap_main"), "0x00001234"
        )
        self.assertIsNone(parse_readelf_symbol(readelf_output, "main"))

    def test_fault_info_decodes_register_bits(self):
        """Fault formatting expands CFSR/HFSR bit names for diagnostics."""
        gdb_text = "CFSR=0x00030000\nHFSR=0x40000000\nPC=0x00000123\n"

        fault_info = fault_info_from_gdb(gdb_text)

        self.assertIn("CFSR=0x00030000", fault_info)
        self.assertIn("UNDEFINSTR", fault_info)
        self.assertIn("INVSTATE", fault_info)
        self.assertIn("FORCED", fault_info)

    def test_gdb_load_failed_detects_representative_output(self):
        """GDB load failures are detected case-insensitively."""
        self.assertTrue(
            gdb_load_failed("Error finishing flash operation\nLoad failed\n")
        )
        self.assertTrue(
            gdb_load_failed("warning: section write failed: load FAILED")
        )
        self.assertFalse(
            gdb_load_failed("Loading section .text, size 0x100 lma 0x0")
        )

    def test_gdb_load_failed_requires_no_target_output(self):
        """Load-failure recovery is skipped once target output has started."""
        gdb_text = "Load failed\n"

        self.assertTrue(gdb_load_failed_before_target_output(gdb_text))
        self.assertFalse(
            gdb_load_failed_before_target_output(
                gdb_text, target_output_observed=True
            )
        )
        self.assertFalse(
            gdb_load_failed_before_target_output(
                gdb_text, exit_code_observed=True
            )
        )
        self.assertFalse(
            gdb_load_failed_before_target_output(
                "Load failed\n[[MLKEM-EXIT:0]]\n"
            )
        )

    def test_flexmem_config_build_instructions_show_make_command(self):
        """Missing config diagnostics explain how to build the helper ELF."""
        instructions = flexmem_config_build_instructions(
            "/tmp/flexmem_config.elf"
        )

        self.assertIn(
            f"make flexmem_config EXTRA_MAKEFILE={PLATFORM_MK}", instructions
        )
        self.assertIn(
            f"make run_flexmem_config EXTRA_MAKEFILE={PLATFORM_MK}",
            instructions,
        )
        self.assertIn("/tmp/flexmem_config.elf", instructions)

    def test_load_failure_recovery_reports_build_hint_when_config_missing(
        self,
    ):
        """The wrapper points users at flexmem_config."""
        messages = []
        env = {"FLEXMEM_CONFIG_ELF": "/tmp/missing_flexmem_config.elf"}

        def fake_exists(path):
            return path.endswith("flexmem_configure.py")

        with mock.patch.dict(os.environ, env), mock.patch.object(
            exec_wrapper.os.path, "exists", side_effect=fake_exists
        ), mock.patch.object(exec_wrapper, "err", side_effect=messages.append):
            self.assertFalse(exec_wrapper._recover_after_load_failure())

        self.assertIn(
            "FLEXMEM config ELF not found: /tmp/missing_flexmem_config.elf",
            messages,
        )
        self.assertTrue(
            any("make flexmem_config" in message for message in messages)
        )

    def test_flexmem_configure_reports_build_hint_when_config_missing(self):
        """Direct configure invocations also report the build command."""
        messages = []
        argv = ["flexmem_configure.py", "/tmp/missing_flexmem_config.elf"]

        with mock.patch.object(
            flexmem_configure.sys, "argv", argv
        ), mock.patch.object(
            flexmem_configure.os.path, "exists", return_value=False
        ), mock.patch.object(
            flexmem_configure, "err", side_effect=messages.append
        ):
            self.assertEqual(flexmem_configure.main(), 2)

        self.assertIn(
            "Config ELF not found: /tmp/missing_flexmem_config.elf", messages
        )
        self.assertTrue(
            any("make flexmem_config" in message for message in messages)
        )

    def test_main_recovers_once_after_load_failure(self):
        """The wrapper invokes FLEXMEM configuration once before retrying."""
        run_results = iter([23, 0])

        def fake_run_once():
            rc = next(run_results)
            if rc != 0:
                exec_wrapper.TARGET_FAILURE = True
                exec_wrapper.TARGET_FAILURE_KIND = "load-failed"
                exec_wrapper.LAST_LOAD_FAILURE_DIAGNOSTICS = "Load failed\n"
            else:
                exec_wrapper.TARGET_FAILURE = False
                exec_wrapper.TARGET_FAILURE_KIND = ""
            return rc

        env = {
            "GDB_RUN_ATTEMPTS": "1",
            "GDB_HARDFAULT_RECOVERY_ATTEMPTS": "0",
            "GDB_LOAD_FAILURE_RECOVERY_ATTEMPTS": "1",
        }
        with mock.patch.dict(os.environ, env), mock.patch.object(
            exec_wrapper, "_run_once", side_effect=fake_run_once
        ), mock.patch.object(
            exec_wrapper, "_recover_after_load_failure", return_value=True
        ) as recover, mock.patch.object(
            exec_wrapper.time, "sleep"
        ):
            self.assertEqual(exec_wrapper.main(), 0)

        recover.assert_called_once_with()

    def test_load_failure_recovery_invokes_flexmem_configure(self):
        """The load-failure recovery path runs the platform config helper."""
        completed = mock.Mock(returncode=0, stdout="")
        env = {"FLEXMEM_CONFIG_ELF": "/tmp/flexmem_config.elf"}

        with mock.patch.dict(os.environ, env), mock.patch.object(
            exec_wrapper.os.path, "exists", return_value=True
        ), mock.patch.object(
            exec_wrapper, "run", return_value=completed
        ) as run:
            self.assertTrue(exec_wrapper._recover_after_load_failure())

        cmd = run.call_args.args[0]
        self.assertEqual(cmd[0], exec_wrapper.sys.executable)
        self.assertTrue(cmd[1].endswith("flexmem_configure.py"))
        self.assertEqual(cmd[2], "/tmp/flexmem_config.elf")
        self.assertEqual(
            run.call_args.kwargs["env"]["STLINK_CONNECT_MODE"], "UR"
        )

    def test_main_reports_diagnostics_when_load_recovery_fails(self):
        """Load-failure diagnostics survive a failed FLEXMEM recovery."""
        messages = []

        def fake_run_once():
            exec_wrapper.TARGET_FAILURE = True
            exec_wrapper.TARGET_FAILURE_KIND = "load-failed"
            exec_wrapper.LAST_LOAD_FAILURE_DIAGNOSTICS = (
                "Load failed\nCannot access memory\n"
            )
            return 23

        env = {
            "GDB_RUN_ATTEMPTS": "1",
            "GDB_HARDFAULT_RECOVERY_ATTEMPTS": "0",
            "GDB_LOAD_FAILURE_RECOVERY_ATTEMPTS": "1",
        }
        with mock.patch.dict(os.environ, env), mock.patch.object(
            exec_wrapper, "_run_once", side_effect=fake_run_once
        ), mock.patch.object(
            exec_wrapper, "_recover_after_load_failure", return_value=False
        ), mock.patch.object(
            exec_wrapper, "err", side_effect=messages.append
        ), mock.patch.object(
            exec_wrapper.time, "sleep"
        ):
            self.assertEqual(exec_wrapper.main(), 23)

        self.assertIn(
            "GDB load-failure diagnostics from failed run:", messages
        )
        self.assertIn("Load failed\nCannot access memory\n", messages)

    def test_main_does_not_recover_when_load_recovery_disabled(self):
        """Setting zero load-failure attempts disables FLEXMEM recovery."""
        messages = []

        def fake_run_once():
            exec_wrapper.TARGET_FAILURE = True
            exec_wrapper.TARGET_FAILURE_KIND = "load-failed"
            exec_wrapper.LAST_LOAD_FAILURE_DIAGNOSTICS = "Load failed\n"
            return 23

        env = {
            "GDB_RUN_ATTEMPTS": "1",
            "GDB_HARDFAULT_RECOVERY_ATTEMPTS": "0",
            "GDB_LOAD_FAILURE_RECOVERY_ATTEMPTS": "0",
        }
        with mock.patch.dict(os.environ, env), mock.patch.object(
            exec_wrapper, "_run_once", side_effect=fake_run_once
        ), mock.patch.object(
            exec_wrapper, "_recover_after_load_failure"
        ) as recover, mock.patch.object(
            exec_wrapper, "err", side_effect=messages.append
        ), mock.patch.object(
            exec_wrapper,
            "log_output",
            side_effect=lambda msg, *args, **kwargs: messages.append(msg),
        ):
            self.assertEqual(exec_wrapper.main(), 23)

        recover.assert_not_called()
        self.assertIn("FAIL!", messages)
        self.assertIn("gdb batch failed with code 23", messages)
        self.assertIn("Load failed\n", messages)

    def test_restore_argv_command_prefers_numeric_address(self):
        """Numeric argv restore addresses are preferred."""
        self.assertEqual(
            restore_argv_command("argv.bin", "0x1234", "mlk_cmdline_block"),
            "restore argv.bin binary 0x1234",
        )
        self.assertEqual(
            restore_argv_command("argv.bin", None, "mlk_cmdline_block"),
            "restore argv.bin binary &mlk_cmdline_block",
        )

    def test_build_run_script_contains_required_sequence(self):
        """The GDB script keeps the critical run order."""
        gdb_lines = build_run_script(
            port=3333,
            wrap_main_break="*0x100",
            reset_handler_jump="*0x5",
            argv_bin="argv.bin",
            arg_block_addr="0x70000",
            arg_block_sym="mlk_cmdline_block",
            stdout_capture_addr="0x34080000",
            stdout_capture_len_addr="0x30000100",
            stdout_capture_truncated_addr="0x30000104",
            stdout_capture_size=1536,
            stdout_capture_bin="stdout.bin",
        )

        self.assertEqual(
            gdb_lines[:7],
            [
                "set pagination off",
                "set confirm off",
                "target remote localhost:3333",
                "load",
                "tbreak *0x100",
                "jump *0x5",
                "restore argv.bin binary 0x70000",
            ],
        )
        self.assertIn("break HardFault_Handler", gdb_lines)
        self.assertIn("break nucleo_layout_fail", gdb_lines)
        expected_dump = (
            "  dump binary memory stdout.bin 0x34080000 "
            "0x34080000 + $nucleo_stdout_len"
        )
        self.assertIn(expected_dump, gdb_lines)
        self.assertIn("p/x $nucleo_stdout_truncated", gdb_lines)
        self.assertIn("echo CFSR=", gdb_lines)


if __name__ == "__main__":
    unittest.main()
