# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Tests for check-bind. Run: python3 -m unittest test_bind"""

import importlib.machinery
import importlib.util
import os
import struct
import tempfile
import unittest

import conform

HERE = os.path.dirname(os.path.realpath(__file__))
loader = importlib.machinery.SourceFileLoader("check_bind", f"{HERE}/check-bind")
spec = importlib.util.spec_from_loader("check_bind", loader)
bind = importlib.util.module_from_spec(spec)
loader.exec_module(bind)


def elf(sections):
    """A minimal ELF64 file with the given (name, type, info, contents)
    sections, after the null section, and a section-name table."""
    names = b"\0" + b"".join(n.encode() + b"\0" for n, _, _, _ in sections)
    names += b".shstrtab\0"
    body = b"".join(c for _, _, _, c in sections) + names
    ident = b"\x7fELF\x02\x01\x01" + bytes(9)
    shnum = len(sections) + 2
    header = struct.pack(
        "<16sHHIQQQIHHHHHH",
        ident,
        1,
        183,
        1,
        0,
        0,
        64 + len(body),
        0,
        64,
        0,
        0,
        64,
        shnum,
        shnum - 1,
    )
    shdrs, offset, name = [bytes(64)], 64, 1
    for n, kind, info, contents in sections:
        shdrs.append(
            struct.pack(
                "<IIQQQQIIQQ", name, kind, 0, 0, offset, len(contents), 0, info, 1, 0
            )
        )
        offset += len(contents)
        name += len(n) + 1
    shdrs.append(
        struct.pack("<IIQQQQIIQQ", name, 3, 0, 0, offset, len(names), 0, 0, 1, 0)
    )
    return header + body + b"".join(shdrs)


class Bind(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()

    def write(self, name, data):
        path = os.path.join(self.dir, name)
        with open(path, "wb") as f:
            f.write(data)
        return path

    def test_section(self):
        path = self.write(
            "f.o", elf([(".text", 1, 0, b"\x01\x02"), (".data", 1, 0, b"\x09")])
        )
        self.assertEqual(bind.elf_section(path, ".text"), b"\x01\x02")
        self.assertEqual(bind.elf_section(path, ".data"), b"\x09")
        with self.assertRaisesRegex(bind.Failed, "expected one .bss section"):
            bind.elf_section(path, ".bss")

    def test_relocations_are_refused(self):
        rela = (".rela.text", bind.SHT_RELA, 1, bytes(24))
        path = self.write("f.o", elf([(".text", 1, 0, b"\x01"), rela]))
        with self.assertRaisesRegex(bind.Failed, ".text has relocations"):
            bind.elf_section(path, ".text")

    def check(self, code, text, bind_line):
        obj = self.write("f.o", elf([(".text", 1, 0, code)]))
        defs = os.path.join(self.dir, "f.defs")
        conform.write_entries(defs, "# test\n", {"definition mc": text})
        path = self.write(
            "f.bind",
            f"# comment\nmc {obj} .text\n".encode()
            if bind_line is None
            else bind_line.encode(),
        )
        return bind.check(path)

    def test_check(self):
        report = self.check(b"\x01\xff", "|- (= mc #x[01 ff])", None)
        self.assertIn("mc: 2 bytes, sha256 ", report[0])
        with self.assertRaisesRegex(bind.Failed, "mc differs from .text"):
            self.check(b"\x01\xfe", "|- (= mc #x[01 ff])", None)
        with self.assertRaisesRegex(bind.Failed, "not a byte list"):
            self.check(b"\x01", "|- (= mc [x])", None)
        with self.assertRaisesRegex(bind.Failed, "binds nothing"):
            self.check(b"\x01", "|- (= mc #x[01])", "# nothing\n")

    def test_edited_note_fails(self):
        self.check(b"\x01", "|- (= mc #x[01])", None)
        defs = os.path.join(self.dir, "f.defs")
        with open(defs) as f:
            text = f.read().replace("1 bytes", "2 bytes")
        with open(defs, "w") as f:
            f.write(text)
        with self.assertRaisesRegex(bind.Failed, "the comment before"):
            bind.check(os.path.join(self.dir, "f.bind"))


if __name__ == "__main__":
    unittest.main()
