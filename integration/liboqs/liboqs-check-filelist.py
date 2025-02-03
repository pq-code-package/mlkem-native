#!/usr/bin/env python3
# Copyright (c) 2024-2025 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

# This script makes sure that the sources in the liboqs meta files
# are kept up to date.


import yaml
import os

MLKEM_DIR = "../../mlkem"


def load(fname):
    with open(fname) as f:
        return yaml.safe_load(f)


def get_shared_sources():
    # add files mlkem/*
    sources = [f for f in os.listdir(MLKEM_DIR) if os.path.isfile(f"{MLKEM_DIR}/{f}")]
    # add files mlkem/native/* (API definitions)
    sources += [
        f"native/{f}"
        for f in os.listdir(f"{MLKEM_DIR}/native")
        if os.path.isfile(f"{MLKEM_DIR}/native/{f}")
    ]
    # randombytes.h is provided by liboqs
    sources.remove("randombytes.h")
    return sources


def get_native_sources(backend):
    return [f"native/{backend}"]


def check_implementation(impl):
    name = impl["name"]
    print(f"checking {name}")
    ymlsources = impl["sources"]
    ymlsources = ymlsources.split(" ")
    sources = get_shared_sources()

    if name != "ref":
        sources += get_native_sources(name)

    sources.sort()
    ymlsources.sort()

    if sources != ymlsources:
        print(sources)
        print(ymlsources)
        raise Exception("mismatch of liboqs file list")


def check_file(fname):
    print(f"checking {fname}")
    yml = load(fname)
    implementations = yml["implementations"]
    for implementation in implementations:
        check_implementation(implementation)


def check():
    check_file("ML-KEM-512_META.yml")
    check_file("ML-KEM-768_META.yml")
    check_file("ML-KEM-1024_META.yml")


if __name__ == "__main__":
    check()
