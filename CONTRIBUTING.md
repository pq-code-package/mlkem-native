[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Contributing to mlkem-native

We welcome contributors who can help us build mlkem-native. If you are interested, please contact us, or volunteer for
any of the open issues. Here are some things to get you started.

### Nix (Recommended)

We specify the development environment for mlkem-native using `nix`. If you want to help develop mlkem-native, please
use `nix`. We recommend using the latest Nix version provided by the [nix installer
script](https://nixos.org/download/), but we currently support all Nix versions >= 2.18.

All the development and build dependencies are specified in [flake.nix](flake.nix). To execute a bash shell, run
```bash
nix develop --experimental-features 'nix-command flakes'
```

Use the `./scripts/format` and `./scripts/autogen` scripts (in your `PATH` when using `nix`) to re-format and re-generate all the files respectively. To confirm that everything worked, try `lint` or `tests cbmc`.

### Debian

When using Debian, the following dependencies are needed to be installed:

```bash
sudo apt install shfmt black clang-format llvm python3-pyparsing python3-yaml
```

Additionally, `nixpkgs-fmt` is needed to be compiled from source:

```bash
sudo apt install cargo
cargo install nixpkgs-fmt
export PATH="$PATH:~/.cargo/bin"
```

The scripts `./scripts/format` and `./scripts/autogen` can then be used to re-format and re-generate all the files respectively.

### Coding style

We use auto-formatting using `clang-format` as specified in [.clang-format](.clang-format).

### Namespacing

We namespace all entities of global scope, including statics and structures. This is to facilitate monolithic builds of
mlkem-native in a single compilation unit, potentially including multiple copies for different security levels. See
[examples/monolithic_build](examples/monolithic_build) for an example.
