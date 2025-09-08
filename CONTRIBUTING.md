[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Contributing to mlkem-native

We welcome contributors who can help us build mlkem-native. If you are interested, please contact us, or volunteer for
any of the open issues. Here are some things to get you started.

### nix setup

We specify the development environment for mlkem-native using `nix`. If you want to help develop mlkem-native, please
use `nix`. We recommend using the latest Nix version provided by the [nix installer
script](https://nixos.org/download/), but we currently support all Nix versions >= 2.18.

All the development and build dependencies are specified in [flake.nix](flake.nix). To execute a bash shell, run
```bash
nix develop --experimental-features 'nix-command flakes'
```

To confirm that everything worked, try `lint` or `tests cbmc`.

### Coding style

We use auto-formatting using `clang-format` as specified in [.clang-format](.clang-format). Use the `./scripts/format`
script (in your `PATH` when using`nix`) to re-format the files accordingly.

### Namespacing

We namespace all entities of global scope, including statics and structures. This is to facilitate monolithic builds of
mlkem-native in a single compilation unit, potentially including multiple copies for different security levels. See
[examples/monolithic_build](examples/monolithic_build) for an example.
