[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Contributing to mlkem-native

We welcome contributors who can help us build mlkem-native. If you are interested, please contact us via e-mail or discord,
so we can introduce each other and understand your background and interest. We do not accept contributions from people we
don't know.

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

### Commit messages

We follow common git conventions:

- **Subject line**: `<Component>: <Summary>`, e.g. `CBMC: Add CaDiCaL SAT profile` or `AArch64, x86_64: Use MLKEM_Q as NTT
  input bound`. The component is the area the commit touches, e.g. `CI`, `CBMC`, `HOL-Light`, `nix`, `AArch64`,
  `x86_64`, `Armv8.1-M`, `FIPS202`, `README`, or a file name such as `sys.h`. Use the imperative mood, capitalize the
  summary, omit the trailing period, and keep the subject at no more than 72 characters.
- **Body**: Separate it from the subject by a blank line and wrap it at 72 characters. Explain what changed and why;
  the diff already shows how. The body may be omitted for trivial changes.
- **Issue references**: Reference an issue the commit resolves in the body, e.g. `Resolves #1603`.
- **Sign-off**: Every commit must carry a `Signed-off-by:` line certifying the [Developer Certificate of
  Origin](https://developercertificate.org/), e.g. via `git commit -s`. This is enforced by the DCO check on pull
  requests.

Each commit should be a self-contained logical change that builds and passes the tests on its own.

### Namespacing

We namespace all entities of global scope, including statics and structures. This is to facilitate monolithic builds of
mlkem-native in a single compilation unit, potentially including multiple copies for different security levels. See
[examples/monolithic_build](examples/monolithic_build) for an example.
