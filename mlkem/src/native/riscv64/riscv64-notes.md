[//]: # (SPDX-License-Identifier: CC-BY-4.0)

#	rv64v-notes.md

Notes on RISC-V Vector support.

**WARNING** This is highly experimental. Currently vlen=256 only.

###	Some preprequisites for cross compiling

Here's a collection of prerequisites (may contain extras/duplicates:
```
sudo apt install \
asciidoctor autoconf automake autotools-dev bc bison build-essential ccache \
clang clang-format cmake curl device-tree-compiler flex g++ gawk gdb git \
gperf graphviz help2man libeigen3-dev libexpat1-dev libffi-dev libfl2 \
libfl-dev libglib2.0-dev libgmp-dev libgoogle-perftools-dev libmpc-dev \
libmpfr-dev libreadline-dev libtool ninja-build patchutils perl pkg-config \
python3 python3-dev python3-pip slirp tcl-dev texinfo tio xdot zlib1g \
zlib1g-dev libboost-all-dev libboost-system-dev libboost-python-dev \
libboost-filesystem-dev libboost-thread-dev libboost-program-options-dev \
libftdi-dev libusb-1.0-0-dev libftdi1-dev
```

###	Set up local tool directories

I have the following lines at the end of In `~/.bashrc` so that toolchains
can be installed without sude:
```
export RVSRC="$HOME/rv/src"
export RISCV="$HOME/rv/riscv"
export PATH="$RISCV/bin:$PATH"
```

Just create the directories (as a regular user):
```
mkdir -p $RVSRC $RISCV
```

###	Build regular cross-compiler toolchains

Builds `riscv64-unknown-linux-gnu-*` toolchains, both gcc and clang:
```
cd $RVSRC
git clone https://github.com/riscv/riscv-gnu-toolchain
cd riscv-gnu-toolchain
./configure --prefix=$RISCV --enable-llvm --enable-linux --with-arch=rv64gcv
time make
```
This installs the tools locally locally (no `make install`.)


### You'll also need pk
```
cd $RVSRC
git clone https://github.com/riscv-software-src/riscv-pk.git
cd riscv-pk
mkdir build
cd build
../configure --prefix=$RISCV --host=riscv64-unknown-linux-gnu  CC=clang-19
make
make install
```

