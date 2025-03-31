# SPDX-License-Identifier: Apache-2.0

.PHONY: all clean

CC = clang
CPPFLAGS += -Wno-c++17-extensions -fPIC -shared 
LDFLAGS += `llvm-config --cxxflags --ldflags --system-libs --libs core passes`

all: ctllvm.so

%.so: %.cpp
	$(CC) $(CPPFLAGS) $< -o $@ $(LDFLAGS)

clean:
	-$(RM) -rf *.so
