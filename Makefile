BASE = /usr
CC = $(BASE)/bin/clang
CXX = $(BASE)/bin/clang++
AR = $(BASE)/bin/llvm-ar
CFLAGS      ?= -O0 -funroll-loops -g3 -Wall -Wno-pointer-sign
CXXFLAGS    ?= -O0 -funroll-loops -g3 -Wall

# Used for llvm pass compilation
LLVM_CONFIG ?= $(BASE)/bin/llvm-config
CLANG_CFL    = `$(LLVM_CONFIG) --cxxflags` -Wl,-znodelete -fno-rtti -fpic $(CXXFLAGS) -DLLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING
CLANG_LFL    = `$(LLVM_CONFIG) --ldflags` $(LDFLAGS)

TARGETS = sgfuzz-source-pass.so

all: $(TARGETS)

sgfuzz-source-pass.so: sgfuzz-source-pass.cc variable-resolver.cc
	$(CXX) $(CLANG_CFL) -fPIC -shared -Wswitch -Wno-deprecated-declarations $^ -o $@ $(CLANG_LFL)

clean:
	rm -f $(TARGETS)
