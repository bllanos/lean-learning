LAKE ?= lake

.PHONY: all run lake

all: run

MAP_ARRAY_DIR := ../map_array

lake:
	$(LAKE) --dir=$(MAP_ARRAY_DIR) build

OUT_DIR = out
LEAN_SYSROOT ?= $(shell lean --print-prefix)
LEAN_LIBDIR := $(LEAN_SYSROOT)/lib/lean

$(OUT_DIR):
	mkdir -p $@

ifneq ($(OS),Windows_NT)
# Add shared library paths to loader path (no Windows equivalent)
LINK_FLAGS=-Wl,-rpath,$(LEAN_LIBDIR) -Wl,-rpath,$(PWD)/$(MAP_ARRAY_DIR)/.lake/build/lib
endif

$(OUT_DIR)/main: main.c lake | $(OUT_DIR)
# Add library paths for Lake package and for Lean itself
	cc -o $@ $< -I $(LEAN_SYSROOT)/include -L $(LEAN_LIBDIR) -L $(MAP_ARRAY_DIR)/.lake/build/lib -lMapArray -lInit_shared -lleanshared_1 -lleanshared $(LINK_FLAGS)

run: $(OUT_DIR)/main
ifeq ($(OS),Windows_NT)
# Add shared library paths to loader path dynamically
	env PATH="$(MAP_ARRAY_DIR)/.lake/build/lib:$(shell cygpath $(LEAN_SYSROOT))/bin:$(PATH)" $(OUT_DIR)/main
else
	$(OUT_DIR)/main
endif
