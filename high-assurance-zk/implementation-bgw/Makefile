# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_JOBS ?= 1
OCAMLBUILD_BIN   ?= ocamlbuild
OCAMLBUILD_EXTRA ?=
OCAMLBUILD_OPTS := -use-ocamlfind -tag thread -tag debug -tag bin_annot -tag short_paths -cflags "-w A-4-33-40-41-42-43-34-44" -cflags -strict-sequence -j $(OCAMLBUILD_JOBS)

ifeq ($(LINT),1)
 OCAMLBUILD_OPTS += -tag lint
endif

OCAMLBUILD_OPTS += $(OCAMLBUILD_EXTRA)

OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_OPTS)
# --------------------------------------------------------------------

.PHONY: all help build byte native 
.PHONY: clean 

EXE = benchmark.native
EXE_ARGS = 1

TESTS = $(wildcard tests/*)
BENCHS = $(wildcard benchs/*)

define do-build
	$(OCAMLBUILD) "src/$(1)"
endef

define do-header
	@echo
	@echo "**************************************************************************"
	@echo "**************************************************************************"
	@echo "               " $(1)
	@echo "**************************************************************************"
	@echo "**************************************************************************"
	@echo
endef

define do-test
	echo "---------------------------------"; echo "    $(2)"; echo "---------------------------------"; ./$(EXE) $(1) $(EXE_ARGS)
endef

# --------------------------------------------------------------------

all: help

help:
	@echo
	@echo "Available targets:"
	@echo "build  --  compiles the code, producing the executable '$(EXE)'"
	@echo "clean  --  cleans the build files, please run if you encounter any build error"
	@echo "test   --  runs the executable on the test circuits (from directory 'tests')"
	@echo "bench  --  runs the executable on benchmark circuits (from directory 'benchs')"	

build: $(EXE)

byte:
	$(call do-build,benchmark.byte)

native:
	$(call do-build,benchmark.native)

$(EXE):
	$(call do-build,benchmark.native)


test: $(EXE) $(TESTS)
	$(call do-header,"TESTING BGW: "$(EXE))
	@for t in $(TESTS); do $(call do-test,$$t); done 

bench: $(EXE) $(BENCHS)
	$(call do-header,"BENCHMARKING BGW: "$(EXE))
	@for t in $(BENCHS); do $(call do-test,$$t); done 

clean:
	@$(OCAMLBUILD) -clean

