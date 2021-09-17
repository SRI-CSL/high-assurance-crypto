# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_JOBS ?= 1
OCAMLBUILD_BIN   ?= ocamlbuild
OCAMLBUILD_EXTRA ?= 
OCAMLBUILD_OPTS :=-use-ocamlfind -tag thread -tag debug -tag bin_annot -tag short_paths -cflags "-g -w A-4-33-40-41-42-43-34-44" -cflags -strict-sequence -j $(OCAMLBUILD_JOBS)

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_OPTS += -classic-display
endif
ifeq ($(LINT),1)
 OCAMLBUILD_OPTS += -tag lint
endif
OCAMLBUILD_OPTS += $(OCAMLBUILD_EXTRA)

OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_OPTS)

# --------------------------------------------------------------------
.PHONY: all help build byte native 
.PHONY: clean 

EXE_P = benchmark_25519.native
TESTS_P = $(wildcard tests/25519/*)
BENCHS_P = $(wildcard benchs/25519/*)
EXE_S = benchmark_small_modulus.native
TESTS_S = $(wildcard tests/small_modulus/*)
BENCHS_S = $(wildcard benchs/small_modulus/*)
EXE_B = benchmark_boolean.native
TESTS_B = $(wildcard tests/boolean/*)
BENCHS_B = $(wildcard benchs/boolean/*)
EXE = benchmark.native

EXE_ARGS = -prover -verifier 1

all: help

help:
	@echo
	@echo "Available targets:"
	@echo "build  --  compiles the code, producing the executable '$(EXE)'"
	@echo "clean  --  cleans the build files, please run if you encounter any build error"
	@echo "test   --  runs the executable on the test circuits (from directory 'tests')"
	@echo "bench  --  runs the executable on benchmark circuits (from directory 'benchs')"	

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
	echo "---------------------------------"; echo "    $(2)"; echo "---------------------------------"; ./$(1) $(2) $(EXE_ARGS)
endef

define do-build
	cp "maurer_$(1).c" "maurer.c"
	cp "MPC_$(1).s" MPC.s
	cp "src/MPC/Maurer/NextMsgMaurerAPI_$(1).ml" "src/MPC/Maurer/NextMsgMaurerAPI.ml"
	rm -f "benchmark_$(1).native"
	$(OCAMLBUILD) "src/benchmark_$(1).native"
	rm -f "maurer.c" "MPC.s" "src/MPC/Maurer/NextMsgMaurerAPI.ml"
endef

define do-build-exe
	cp "maurer_25519.c" "maurer.c"
	cp "MPC_25519.s" MPC.s
	cp "src/MPC/Maurer/NextMsgMaurerAPI_25519.ml" "src/MPC/Maurer/NextMsgMaurerAPI.ml"
	rm -f "benchmark.native"
	$(OCAMLBUILD) "src/benchmark.native"
	rm -f "maurer.c" "MPC.s" "src/MPC/Maurer/NextMsgMaurerAPI.ml"
endef

# --------------------------------------------------------------------

all: build
	@true

build: $(EXE_P) $(EXE_S) $(EXE_B) $(EXE)

$(EXE_P):
	$(call do-build,25519)

$(EXE_S):
	$(call do-build,small_modulus)

$(EXE_B):
	$(call do-build,boolean)

$(EXE):
	$(call do-build-exe)

test: test_p test_s test_b

test_p: $(EXE_P) $(TESTS_P)
	$(call do-header,"TESTING MAURER: "$(EXE_P))
	@for t in $(TESTS_P); do $(call do-test,$(EXE_P),$$t); done 

test_s: $(EXE_S) $(TESTS_S)
	$(call do-header,"TESTING MAURER: "$(EXE_S))
	@for t in $(TESTS_S); do $(call do-test,$(EXE_S),$$t); done 

test_b: $(EXE_B) $(TESTS_B)
	$(call do-header,"TESTING MAURER: "$(EXE_B))
	@for t in $(TESTS_B); do $(call do-test,$(EXE_B),$$t); done 

bench: bench_p bench_s bench_b

bench_p: $(EXE_P) $(BENCHS_P)
	$(call do-header,"BENCHMARKING MAURER: "$(EXE_P))
	@for t in $(BENCHS_P); do $(call do-test,$(EXE_P),$$t); done 

bench_s: $(EXE_S) $(BENCHS_S)
	$(call do-header,"BENCHMARKING MAURER: "$(EXE_S))
	@for t in $(BENCHS_S); do $(call do-test,$(EXE_S),$$t); done 

bench_b: $(EXE_B) $(BENCHS_B)
	$(call do-header,"BENCHMARKING MAURER: "$(EXE_B))
	@for t in $(BENCHS_B); do $(call do-test,$(EXE_B),$$t); done 

clean:
	@$(OCAMLBUILD) -clean
	@rm -f $(EXE_P) $(EXE_S) $(EXE_B)
	@rm -f "maurer.c" "MPC.s" "src/MPC/Maurer/NextMsgMaurerAPI.ml"
	@rm -f *.dat
