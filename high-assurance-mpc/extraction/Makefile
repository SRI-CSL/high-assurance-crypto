# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_JOBS ?= 1
OCAMLBUILD_BIN   ?= ocamlbuild
OCAMLBUILD_EXTRA ?=
OCAMLBUILD_OPTS := -use-ocamlfind -tag thread -tag debug -tag bin_annot -tag short_paths -cflags "-w A-4-33-40-41-42-43-34-44" -cflags -strict-sequence -j $(OCAMLBUILD_JOBS)

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
.PHONY: all build byte native 
.PHONY: clean 

all: build
	@true

build: native

define do-build
	rm -f "$(1)$(EXE)"
	$(OCAMLBUILD) "src/$(1)"
	if [ ! -z "$(EXE)" ]; then \
		cp "_build/src/$(1)" "$(1)$(EXE)"; \
	fi
endef

byte:
	$(call do-build,benchmark.byte)

native:
	$(call do-build,benchmark.native)

wrapper:
	$(call do-build,mzkRun.native)

clean:
	$(OCAMLBUILD) -clean
	rm -f benchmark.byte benchmark.native wrapper.native wrapper.byte
