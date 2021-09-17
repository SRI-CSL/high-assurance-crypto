all: help

include Makefile.common

ECDIRS = proof
IMPLDIRS = extraction
SUBDIRS = $(ECDIRS) $(IMPLDIRS)

ALL_COMPONENTS = abstract bgw maurer jasmin bgw_unverified maurer_unverified

.PHONY: help build-all test-all check-all cloc-all cloc-comps

help:
	@echo
	@echo "Available targets:"
	@echo "build  --  builds a benchmark executable for the BGW gates implementations"
	@echo "check  --  checks (compiles) all EasyCrypt scripts"
	@echo "clean  --  cleanup working dir"

build:
	@for d in $(IMPLDIRS); do (cd $$d; make build); done

check:
	@for i in $(ECDIRS); do echo; echo '************************************'; echo "\t $$i"; echo '************************************'; ec-runtest config/tests.config --report=$$i.report $$i; done

clean: _clean
	@for d in $(IMPLDIRS); do (cd $$d; make clean); done
	@rm -f *.report

