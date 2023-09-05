all: help

include Makefile.common

ECDIRS = generic-mith mith-bgw mith-maurer
IMPLDIRS = implementation-bgw implementation-maurer
SUBDIRS = $(ECDIRS) $(IMPLDIRS)

ALL_COMPONENTS = abstract bgw maurer jasmin bgw_unverified maurer_unverified

.PHONY: help build-all test-all check-all cloc-all cloc-comps

help:
	@echo
	@echo "Available targets:"
	@echo "build-all  --  builds all the executables"
	@echo "test-all  --  runs some tests"
	@echo "check-all  --  checks (compiles) all easycrypt scripts"
	@echo "<ECDIR>.check  --  checks easycrypt files in <SUBDIR> "
	@echo "cloc-all  --  computes global 'cloc' counts"
	@echo "cloc-comps  --  computes 'cloc' counts for all <COMPONENT>"
	@echo "<SUBDIR>.cloc  --  computes 'cloc' counts for <SUBDIR>"
	@echo "clean  --  cleanup working dir"
	@echo
	@echo "where:"
	@echo "  <ECDIR> ::= "$(ECDIRS)
	@echo "  <COMPONENT> ::= "$(ALL_COMPONENTS)
	@echo "  <SUBDIR> ::= "$(SUBDIRS)

build-all:
	@for d in $(IMPLDIRS); do (cd $$d; make build); done

test-all:
	@for d in $(IMPLDIRS); do (cd $$d; make test); done

cloc-all:
	@echo '************************************'
	@echo "       OVERLALL COUNTS"
	@echo '************************************'
	@$(CLOC_CMD) $(CLOCFLAGS) .

cloc-comps:
	@for i in $(ALL_COMPONENTS); do echo; echo '************************************'; echo "\t $$i"; echo '************************************'; $(CLOC_CMD) $(CLOCFLAGS) --list-file=config/cloc_$$i.files; done


%.cloc:
	$(CLOC_CMD) $(CLOCFLAGS) $(shell basename $@ .cloc)


check-all:
	@for i in $(ECDIRS); do echo; echo '************************************'; echo "\t $$i"; echo '************************************'; ec-runtest config/tests.config --report=$$i.report $$i; done

%.check:
	ec-runtest config/tests.config --report=$(shell basename $@ .check).report  $(shell basename $@ .check)

clean: _clean
	@for d in $(IMPLDIRS); do (cd $$d; make clean); done
	@rm -f *.report

