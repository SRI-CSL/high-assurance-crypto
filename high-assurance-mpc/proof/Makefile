# -*- Makefile -*-

# --------------------------------------------------------------------
ECROOT   ?= ../easycrypt
ECCHECK  ?=
ECARGS   ?=
ECCONF   := config/tests.config 
XUNITOUT ?= xunit.xml
CHECKS   ?= proof

ifeq ($(ECCHECK),)
ifeq ($(ECROOT),)
ECCHECK := ec-runtest
else
PATH    := ${ECROOT}:${PATH}
ECCHECK := $(ECROOT)/scripts/testing/runtest
endif
endif

# --------------------------------------------------------------------

FIND := find
ARG := *.eco

# --------------------------------------------------------------------
.PHONY: default check check-xunit

default:
	@echo "Usage: make <target> where <target> in [check|check-xunit]" >&2

check:
	$(ECCHECK) --bin-args="$(ECARGS)" $(ECCONF) $(CHECKS)
	$(FIND) . -name "$(ARG)" -type f -delete

check-xunit:
	$(ECCHECK) --bin-args="$(ECARGS)" --xunit=$(XUNITOUT) $(ECCONF) $(CHECKS)
