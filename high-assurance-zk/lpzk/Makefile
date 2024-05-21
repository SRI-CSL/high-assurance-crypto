all: help

CD := cd
MAKE := make

ECDIRS = proof
IMPLDIRS = extraction/list extraction/array
TESTDIR = tests
SUBDIRS = $(ECDIRS) $(IMPLDIRS)
ECTEST = /home/easycrypt/scripts/testing/runtest

UC = $(shell echo '$1' | tr '[:lower:]' '[:upper:]')

.PHONY: help build test

help:
	@echo
	@echo "Available targets:"
	@echo "                                  build  --  builds all versions of the LPZK implementation"
	@echo
	@echo "test-list <prime=P> <size=N> <cores=K>   --  runs list-based LPZK implementation matrix multiplication of size N, over field P and using K cores"
	@echo "                                             Example: make test-list prime=p1 size=16 cores=4"
	@echo
	@echo "test-array <prime=P> <size=N> <cores=N>  --  runs array-based LPZK implementation matrix multiplication of size N, over field P and using K cores"
	@echo "                                             Example: make test-array prime=p3 size=128 cores=1"
	@echo
	@echo "                               check-ec  --  checks (compiles) all EasyCrypt scripts"
	@echo
	@echo "                                  clean  --  cleanup working dir"
	@echo
	@echo "where:"
	@echo "  <prime>:  p1 - 2^{30}-2^{18}+1"
	@echo "            p2 - 2^{61}-1"
	@echo "            p3 - 2^{255}-19"
	@echo "  <size>:   16, 32, 64 or 128"
	@echo "  <cores>:  desired number of parallel cores"


build:
	opam switch 5.0.0
	@for d in $(IMPLDIRS); do (cd $$d; make); done

define run-test
	@echo "***************************************************************"
	@echo " TESTING $(call UC,$(1))-BASED IMPLEMENTATION AGAINST MM$(3) FOR PRIME $(call UC,$(2))"
	@echo "***************************************************************"
	$(CD) extraction/$(1) ; ./lpzk_exec.exe /home/tests/matrix-mult_$(2)/matrix-mult_$(3)/relation/relation.json /home/tests/matrix-mult_$(2)/matrix-mult_$(3)/instance/instance.json /home/tests/matrix-mult_$(2)/matrix-mult_$(3)/witness/witness.json $(4)
	@echo
endef

test-list:
	opam switch 5.0.0
	$(call run-test,list,$(prime),$(size),$(cores))

test-array:
	opam switch 5.0.0
	$(call run-test,array,$(prime),$(size),$(cores))

check-ec:
	$(ECTEST) --jobs="0" config/tests.config lpzk

clean:
	$(CD) $(IMPLDIRS); $(MAKE) clean
	$(RM) -f $(ECDIRS).report

