all: build

CD := cd
MAKE := make

ECDIRS = $(shell pwd)/proof
IMPLDIRS = $(shell pwd)/extraction/list $(shell pwd)/extraction/array
#TESTDIR = tests
SUBDIRS = $(ECDIRS) $(IMPLDIRS)
ECTEST = /home/easycrypt/scripts/testing/runtest

UC = $(shell echo '$1' | tr '[:lower:]' '[:upper:]')

.PHONY: help build test

help:
	@echo
	@echo "Available targets:"
	@echo
	@echo "       lpzk-array -- builds the array based LPZK implementation"
	@echo
	@echo "        lpzk-list -- builds the list based LPZK implementation"
	@echo
	@echo "           build  --  builds all versions of the LPZK implementation"
	@echo
	@echo "        check-ec  --  checks (compiles) all EasyCrypt scripts"
	@echo
	@echo "           clean  --  cleanup working dir"

lpzk-array:
	$(CD) $(shell pwd)/extraction/array; make

lpzk-list: 
	$(CD) $(shell pwd)/extraction/list; make

build: lpzk-array lpzk-list

check-ec:
	docker build -t ec-check-docker -f Dockerfile .
	docker run -ti --memory="16g" --cpus="3.0" ec-check-docker
	
clean:
	$(CD) $(shell pwd)/extraction/list; $(MAKE) clean
	$(CD) $(shell pwd)/extraction/array; $(MAKE) clean
	$(RM) -f $(ECDIRS).report

