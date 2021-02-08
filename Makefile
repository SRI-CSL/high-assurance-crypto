LN := ln
RM := rm
FIND := find
MV := mv
MAKE := make
WHY3 := why3

NAME_OPT := -name
ECO := "*.eco"
TYPE_OPT := -type f
DELETE_OPT := -delete

LN_OPT := -si
RM_OPT := -rf

MAKE_OPT := -C

WHY3_OPT := extract --recursive

CLEAN := clean

EC_PATH := $(CURDIR)/easycrypt
ET_PATH := $(CURDIR)/extraction-tool
PROOF_PATH := $(CURDIR)/proof
ME_PATH := $(CURDIR)/modular-extraction

EXTRACT_DIR_OPT := -L extraction-tool

OCAML64_DRIVER := -D ocaml64
EC_DRIVER := -D $(ET_PATH)/ec_driver.drv

ECWHY3 := ecwhy3.native
ZKRUN := zkRun.native
MZKRUN := mzkRun.native

.PHONY: easycrypt clean-easycrypt
.PHONY: check-proof clean-proof
.PHONY: extraction-tool clean-extraction-tool
.PHONY: extract-InTheHead
.PHONY: extraction-wrapper modular-extraction-wrapper

# --------------------------------------------------------------------
# Build EasyCrypt
easycrypt:
	$(MAKE) $(MAKE_OPT) easycrypt/
# Clean EasyCrypt
clean-easycrypt:
	$(MAKE) $(CLEAN) $(MAKE_OPT) easycrypt/
