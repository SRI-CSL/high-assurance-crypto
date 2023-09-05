include ../../../Makefile.common

.DEFAULT_GOAL := all

EC_TARGETS ?= Maurer5_jazz.ec Fp_small.ec Fp_bool.ec 
ASM_TARGETS ?= MPC_25519.s MPC_small_modulus.s MPC_boolean.s

all: sfiles ecfiles

sfiles: asm-clean
	@make MPC_25519.s
	@make MPC_small_modulus.s
	@make MPC_boolean.s

ecfiles: $(EC_TARGETS)

bn_generic.s : GFLAGS += -D BN_GENERIC_EXPORT
bn_generic.ec : GFLAGS += -D BN_GENERIC_TOEC

bn_p25519.s : GFLAGS += -D BN_P25519_EXPORT
bn_p25519.ec : GFLAGS += -D BN_P25519_TOEC

Fp_small.s : GFLAGS += -D BN_SMALL_EXPORT
Fp_small.ec : GFLAGS += -D BN_SMALL_TOEC

Fp_bool.s : GFLAGS += -D BN_BOOL_EXPORT
Fp_bool.ec : GFLAGS += -D BN_BOOL_TOEC

Maurer5_jazz.ec : GFLAGS += -D MAURER5_TOEC -D BN_P25519

MPC_25519.s : GFLAGS += -D BN_P25519
MPC_small_modulus.s : GFLAGS += -D BN_SMALL
MPC_boolean.s : GFLAGS += -D BN_BOOL
MPC_25519.s MPC_small_modulus.s MPC_boolean.s: Maurer5_jazz_export.japp
	@$(JASMINC) $(JFLAGS) -o $@ $< || (rm -f $@ && touch fail && echo "\033[1;31m FAIL \033[0m")

asm-clean:
	@rm -f fail *.japp $(ASM_TARGETS)
ec-clean:
	@rm -f fail Array*.ec WArray*.ec $(EC_TARGETS)

clean: asm-clean ec-clean
