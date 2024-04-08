.PHONY: default build install uninstall reinstall test clean

default: build

build:
	dune build

test:
	dune build
	dune build @runtest

install: build
	dune install

reinstall: uninstall install

uninstall:
	dune uninstall

clean:
	dune clean