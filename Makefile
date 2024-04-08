.PHONY: default build install uninstall reinstall test clean

default: lib

lib:
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

check-proof:
	cd proof && docker build -t ec-check-docker -f Dockerfile . 
	cd proof && docker run -ti --memory="16g" --cpus="3.0" ec-check-docker