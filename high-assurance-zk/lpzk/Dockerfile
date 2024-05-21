FROM ubuntu:latest

RUN \
	apt -q -y update && \
	apt -q -y install build-essential && \
	apt -q -y install git && \
	apt -q -y install opam
	
RUN opam init -y
RUN opam switch create 5.1.0
RUN eval $(opam env)

RUN opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
RUN apt install -y libgmp-dev
RUN apt install -y libpcre3-dev
RUN apt install -y pkg-config
RUN apt install -y zlib1g-dev
RUN apt install -y autoconf
RUN apt install -y pip
RUN apt install -y python3

RUN opam install -y --deps-only easycrypt
RUN opam install -y why3

RUN opam install -y alt-ergo
#RUN opam install -y z3

WORKDIR home
RUN git clone https://github.com/EasyCrypt/easycrypt.git
RUN cd easycrypt # && git checkout 796cc2d1127fac39bebf3e0ed243b47eb761896d
RUN eval $(opam env) && cd easycrypt && make && make install
RUN eval $(opam env) && why3 config detect

#RUN opam switch create 5.0.0
RUN opam install -y ocamlbuild
RUN opam install -y ocamlfind
RUN opam install -y dune
RUN opam install -y containers
RUN opam install -y zarith
RUN opam install -y yojson
RUN opam install -y ppx_deriving
RUN opam install -y domainslib
RUN opam install -y cryptokit
RUN opam install -y tyre
RUN opam pin -y git+https://github.com/disteph/timer.git#main
RUN opam pin -y https://github.com/disteph/tracing.git

RUN echo 'eval $(opam env)' > /root/.bashrc

COPY /proof /home/proof
COPY /extraction /home/extraction
#COPY /tests /home/tests
COPY /config /home/config

RUN mkdir ~/.config
RUN mkdir ~/.config/easycrypt/
RUN mv /home/config/easycrypt.conf ~/.config/easycrypt/

COPY Makefile /home

CMD ["bash"]
