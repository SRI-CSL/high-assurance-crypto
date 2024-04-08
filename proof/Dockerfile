FROM ubuntu:latest

RUN \
	apt -q -y update && \
	apt -q -y install build-essential && \
	apt -q -y install git && \
	apt -q -y install opam
	
RUN opam init -y
RUN opam switch create 5.0.0
RUN eval $(opam env)

RUN opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
RUN apt install -y libgmp-dev
RUN apt install -y libpcre3-dev
RUN apt install -y pkg-config
RUN apt install -y zlib1g-dev
RUN apt install -y autoconf
RUN apt install -y pip
RUN pip install pyaml

RUN opam install -y --deps-only easycrypt
RUN opam install -y why3

RUN opam install -y alt-ergo
RUN opam install -y z3

WORKDIR home
RUN git clone https://github.com/EasyCrypt/easycrypt.git
RUN cd easycrypt # && git checkout 796cc2d1127fac39bebf3e0ed243b47eb761896d
RUN eval $(opam env) && cd easycrypt && make && make install
RUN eval $(opam env) && why3 config detect

RUN echo 'eval $(opam env)' > /root/.bashrc

COPY /proof /home/proof
COPY /config /home/config

RUN mkdir ~/.config
RUN mkdir ~/.config/easycrypt/
RUN mv /home/config/easycrypt.conf ~/.config/easycrypt/

COPY Makefile /home

ENTRYPOINT /home/easycrypt/scripts/testing/runtest --timeout="60" --jobs="0" config/tests.config lpzk
#CMD ["bash"]
