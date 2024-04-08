FROM ubuntu:22.04

RUN apt -y update
RUN apt -y install build-essential
RUN apt -y install ca-certificates
RUN apt -y install git
RUN apt -y install curl
RUN apt -y install unzip
RUN apt -y install bubblewrap
	
# OPAM
RUN echo "insecure" > $HOME/.curlrc
RUN echo | bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
RUN opam init -y
# RUN apt install opam

# RUN opam init -y
# #RUN opam switch create 5.0.1
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
#RUN cd easycrypt # && git checkout 796cc2d1127fac39bebf3e0ed243b47eb761896d
RUN eval $(opam env) && cd easycrypt && make && make install
RUN eval $(opam env) && easycrypt why3config

RUN echo 'eval $(opam env)' > /root/.bashrc

RUN mkdir /home/proof
COPY src /home/proof/src

COPY config /home/proof/config

RUN mv /home/proof/config/easycrypt.conf ~/.config/easycrypt/

# COPY Makefile /home

ENTRYPOINT /home/easycrypt/scripts/testing/runtest --jobs="0" proof/config/tests.config lpzk
#CMD ["bash"]
