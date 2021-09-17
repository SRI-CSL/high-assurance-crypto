# Install requirements

FROM easycryptpa/ec-build-box

RUN \
	apt-get -q -y update && \
	apt-get -q -y install libpcre3-dev libgmp3-dev zlib1g-dev && \
	apt-get -q -y install ppl-dev libmpfr-dev libapron-dev gpp

RUN mkdir -p /home/bgw
COPY Makefile Makefile.common /home/bgw

COPY /config /home/bgw/config

RUN eval $(opam env) && \
	opam install /home/bgw/config/dependencies.opam

RUN eval $(opam env) && \
	opam install conf-ppl apron yaml lymp

RUN cd /home && \
	git clone https://github.com/EasyCrypt/easycrypt.git && \
	eval $(opam env) && \
	cd /home/easycrypt && \
	make && \
	make install

RUN echo 'eval $(opam env); cd /home/bgw' > /root/.bashrc

COPY /proof /home/bgw/proof
COPY /extraction /home/bgw/extraction

CMD ["bash"]
