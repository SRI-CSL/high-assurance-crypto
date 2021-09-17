# Install requirements

FROM easycryptpa/ec-build-box

RUN \
	apt-get -q -y update && \
	apt-get -q -y install cloc bubblewrap && \
	apt-get -q -y install libpcre3-dev libgmp3-dev zlib1g-dev && \
	apt-get -q -y install ppl-dev libmpfr-dev libapron-dev gpp

RUN mkdir -p /home/mith
COPY Makefile Makefile.common /home/mith

COPY /config /home/mith/config
RUN mv /home/mith/config/ecml.x86_64 /usr/local/bin/ecml && \
	chmod ugo+x /usr/local/bin/ecml

RUN eval $(opam env) && \
	opam install /home/mith/config/dependencies.opam

RUN eval $(opam env) && \
	opam install conf-ppl apron yaml lymp

RUN cd /home && \
	git clone https://gitlab.com/jasmin-lang/jasmin-compiler.git && \
	eval $(opam env) && \
	cd /home/jasmin-compiler/compiler && \
	git checkout glob_array3 && \
	make && \
	install jasminc /usr/local/bin/

RUN cd /home && \
	git clone https://github.com/EasyCrypt/easycrypt.git && \
	eval $(opam env) && \
	cd /home/easycrypt && \
	git checkout deploy-ppe-with-full-path && \
	make && \
	make install

RUN echo 'eval $(opam env); cd /home/mith' > /root/.bashrc

COPY /generic-mith /home/mith/generic-mith
COPY /mith-bgw /home/mith/mith-bgw
COPY /mith-maurer /home/mith/mith-maurer
COPY /implementation-bgw /home/mith/implementation-bgw
COPY /implementation-maurer /home/mith/implementation-maurer

CMD ["bash"]
