# Install requirements

FROM easycryptpa/ec-build-box

RUN cd /home && \
git clone https://github.com/EasyCrypt/easycrypt.git

RUN eval $(opam env) && \
cd /home/easycrypt && \
make && \
make install

RUN mkdir -p /home/proof
COPY Makefile /home/proof

RUN mkdir -p /home/proof/config
COPY /config /home/proof/config

RUN mkdir -p /home/proof/src
COPY /src /home/proof/src

RUN mkdir -p ~/.config/easycrypt
COPY easycrypt.conf /
RUN mv easycrypt.conf ~/.config/easycrypt/

COPY run.sh /

CMD ["bash", "run.sh"]
