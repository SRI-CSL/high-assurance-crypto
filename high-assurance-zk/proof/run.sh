#!/bin/bash

cd /home/proof/ && \
    eval $(opam env) && \
    why3 config detect && \
    make check
