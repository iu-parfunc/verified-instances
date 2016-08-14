FROM fpco/stack-build:lts-6

WORKDIR /opt

# develop branch
ENV LIQUID_SHA 4a489c9

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git && \
    cd liquidhaskell && \
    git checkout ${LIQUID_SHA} && \
    git submodule update --init --recursive

RUN cd liquidhaskell && \
    stack install liquiddesugar && \
    stack install liquid-fixpoint && \
    stack install prover && \
    stack install --local-bin-path=/usr/local/bin

WORKDIR /root
ADD . verified-instances

RUN make all
