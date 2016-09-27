FROM fpco/stack-build:lts-6

WORKDIR /opt

RUN apt-get -y install z3

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git
WORKDIR /opt/liquidhaskell

# https://github.com/ucsd-progsys/liquidhaskell/pull/836
ENV LIQUID_SHA 5acfe16
RUN git checkout ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    stack install --local-bin-path=/usr/local/bin \
          liquiddesugar liquid-fixpoint prover liquidhaskell

WORKDIR /root
ADD . verified-instances
WORKDIR /root/verified-instances

RUN make all
