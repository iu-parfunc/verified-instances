FROM fpco/stack-build:lts-7

WORKDIR /opt

RUN apt-get -y install z3

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA 29bd54f9
RUN git checkout ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    stack install --local-bin-path=/usr/local/bin \
          liquiddesugar liquid-fixpoint prover liquidhaskell

WORKDIR /root
ADD . verified-instances
WORKDIR /root/verified-instances

RUN make all
