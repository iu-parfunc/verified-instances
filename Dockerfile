FROM fpco/stack-build:lts-6

RUN apt-get -y install z3

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git /opt/liquidhaskell
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA ad708c7f5a2563c871659dd585a6a045ba9dc716
RUN git fetch --all && \
    git checkout ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    stack install --local-bin-path=/usr/local/bin \
          liquiddesugar liquid-fixpoint prover liquidhaskell
