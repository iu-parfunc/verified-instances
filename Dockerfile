FROM fpco/stack-build:lts-6

RUN apt-get -y install z3

# force http clone instead of git
RUN git config --global url."https://".insteadOf git://

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git /opt/liquidhaskell
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA 0fd0cd4155dd3d677bf8295c9a9922cadac698d7
RUN git fetch --all && \
    git checkout ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    stack install --local-bin-path=/usr/local/bin \
          liquiddesugar liquid-fixpoint prover liquidhaskell
