FROM fpco/stack-build:lts-6

WORKDIR /opt

ADD https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/z3-4.4.1-x64-debian-8.2.zip /tmp
RUN unzip /tmp/z3-4.4.1-x64-debian-8.2.zip && \
    mv z3-4.4.1-x64-debian-8.2 z3 && \
    ln -s /opt/z3/bin/z3 /usr/local/bin/z3

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA 4a489c9
RUN git checkout ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    stack install --local-bin-path=/usr/local/bin \
          liquiddesugar liquid-fixpoint prover liquidhaskell

WORKDIR /root
ADD . verified-instances
WORKDIR /root/verified-instances

RUN make all
