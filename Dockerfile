FROM fpco/stack-build:lts-6

RUN apt-get -y install z3

# force http clone instead of git
RUN git config --global url."https://github.com/".insteadOf "git@github.com:"
RUN cp /root/.gitconfig /home/_stack/.gitconfig

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git /opt/liquidhaskell
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA 8a4597fe26f3e9196dee4d7a47e26d8b35863a00
RUN git fetch --all && \
    git checkout ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    stack install --local-bin-path=/usr/local/bin \
          liquiddesugar liquid-fixpoint prover liquidhaskell
