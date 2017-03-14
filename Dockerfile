FROM fpco/stack-build:lts-6

RUN apt-get -y install z3

# force http clone instead of git
RUN git config --global url."https://github.com/".insteadOf "git@github.com:"
RUN cp /root/.gitconfig /home/_stack/.gitconfig

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git /opt/liquidhaskell
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA 904e6927a97480856fe2c7d2e083f7bc7a0710c5
RUN git fetch --all && \
    git checkout --force ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    git clean -dffx && \
    stack --system-ghc install --local-bin-path=/usr/local/bin \
          liquiddesugar liquid-fixpoint liquidhaskell
