FROM fpco/stack-build:lts-8.9

RUN apt-get -y install z3

# force http clone instead of git
RUN git config --global url."https://github.com/".insteadOf "git@github.com:"

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git /opt/liquidhaskell
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA 27bc088c4f8b29fd9866e5589233e97e22e314c4
RUN git fetch --all && \
    git checkout --force ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    git clean -dffx && \
    stack --system-ghc install --local-bin-path=/usr/local/bin \
          liquid-fixpoint liquidhaskell
