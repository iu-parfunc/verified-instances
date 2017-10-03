FROM fpco/stack-build:lts-8.9

RUN apt-get -y install z3

# force https on github instead of ssh
RUN git config --system url."https://github.com/".insteadOf "git@github.com:"

RUN git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git /opt/liquidhaskell
WORKDIR /opt/liquidhaskell

# "develop" branch
ENV LIQUID_SHA 7cba25f05c731ae29770b0760e832f34691cf551
RUN git fetch --all && \
    git checkout --force ${LIQUID_SHA} && \
    git submodule update --init --recursive && \
    git clean -dffx && \
    stack --system-ghc install --local-bin-path=/usr/local/bin
