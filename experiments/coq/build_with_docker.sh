#!/usr/bin/env bash

# Uses docker but MUTATES the current directory! Naughty.
# Brings up coqide.

set -xe

TAG=verified-instances

docker build -t $TAG .

function go () {
    docker run --rm -it -e DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix -v `pwd`:/coq -w /coq $TAG $*
}

go make clean
go make
go coqide LemmasV2.v
