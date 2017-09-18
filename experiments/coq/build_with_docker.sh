#!/usr/bin/env bash

set -xe

TAG=verified-instances

docker build -t $TAG .

function go () {
    docker run --rm -it -e DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix -v `pwd`:/coq $TAG -w /coq $*
}

go make clean
go make

# coq coqide /coq/LemmasV2.v
