#!/usr/bin/env bash

set -xe

nix-shell --pure --run "make deps"
nix-shell --pure --run "opam config env > .env"
nix-shell --pure --run 'source .env; make'
nix-shell 
