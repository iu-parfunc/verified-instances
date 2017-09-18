#!/bin/bash

set -xe

if [ -z "$CABAL_HEAD" ]; then
  export CABAL_HEAD=cabal
fi

run="$CABAL_HEAD new-run liquid -- -iinclude -isrc "

for file in List Newtype Product Sum Unit TwoData ;
do
    $run src/GenericProofs/VerifiedEq/Examples/${file}.hs
done
