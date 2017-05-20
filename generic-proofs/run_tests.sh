#!/bin/bash

set -xe
stack install

run="stack exec liquid -- -iinclude -isrc "

for file in List Newtype Product Sum Unit;
do
    $run src/GenericProofs/VerifiedEq/Examples/${file}.hs
done

$run src/GenericProofs/VerifiedSemigroup/Examples/Newtype.hs
