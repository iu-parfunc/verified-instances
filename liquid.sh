#!/usr/bin/env bash

stack exec -- liquid --no-adt -i src src/Data/VerifiedEq.hs
stack exec -- liquid --no-adt -i src src/Data/Iso.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedEq/Instances/Contra.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedEq/Instances/Generics.hs	--compile-spec
stack exec -- liquid --no-adt -i src src/Data/VerifiedEq/Instances/Iso.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedEq/Instances/Sum.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedEq/Instances/Prod.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedEq/Instances.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedOrd.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedOrd/Instances/Sum.hs
stack exec -- liquid --no-adt -i src src/Data/VerifiedOrd/Instances/Prod.hs