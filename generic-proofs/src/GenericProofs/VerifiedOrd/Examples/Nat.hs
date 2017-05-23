{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module GenericProofs.VerifiedOrd.Examples.Nat where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data N = Zero | Succ { pred :: N } @-}
data N = Zero | Succ N deriving (Eq)

{-@ axiomatize fromN @-}
{-@ axiomatize toN @-}
{-@ tofN :: a:N -> { toN (fromN a) == a } @-}
{-@ fotN :: a:RepN x -> { fromN (toN a) == a } @-}
$(deriveIso "RepN"
            "toN" "fromN"
            "tofN" "fotN"
            "isoN"
            ''N)

{-@ lazy vordN @-}
vordN :: VerifiedOrd N
vordN =
    vordIso
        (isoSym isoN)
        (vordM1 (vordSum (vordM1 vordU1) (vordM1 (vordM1 (vordK1 vordN)))))
