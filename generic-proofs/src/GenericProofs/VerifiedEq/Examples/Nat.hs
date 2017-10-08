{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module GenericProofs.VerifiedEq.Examples.Nat where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data N = Zero | Succ { pred :: N } @-}
data N = Zero | Succ N

{-@ axiomatize fromN @-}
{-@ axiomatize toN @-}
{-@ tofN :: a:N -> { toN (fromN a) == a } @-}
{-@ fotN :: a:RepN x -> { fromN (toN a) == a } @-}
$(deriveIso "RepN"
            "toN" "fromN"
            "tofN" "fotN"
            "isoN"
            ''N)

{-@ lazy veqN @-}
veqN :: VerifiedEq N
veqN =
    veqIso
        (isoSym isoN)
        (veqM1 (veqSum (veqM1 veqU1) (veqM1 (veqM1 (veqK1 veqN)))))
