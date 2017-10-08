{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Sum where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data MySum = MyLeft Int | MyRight Double @-}
data MySum = MyLeft Int | MyRight Double

{-@ axiomatize fromMySum @-}
{-@ axiomatize toMySum @-}
{-@ tofMySum :: a:MySum
             -> { toMySum (fromMySum a) == a }
@-}
{-@ fotMySum :: a:RepMySum x
             -> { fromMySum (toMySum a) == a }
@-}
$(deriveIso "RepMySum"
            "toMySum" "fromMySum"
            "tofMySum" "fotMySum"
            "isoMySum"
            ''MySum)

veqMySum :: VerifiedEq MySum
veqMySum = veqIso (isoSym isoMySum) $ veqM1
                                    $ veqSum (veqM1 $ veqM1 $ veqK1 veqInt)
                                             (veqM1 $ veqM1 $ veqK1 veqDouble)
