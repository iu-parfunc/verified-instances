{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
module GenericProofs.VerifiedOrd.Examples.Sum where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal

data MySum = MyLeft Int | MyRight Double deriving (Eq)

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

vordMySum :: VerifiedOrd MySum
vordMySum = vordIso (isoSym isoMySum) $ vordM1
                                      $ vordSum (vordM1 $ vordM1 $ vordK1 vordInt)
                                                (vordM1 $ vordM1 $ vordK1 vordDouble)
