{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
module GenericProofs.VerifiedOrd.Examples.Unit where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data MyUnit = MyUnit @-}
data MyUnit = MyUnit deriving (Eq)

{-@ axiomatize fromMyUnit @-}
{-@ axiomatize toMyUnit @-}
{-@ tofMyUnit :: a:MyUnit
              -> { toMyUnit (fromMyUnit a) == a }
@-}
{-@ fotMyUnit :: a:RepMyUnit x
              -> { fromMyUnit (toMyUnit a) == a }
@-}
$(deriveIso "RepMyUnit"
            "toMyUnit" "fromMyUnit"
            "tofMyUnit" "fotMyUnit"
            "isoMyUnit"
            ''MyUnit)

vordMyUnit :: VerifiedOrd MyUnit
vordMyUnit = vordIso (isoSym isoMyUnit) $ vordM1 $ vordM1 vordU1
