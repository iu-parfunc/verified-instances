{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Unit where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics

import Generics.Deriving.Newtypeless.Base.Internal

data MyUnit = MyUnit

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

veqMyUnit :: VerifiedEq MyUnit
veqMyUnit = veqIso (isoSym isoMyUnit) $ veqM1 $ veqM1 veqU1
