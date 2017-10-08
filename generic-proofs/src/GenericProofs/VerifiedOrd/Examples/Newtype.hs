{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
module GenericProofs.VerifiedOrd.Examples.Newtype
  ( MyInt(..)
  , RepMyInt
  , toMyInt
  , fromMyInt
  , tofMyInt
  , fotMyInt
  , isoMyInt
  , vordMyInt
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal

-- Morally a newtype, but in practice, not.
data MyInt = MyInt { getMyInt :: Int } deriving (Eq)

{-@ axiomatize fromMyInt @-}
{-@ axiomatize toMyInt @-}
{-@ tofMyInt :: a:MyInt
             -> { toMyInt (fromMyInt a) == a }
@-}
{-@ fotMyInt :: a:RepMyInt x
             -> { fromMyInt (toMyInt a) == a }
@-}
$(deriveIso "RepMyInt"
            "toMyInt" "fromMyInt"
            "tofMyInt" "fotMyInt"
            "isoMyInt"
            ''MyInt)

vordMyInt :: VerifiedOrd MyInt
vordMyInt = vordIso (isoSym isoMyInt) $ vordM1 $ vordM1 $ vordM1 $ vordK1 vordInt
