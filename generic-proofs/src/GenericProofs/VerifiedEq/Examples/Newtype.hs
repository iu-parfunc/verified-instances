{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Newtype
  ( MyInt(..)
  , RepMyInt
  , toMyInt
  , fromMyInt
  , tofMyInt
  , fotMyInt
  , isoMyInt
  , veqMyInt
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

-- Morally a newtype, but in practice, not.
{-@ data MyInt = MyInt { getMyInt :: Int } @-}
data MyInt = MyInt { getMyInt :: Int }

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

veqMyInt :: VerifiedEq MyInt
veqMyInt = veqIso (isoSym isoMyInt) $ veqM1 $ veqM1 $ veqM1 $ veqK1 veqInt
