{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Maybe
  ( Maybe(..)
  , RepMaybe
  , toMaybe
  , fromMaybe
  , tofMaybe
  , fotMaybe
  , isoMaybe
  , veqMaybe
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

import Prelude hiding (Maybe(..))

{-@ data Maybe a = Nothing | Just a @-}
data Maybe a = Nothing | Just a

{-@ axiomatize fromMaybe @-}
{-@ axiomatize toMaybe @-}
{-@ tofMaybe :: a:Maybe a
             -> { toMaybe (fromMaybe a) == a }
@-}
{-@ fotMaybe :: a:RepMaybe a x
             -> { fromMaybe (toMaybe a) == a }
@-}
$(deriveIso "RepMaybe"
            "toMaybe" "fromMaybe"
            "tofMaybe" "fotMaybe"
            "isoMaybe"
            ''Maybe)

veqMaybe :: VerifiedEq (Maybe Int)
veqMaybe = veqIso (isoSym isoMaybe)
         $ veqM1 $ veqSum (veqM1 veqU1)
                          (veqM1 $ veqM1 $ veqK1 veqInt)
