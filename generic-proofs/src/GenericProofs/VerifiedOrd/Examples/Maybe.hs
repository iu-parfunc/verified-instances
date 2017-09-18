{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
module GenericProofs.VerifiedOrd.Examples.Maybe
  ( Maybe(..)
  , RepMaybe
  , toMaybe
  , fromMaybe
  , tofMaybe
  , fotMaybe
  , isoMaybe
  , vordMaybe
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal

import Prelude                                     hiding (Maybe (..))

{-@ data Maybe a = Nothing | Just a @-}
data Maybe a = Nothing | Just a deriving (Eq)

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

vordMaybe :: VerifiedOrd (Maybe Int)
vordMaybe = vordIso (isoSym isoMaybe)
          $ vordM1 $ vordSum (vordM1 vordU1)
                             (vordM1 $ vordM1 $ vordK1 vordInt)
