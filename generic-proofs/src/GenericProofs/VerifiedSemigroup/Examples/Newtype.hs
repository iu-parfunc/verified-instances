{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedSemigroup.Examples.Newtype
  ( WrapUnit(..)
  , toWrapUnit
  , fromWrapUnit
  , tofWrapUnit
  , fotWrapUnit
  , isoWrapUnit
  , vsemigroupWrapUnit
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedSemigroup
import GenericProofs.VerifiedSemigroup.Generics
import GenericProofs.VerifiedSemigroup.Instances

import Generics.Deriving.Newtypeless.Base.Internal

-- Morally a newtype, but in practice, not.
data WrapUnit = WrapUnit { runMyUnit :: Unit }

{-@ axiomatize fromWrapUnit @-}
{-@ axiomatize toWrapUnit @-}
{-@ tofWrapUnit :: a:WrapUnit
                -> { toWrapUnit (fromWrapUnit a) == a }
@-}
{-@ fotWrapUnit :: a:RepWrapUnit x
                -> { fromWrapUnit (toWrapUnit a) == a }
@-}
$(deriveIso "RepWrapUnit"
            "toWrapUnit" "fromWrapUnit"
            "tofWrapUnit" "fotWrapUnit"
            "isoWrapUnit"
            ''WrapUnit)

vsemigroupWrapUnit :: VerifiedSemigroup WrapUnit
vsemigroupWrapUnit = vsemigroupIso (isoSym isoWrapUnit)
                   $ vsemigroupM1
                   $ vsemigroupM1
                   $ vsemigroupM1
                   $ vsemigroupK1 vsemigroupUnit
