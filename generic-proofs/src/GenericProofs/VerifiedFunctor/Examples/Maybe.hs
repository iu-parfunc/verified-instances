{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedFunctor.Examples.Maybe where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedFunctor
import GenericProofs.VerifiedFunctor.Generics

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
$(deriveIso1 "RepMaybe"
             "toMaybe" "fromMaybe"
             "tofMaybe" "fotMaybe"
             "isoMaybe"
             ''Maybe)

vfunctorMaybe :: VerifiedFunctor Maybe
vfunctorMaybe = vfunctorIso (iso1Sym isoMaybe)
              $ vfunctorM1 $ vfunctorSum (vfunctorM1 vfunctorU1)
                                         (vfunctorM1 $ vfunctorM1 vfunctorPar1)
