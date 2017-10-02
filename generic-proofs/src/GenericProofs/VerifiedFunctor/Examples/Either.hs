{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedFunctor.Examples.Either where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedFunctor
import GenericProofs.VerifiedFunctor.Generics

import Generics.Deriving.Newtypeless.Base.Internal

import Prelude hiding (Either(..))

-- Morally a newtype, but in practice, not.
{-@ data Either a b = L a | R b @-}
data Either a b = L a | R b

{-@ axiomatize fromEither @-}
{-@ axiomatize toEither @-}
{-@ tofEither :: a:Either a b
             -> { toEither (fromEither a) == a }
@-}
{-@ fotEither :: a:RepEither a b x
             -> { fromEither (toEither a) == a }
@-}
$(deriveIso1 "RepEither"
             "toEither" "fromEither"
             "tofEither" "fotEither"
             "isoEither"
             ''Either)

vfunctorEither :: VerifiedFunctor (Either a)
vfunctorEither = vfunctorIso (iso1Sym isoEither)
               $ vfunctorM1 $ vfunctorSum (vfunctorM1 $ vfunctorM1 vfunctorK1)
                                          (vfunctorM1 $ vfunctorM1 vfunctorPar1)
{-
veqEither :: VerifiedEq (Either Int Double)
veqEither = veqIso (isoSym isoEither)
          $ veqM1 $ veqSum (veqM1 $ veqM1 $ veqK1 veqInt)
                           (veqM1 $ veqM1 $ veqK1 veqDouble)
-}
