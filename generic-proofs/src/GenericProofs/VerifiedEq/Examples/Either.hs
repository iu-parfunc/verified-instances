{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Either
  ( Either(..)
  , RepEither
  , toEither
  , fromEither
  , tofEither
  , fotEither
  , isoEither
  , veqEither
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

import Prelude hiding (Either(..))

data Either a b = L a | R b

{-@ axiomatize fromEither @-}
{-@ axiomatize toEither @-}
{-@ tofEither :: a:Either a b
             -> { toEither (fromEither a) == a }
@-}
{-@ fotEither :: a:RepEither a b x
             -> { fromEither (toEither a) == a }
@-}
$(deriveIso "RepEither"
            "toEither" "fromEither"
            "tofEither" "fotEither"
            "isoEither"
            ''Either)

veqEither :: VerifiedEq (Either Int Double)
veqEither = veqIso (isoSym isoEither)
          $ veqM1 $ veqSum (veqM1 $ veqM1 $ veqK1 veqInt)
                           (veqM1 $ veqM1 $ veqK1 veqDouble)
