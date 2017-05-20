{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Product where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal


{-@ data MyTriple = MyTriple { fld1 :: Int, fld2 :: Double, fld3 :: Int } @-}
data MyTriple = MyTriple Int Double Int

{-@ axiomatize fromMyTriple @-}
{-@ axiomatize toMyTriple @-}
{-@ tofMyTriple :: a:MyTriple
                 -> { toMyTriple (fromMyTriple a) == a }
@-}
{-@ fotMyTriple :: a:RepMyTriple x
                 -> { fromMyTriple (toMyTriple a) == a }
@-}
$(deriveIso "RepMyTriple"
            "toMyTriple" "fromMyTriple"
            "tofMyTriple" "fotMyTriple"
            "isoMyTriple"
            ''MyTriple)

veqMyTriple :: VerifiedEq MyTriple
veqMyTriple = 
    veqIso (isoSym isoMyTriple)
               $ veqM1
               $ veqM1
               $ veqProd (veqM1 $ veqK1 veqInt)
               $ veqProd (veqM1 $ veqK1 veqDouble)
                         (veqM1 $ veqK1 veqInt)

