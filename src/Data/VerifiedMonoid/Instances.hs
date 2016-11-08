{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedMonoid.Instances (vmonoidUnit, module X) where

import Data.VerifiedMonoid.Instances.Iso        as X
import Data.VerifiedMonoid.Instances.Prod       as X

import Data.VerifiedMonoid
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize prodUnit @-}
prodUnit :: () -> () -> ()
prodUnit () () = ()

{-@ inline unit @-}
unit :: ()
unit = ()

{-@ prodUnitLIdent :: x:() -> { prodUnit unit x == x } @-}
prodUnitLIdent :: () -> Proof
prodUnitLIdent () = prodUnit () () ==. () *** QED

{-@ prodUnitRIdent :: x:() -> { prodUnit x unit == x } @-}
prodUnitRIdent :: () -> Proof
prodUnitRIdent () = prodUnit () () ==. () *** QED

{-@ prodUnitAssoc :: x:() -> y:() -> z:() -> { prodUnit x (prodUnit y z) == prodUnit (prodUnit x y) z }@-}
prodUnitAssoc :: () -> () -> () -> Proof
prodUnitAssoc () () () =
      prodUnit () (prodUnit () ())
  ==. prodUnit () ()
  ==. prodUnit (prodUnit () ())
  *** QED

vmonoidUnit :: VerifiedMonoid ()
vmonoidUnit = VerifiedMonoid () prodUnit prodUnitLIdent prodUnitRIdent prodUnitAssoc
