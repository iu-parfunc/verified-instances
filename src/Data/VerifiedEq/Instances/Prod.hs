{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Data.VerifiedEq.Instances.Prod (veqProd, eqProd) where

import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators
qed _ = ()

{-@ axiomatize eqProd @-}
eqProd :: (a -> a -> Bool) -> (b -> b -> Bool)
       -> (a, b) -> (a, b) -> Bool
eqProd eqa eqb (a1, b1) (a2, b2) =
  eqa a1 a2 && eqb b1 b2
{-# INLINE eqProd #-}

{-@ eqProdRefl :: eqa:(a -> a -> Bool) -> eqaRefl:(x:a -> { eqa x x })
               -> eqb:(b -> b -> Bool) -> eqbRefl:(y:b -> { eqb y y })
               -> p:(a, b)
               -> { eqProd eqa eqb p p }
@-}
eqProdRefl :: (a -> a -> Bool) -> (a -> Proof)
           -> (b -> b -> Bool) -> (b -> Proof)
           -> (a, b) -> Proof
eqProdRefl eqa eqaRefl eqb eqbRefl p@(x, y) =
  [eqaRefl x, eqbRefl y] *** QED

{-@ eqProdSym :: eqa:(a -> a -> Bool) -> eqaSym:(x:a -> y:{a | eqa x y } -> { eqa y x })
              -> eqb:(b -> b -> Bool) -> eqbSym:(x:b -> y:{b | eqb x y } -> { eqb y x })
              -> p:(a, b) -> q:{(a, b) | eqProd eqa eqb p q }
              -> { eqProd eqa eqb q p }
@-}
eqProdSym :: (a -> a -> Bool) -> (a -> a -> Proof)
          -> (b -> b -> Bool) -> (b -> b -> Proof)
          -> (a, b) -> (a, b) -> Proof
eqProdSym eqa eqaSym eqb eqbSym p@(x1, y1) q@(x2, y2) = qed [ eqaSym x1 x2
                                                            , eqbSym y1 y2 ]

{-@ eqProdTrans :: eqa:(a -> a -> Bool) -> eqaTrans:(x:a -> y:a -> z:{a | eqa x y && eqa y z } -> { eqa x z })
                -> eqb:(b -> b -> Bool) -> eqbTrans:(x:b -> y:b -> z:{b | eqb x y && eqb y z } -> { eqb x z })
                -> p:(a, b) -> q:(a, b) -> r:{(a, b) | eqProd eqa eqb p q && eqProd eqa eqb q r }
                -> { eqProd eqa eqb p r }
@-}
eqProdTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
            -> (b -> b -> Bool) -> (b -> b -> b -> Proof)
            -> (a, b) -> (a, b) -> (a, b) -> Proof
eqProdTrans eqa eqaTrans eqb eqbTrans p@(x1, y1) q@(x2, y2) r@(x3, y3) =
 qed [ eqaTrans x1 x2 x3
     , eqbTrans y1 y2 y3 ]



{-@ veqProd :: VerifiedEq a -> VerifiedEq b -> VerifiedEq (a, b) @-}
veqProd :: VerifiedEq a -> VerifiedEq b -> VerifiedEq (a, b)
veqProd (VerifiedEq eqa eqaRefl eqaSym eqaTrans) (VerifiedEq eqb eqbRefl eqbSym eqbTrans) =
  VerifiedEq (eqProd eqa eqb)
             (eqProdRefl eqa eqaRefl eqb eqbRefl)
             (eqProdSym eqa eqaSym eqb eqbSym)
             (eqProdTrans eqa eqaTrans eqb eqbTrans)
