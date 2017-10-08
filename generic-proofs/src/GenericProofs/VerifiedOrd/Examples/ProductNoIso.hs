{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}

module GenericProofs.VerifiedOrd.Examples.ProductNoIso where

import Language.Haskell.Liquid.ProofCombinators

{-@ data MyProduct = MyProduct { fld1 :: Int, fld2 :: Double } @-}
data MyProduct = MyProduct Int Double deriving (Eq)

{-@ axiomatize leqMyProd @-}
leqMyProd :: MyProduct -> MyProduct -> Bool
leqMyProd (MyProduct x1 y1) (MyProduct x2 y2) =
  if x1 == x2
    then y1 <= y2
    else x1 <= x2
{-# INLINE leqMyProd #-}

{-@ leqMyProdRefl :: p:MyProduct -> { leqMyProd p p } @-}
leqMyProdRefl :: MyProduct -> Proof
leqMyProdRefl p@(MyProduct x y) =
      leqMyProd p p
  ==. (if x == x then y <= y else x <= x)
  ==. y <= y
  ==. True
  *** QED

{-@ leqMyProdAntisym :: p:MyProduct -> q:MyProduct
                     -> { leqMyProd p q && leqMyProd q p ==> p == q } @-}
leqMyProdAntisym :: MyProduct -> MyProduct -> Proof
leqMyProdAntisym p@(MyProduct x1 y1) q@(MyProduct x2 y2) =
      (leqMyProd p q && leqMyProd q p)
  ==. ((if x1 == x2 then y1 <= y2 else x1 <= x2) && (if x2 == x1 then y2 <= y1 else x2 <= x1))
  ==. (if x1 == x2 then y1 <= y2 && y2 <= y1 else x1 <= x2 && x2 <= x1)
  ==. (if x1 == x2 then y1 == y2 else x1 <= x2 && x2 <= x1)
  ==. (if x1 == x2 then y1 == y2 else x1 == x2)
  ==. (x1 == x2 && y1 == y2)
  ==. (p == q)
  *** QED

{-@ leqMyProdTrans :: p:MyProduct -> q:MyProduct -> r:MyProduct
                   -> { leqMyProd p q && leqMyProd q r ==> leqMyProd p r }
@-}
leqMyProdTrans :: MyProduct -> MyProduct -> MyProduct -> Proof
leqMyProdTrans p@(MyProduct x1 y1) q@(MyProduct x2 y2) r@(MyProduct x3 y3) =
    case x1 == x2 of
      True  -> case x2 == x3 of
        True  ->  (leqMyProd p q && leqMyProd q r)
              ==. (y1 <= y2 && y2 <= y3)
              ==. y1 <= y3
              ==. (if x1 == x3 then y1 <= y3 else x1 <= x3)
              ==. leqMyProd p r
              *** QED
        False ->  (leqMyProd p q && leqMyProd q r)
              ==. (y1 <= y2 && x2 <= x3)
              ==. x1 <= x3
              ==. (if x1 == x3 then y1 <= y3 else x1 <= x3)
              ==. leqMyProd p r
              *** QED
      False -> case x2 == x3 of
        True  ->  (leqMyProd p q && leqMyProd q r)
              ==. (x1 <= x2 && y2 <= y3)
              ==. x1 <= x3
              ==. (if x1 == x3 then y1 <= y3 else x1 <= x3)
              ==. leqMyProd p r
              *** QED
        False -> case x1 == x3 of
          True  ->  (leqMyProd p q && leqMyProd q r)
                ==. (x1 <= x2 && x2 <= x3)
                ==. (x1 <= x2 && x2 <= x1)
                ==. (x1 == x2)
                ==. y1 <= y3
                ==. (if x1 == x3 then y1 <= y3 else x1 <= x3)
                *** QED
          False ->  (leqMyProd p q && leqMyProd q r)
                ==. (x1 <= x2 && x2 <= x3)
                ==. x1 <= x3
                ==. (if x1 == x3 then y1 <= y3 else x1 <= x3)
                ==. leqMyProd p r
                *** QED

{-@ leqMyProdTotal :: p:MyProduct -> q:MyProduct
                   -> { leqMyProd p q || leqMyProd q p }
@-}
leqMyProdTotal :: MyProduct -> MyProduct -> Proof
leqMyProdTotal p@(MyProduct x1 y1) q@(MyProduct x2 y2) =
      (leqMyProd p q || leqMyProd q p)
  ==. ((if x1 == x2 then y1 <= y2 else x1 <= x2) || (if x2 == x1 then y2 <= y1 else x2 <= x1))
  ==. ((if x1 == x2 then y1 <= y2 else x1 <= x2) || (if x1 == x2 then y2 <= y1 else x2 <= x1))
  ==. (if x1 == x2 then y1 <= y2 || y2 <= y1 else x1 <= x2 || x2 <= x1)
  ==. (if x1 == x2 then True else x1 <= x2 || x2 <= x1)
  ==. (if x1 == x2 then True else True)
  ==. True
  *** QED
