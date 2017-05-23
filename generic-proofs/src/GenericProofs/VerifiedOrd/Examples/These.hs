{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}

module GenericProofs.VerifiedOrd.Examples.These
  ( These(..)
  , RepThese
  , toThese
  , fromThese
  , tofThese
  , fotThese
  , isoThese
  , vordThese
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data These a b = This a | That b | These { a :: a, b :: b } @-}
data These a b = This a | That b | These a b deriving (Eq)

data D1These
data C1_0This
data C1_1That
data C1_2These

type RepThese a b = D1 D1These (Sum (C1 C1_0This (S1 NoSelector (Rec0 a)))
                                    (Sum (C1 C1_1That (S1 NoSelector (Rec0 b)))
                                         (C1 C1_2These (Product (S1 NoSelector (Rec0 a))
                                                                (S1 NoSelector (Rec0 b))))))

{-@ axiomatize fromThese @-}
fromThese :: These a b -> RepThese a b x
fromThese (This x)    = M1 (L1 (M1 (M1 (K1 x))))
fromThese (That y)    = M1 (R1 (L1 (M1 (M1 (K1 y)))))
fromThese (These x y) = M1 (R1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 y))))))

{-@ axiomatize toThese @-}
toThese :: RepThese a b x -> These a b
toThese (M1 (L1 (M1 (M1 (K1 x)))))                            = This x
toThese (M1 (R1 (L1 (M1 (M1 (K1 y))))))                       = That y
toThese (M1 (R1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 y))))))) = These x y

{-@ tofThese :: a:These a b
             -> { toThese (fromThese a) == a }
@-}
tofThese :: These a b -> Proof
tofThese (This x)    = toThese (fromThese (This x)) ==. toThese (M1 (L1 (M1 (M1 (K1 x))))) *** QED
tofThese (That y)    = toThese (fromThese (That y)) ==. toThese (M1 (R1 (L1 (M1 (M1 (K1 y)))))) *** QED
tofThese (These x y) = toThese (fromThese (These x y)) ==. toThese (M1 (R1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 y))))))) *** QED

{-@ fotThese :: a:RepThese a b x
             -> { fromThese (toThese a) == a }
@-}
fotThese :: RepThese a b x -> Proof
fotThese (M1 (L1 (M1 (M1 (K1 x)))))                            = fromThese (toThese (M1 (L1 (M1 (M1 (K1 x)))))) ==. fromThese (This x) *** QED
fotThese (M1 (R1 (L1 (M1 (M1 (K1 y))))))                       = fromThese (toThese (M1 (R1 (L1 (M1 (M1 (K1 y))))))) ==. fromThese (That y) *** QED
fotThese (M1 (R1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 y))))))) = fromThese (toThese (M1 (R1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 y)))))))) ==. fromThese (These x y) *** QED

isoThese :: Iso (These a b) (RepThese a b x)
isoThese = Iso fromThese toThese fotThese tofThese

-- $(deriveIso "RepThese"
--             "toThese" "fromThese"
--             "tofThese" "fotThese"
--             "isoThese"
--             ''These)

vordThese :: (Eq a, Eq b) => VerifiedOrd a -> VerifiedOrd b -> VerifiedOrd (These a b)
vordThese vorda vordb =
    vordIso (isoSym isoThese) $
    vordM1 $
    vordSum
        (vordM1 $ vordM1 $ vordK1 vorda)
        (vordSum
             (vordM1 $ vordM1 $ vordK1 vordb)
             (vordM1 $ vordProd (vordM1 $ vordK1 vorda)
                                (vordM1 $ vordK1 vordb)))
