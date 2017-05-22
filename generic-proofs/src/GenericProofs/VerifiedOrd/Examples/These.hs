{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
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

{-@ data These = This a | That b | These { a :: a, b :: b } @-}
data These a b = This a | That b | These a b deriving (Eq)

{-@ axiomatize fromThese @-}
{-@ axiomatize toThese @-}
{-@ tofThese :: a:These a b
             -> { toThese (fromThese a) == a }
@-}
{-@ fotThese :: a:RepThese a b x
             -> { fromThese (toThese a) == a }
@-}
$(deriveIso "RepThese"
            "toThese" "fromThese"
            "tofThese" "fotThese"
            "isoThese"
            ''These)

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
