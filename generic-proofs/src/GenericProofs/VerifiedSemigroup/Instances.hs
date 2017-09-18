{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc"     @-}
module GenericProofs.VerifiedSemigroup.Instances (Unit(..), sappendUnit, vsemigroupUnit) where -- (Unit(..), vsemigroupUnit) where

import GenericProofs.VerifiedSemigroup
import Language.Haskell.Liquid.ProofCombinators

{-@ data Unit = Unit @-}
data Unit = Unit

{-@ axiomatize sappendUnit @-}
sappendUnit :: Unit -> Unit -> Unit
sappendUnit _ _ = Unit
{-# INLINE sappendUnit #-}

{-@ sappendUnitAssoc :: a:Unit -> b:Unit -> c:Unit
                     -> { sappendUnit a (sappendUnit b c) == sappendUnit (sappendUnit a b) c }
@-}
sappendUnitAssoc :: Unit -> Unit -> Unit -> Proof
sappendUnitAssoc a b c
  =   sappendUnit a (sappendUnit b c)
  ==. Unit
  ==. sappendUnit (sappendUnit a b) c
  *** QED

vsemigroupUnit :: VerifiedSemigroup Unit
vsemigroupUnit = VerifiedSemigroup sappendUnit sappendUnitAssoc
