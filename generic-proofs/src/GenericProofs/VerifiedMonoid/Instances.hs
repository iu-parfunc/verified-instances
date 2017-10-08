{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--noadt"       @-}
module GenericProofs.VerifiedMonoid.Instances where

import GenericProofs.VerifiedMonoid
import Language.Haskell.Liquid.ProofCombinators

{-@ data Unit = Unit @-}
data Unit = Unit

{-@ axiomatize mappendUnit @-}
mappendUnit :: Unit -> Unit -> Unit
mappendUnit _ _ = Unit
{-# INLINE mappendUnit #-}

{-@ axiomatize memptyUnit @-}
memptyUnit :: Unit
memptyUnit = Unit
{-# INLINE memptyUnit #-}

{-@ mappendUnitAssoc :: a:Unit -> b:Unit -> c:Unit
                     -> { mappendUnit a (mappendUnit b c) == mappendUnit (mappendUnit a b) c }
@-}
mappendUnitAssoc :: Unit -> Unit -> Unit -> Proof
mappendUnitAssoc a b c
  =   mappendUnit a (mappendUnit b c)
  ==. Unit
  ==. mappendUnit (mappendUnit a b) c
  *** QED

{-@ lMemptyUnit :: x:Unit
                -> { mappendUnit memptyUnit x == x }
@-}
lMemptyUnit :: Unit
            -> Proof
lMemptyUnit x@Unit
  =   mappendUnit memptyUnit x
  ==. Unit
  *** QED

{-@ rMemptyUnit :: x:Unit
                -> { mappendUnit x memptyUnit == x }
@-}
rMemptyUnit :: Unit
            -> Proof
rMemptyUnit x@Unit
  =   mappendUnit x memptyUnit
  ==. Unit
  *** QED

vmonoidUnit :: VerifiedMonoid Unit
vmonoidUnit = VerifiedMonoid mappendUnit mappendUnitAssoc memptyUnit lMemptyUnit rMemptyUnit
