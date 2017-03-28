{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.Classes where

{-
class Generic a => GenericIso a where
  repIso :: Iso a (Rep a x)

class Generic1 f => Generic1Iso f where
  rep1Iso :: Iso (f a) (Rep1 f a)
-}
