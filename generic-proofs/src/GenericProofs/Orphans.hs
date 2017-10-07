{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.Orphans where

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data M1 i c f p = M1 { unM1 :: (f p) } @-}
{-@ data K1 i c p = K1 { unK1 :: c } @-}
{-@ data Par1 p = Par1 { unPar1 :: p } @-}
{-@ data Rec1 f p = Rec1 { unRec1 :: (f p) } @-}
{-@ data Sum @-}
{-@ data Product @-}
{-@ data Comp1 f g p = Comp1 { unComp1 :: (f (g p)) } @-}
