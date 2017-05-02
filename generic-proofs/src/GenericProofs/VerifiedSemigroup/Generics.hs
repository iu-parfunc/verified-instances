{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedSemigroup.Generics where

import Language.Haskell.Liquid.ProofCombinators
import GenericProofs.VerifiedSemigroup
import Generics.Deriving.Newtypeless

{-@ axiomatize sappendU1 @-}
sappendU1 :: U1 p -> U1 p -> U1 p
sappendU1 _ _ = U1

{-@ sappendU1Assoc :: x:U1 p -> y:U1 p -> z:U1 p
                   -> { sappendU1 x (sappendU1 y z) == sappendU1 (sappendU1 x y) z }
@-}
sappendU1Assoc :: U1 p -> U1 p -> U1 p -> Proof
sappendU1Assoc x y z
  =   sappendU1 x (sappendU1 y z)
  ==. U1
  ==. sappendU1 (sappendU1 x y) z
  *** QED

vsemigroupU1 :: VerifiedSemigroup (U1 p)
vsemigroupU1 = VerifiedSemigroup sappendU1 sappendU1Assoc

{-@ axiomatize sappendProd @-}
sappendProd :: (f p -> f p -> f p) -> (g p -> g p -> g p)
            -> Product f g p -> Product f g p -> Product f g p
sappendProd sappendFP sappendGP (Product fp1 gp1) (Product fp2 gp2)
  = Product (sappendFP fp1 fp2) (sappendGP gp1 gp2)

{-@ sappendProdAssoc :: sappendFP:(f p -> f p -> f p)
                     -> sappendFPAssoc:(a:(f p) -> b:(f p) -> c:(f p) -> { sappendFP a (sappendFP b c) == sappendFP (sappendFP a b) c })
                     -> sappendGP:(g p -> g p -> g p)
                     -> sappendGPAssoc:(a:(g p) -> b:(g p) -> c:(g p) -> { sappendGP a (sappendGP b c) == sappendGP (sappendGP a b) c })
                     -> x:Product f g p
                     -> y:Product f g p
                     -> z:Product f g p
                     -> { sappendProd sappendFP sappendGP x (sappendProd sappendFP sappendGP y z) == sappendProd sappendFP sappendGP (sappendProd sappendFP sappendGP x y) z }
@-}
sappendProdAssoc :: (f p -> f p -> f p)
                 -> (f p -> f p -> f p -> Proof)
                 -> (g p -> g p -> g p)
                 -> (g p -> g p -> g p -> Proof)
                 -> Product f g p
                 -> Product f g p
                 -> Product f g p
                 -> Proof
sappendProdAssoc sappendFP sappendFPAssoc sappendGP sappendGPAssoc
                 x@(Product fp1 gp1) y@(Product fp2 gp2) z@(Product fp3 gp3)
  =   sappendProd sappendFP sappendGP x (sappendProd sappendFP sappendGP y z)
  ==. sappendProd sappendFP sappendGP x (Product (sappendFP fp2 fp3) (sappendGP gp2 gp3))
  ==. Product (sappendFP fp1 (sappendFP fp2 fp3)) (sappendGP gp1 (sappendGP gp2 gp3))
  ==. Product (sappendFP (sappendFP fp1 fp2) fp3) (sappendGP gp1 (sappendGP gp2 gp3)) ? sappendFPAssoc fp1 fp2 fp3
  ==. Product (sappendFP (sappendFP fp1 fp2) fp3) (sappendGP (sappendGP gp1 gp2) gp3) ? sappendGPAssoc gp1 gp2 gp3
  ==. sappendProd sappendFP sappendGP (Product (sappendFP fp1 fp2) (sappendGP gp1 gp2)) z
  ==. sappendProd sappendFP sappendGP (sappendProd sappendFP sappendGP x y) z
  *** QED
