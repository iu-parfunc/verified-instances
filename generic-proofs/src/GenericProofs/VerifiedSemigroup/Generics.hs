{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedSemigroup.Generics where

import Language.Haskell.Liquid.ProofCombinators
import GenericProofs.VerifiedSemigroup
import Generics.Deriving.Newtypeless.Base.Internal

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

{-@ axiomatize sappendK1 @-}
sappendK1 :: (c -> c -> c) -> K1 i c p -> K1 i c p -> K1 i c p
sappendK1 sappendC (K1 c1) (K1 c2) = K1 (sappendC c1 c2)

{-@ sappendK1Assoc :: sappendC:(c -> c -> c)
                   -> sappendCAssoc:(i:c -> j:c -> k:c -> { sappendC i (sappendC j k) == sappendC (sappendC i j) k })
                   -> x:K1 i c p
                   -> y:K1 i c p
                   -> z:K1 i c p
                   -> { sappendK1 sappendC x (sappendK1 sappendC y z) == sappendK1 sappendC (sappendK1 sappendC x y) z }
@-}
sappendK1Assoc :: (c -> c -> c) -> (c -> c -> c -> Proof)
               -> K1 i c p -> K1 i c p -> K1 i c p -> Proof
sappendK1Assoc sappendC sappendCAssoc x@(K1 c1) y@(K1 c2) z@(K1 c3)
  =   sappendK1 sappendC x (sappendK1 sappendC y z)
  ==. sappendK1 sappendC x (K1 (sappendC c2 c3))
  ==. K1 (sappendC c1 (sappendC c2 c3))
  ==. K1 (sappendC (sappendC c1 c2) c3) ? sappendCAssoc c1 c2 c3
  ==. sappendK1 sappendC (K1 (sappendC c1 c2)) z
  ==. sappendK1 sappendC (sappendK1 sappendC x y) z
  *** QED

vsemigroupK1 :: VerifiedSemigroup c -> VerifiedSemigroup (K1 i c p)
vsemigroupK1 (VerifiedSemigroup sappendC sappendCAssoc)
  = VerifiedSemigroup (sappendK1      sappendC)
                      (sappendK1Assoc sappendC sappendCAssoc)

{-@ axiomatize sappendM1 @-}
sappendM1 :: (f p -> f p -> f p) -> M1 i c f p -> M1 i c f p -> M1 i c f p
sappendM1 sappendFP (M1 fp1) (M1 fp2) = M1 (sappendFP fp1 fp2)

{-@ sappendM1Assoc :: sappendFP:(f p -> f p -> f p)
                   -> sappendFPAssoc:(i:(f p) -> j:(f p) -> k:(f p) -> { sappendFP i (sappendFP j k) == sappendFP (sappendFP i j) k })
                   -> x:M1 i c f p
                   -> y:M1 i c f p
                   -> z:M1 i c f p
                   -> { sappendM1 sappendFP x (sappendM1 sappendFP y z) == sappendM1 sappendFP (sappendM1 sappendFP x y) z }
@-}
sappendM1Assoc :: (f p -> f p -> f p) -> (f p -> f p -> f p -> Proof)
               -> M1 i c f p -> M1 i c f p -> M1 i c f p -> Proof
sappendM1Assoc sappendFP sappendFPAssoc x@(M1 fp1) y@(M1 fp2) z@(M1 fp3)
  =   sappendM1 sappendFP x (sappendM1 sappendFP y z)
  ==. sappendM1 sappendFP x (M1 (sappendFP fp2 fp3))
  ==. M1 (sappendFP fp1 (sappendFP fp2 fp3))
  ==. M1 (sappendFP (sappendFP fp1 fp2) fp3) ? sappendFPAssoc fp1 fp2 fp3
  ==. sappendM1 sappendFP (M1 (sappendFP fp1 fp2)) z
  ==. sappendM1 sappendFP (sappendM1 sappendFP x y) z
  *** QED

vsemigroupM1 :: VerifiedSemigroup (f p) -> VerifiedSemigroup (M1 i c f p)
vsemigroupM1 (VerifiedSemigroup sappendFP sappendFPAssoc)
  = VerifiedSemigroup (sappendM1      sappendFP)
                      (sappendM1Assoc sappendFP sappendFPAssoc)

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

vsemigroupProd :: VerifiedSemigroup (f p) -> VerifiedSemigroup (g p)
               -> VerifiedSemigroup (Product f g p)
vsemigroupProd (VerifiedSemigroup sappendFP sappendFPAssoc)
               (VerifiedSemigroup sappendGP sappendGPAssoc)
  = VerifiedSemigroup (sappendProd sappendFP sappendGP)
                      (sappendProdAssoc sappendFP sappendFPAssoc
                                        sappendGP sappendGPAssoc)
