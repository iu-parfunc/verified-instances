{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedMonoid.Generics where

import Language.Haskell.Liquid.ProofCombinators
import GenericProofs.VerifiedMonoid
import Generics.Deriving.Newtypeless.Base.Internal

{-@ axiomatize memptyU1 @-}
memptyU1 :: U1 p
memptyU1 = U1

{-@ axiomatize mappendU1 @-}
mappendU1 :: U1 p -> U1 p -> U1 p
mappendU1 _ _ = U1

{-@ lMemptyU1 :: x:U1 p
              -> { mappendU1 memptyU1 x == x }
@-}
lMemptyU1 :: U1 p -> Proof
lMemptyU1 x@U1
  =   mappendU1 memptyU1 x
  ==. U1
  *** QED

{-@ rMemptyU1 :: x:U1 p
              -> { mappendU1 x memptyU1 == x }
@-}
rMemptyU1 :: U1 p -> Proof
rMemptyU1 x@U1
  =   mappendU1 x memptyU1
  ==. U1
  *** QED

{-@ mappendU1Assoc :: x:U1 p -> y:U1 p -> z:U1 p
                   -> { mappendU1 x (mappendU1 y z) == mappendU1 (mappendU1 x y) z }
@-}
mappendU1Assoc :: U1 p -> U1 p -> U1 p -> Proof
mappendU1Assoc x y z
  =   mappendU1 x (mappendU1 y z)
  ==. U1
  ==. mappendU1 (mappendU1 x y) z
  *** QED

vmonoidU1 :: VerifiedMonoid (U1 p)
vmonoidU1 = VerifiedMonoid mappendU1 mappendU1Assoc memptyU1 lMemptyU1 rMemptyU1

{-@ axiomatize memptyK1 @-}
memptyK1 :: c -> K1 i c p
memptyK1 memptyC = K1 memptyC

{-@ axiomatize mappendK1 @-}
mappendK1 :: (c -> c -> c) -> K1 i c p -> K1 i c p -> K1 i c p
mappendK1 mappendC (K1 c1) (K1 c2) = K1 (mappendC c1 c2)

{-@ mappendK1Assoc :: mappendC:(c -> c -> c)
                   -> mappendCAssoc:(i:c -> j:c -> k:c -> { mappendC i (mappendC j k) == mappendC (mappendC i j) k })
                   -> x:K1 i c p
                   -> y:K1 i c p
                   -> z:K1 i c p
                   -> { mappendK1 mappendC x (mappendK1 mappendC y z) == mappendK1 mappendC (mappendK1 mappendC x y) z }
@-}
mappendK1Assoc :: (c -> c -> c) -> (c -> c -> c -> Proof)
               -> K1 i c p -> K1 i c p -> K1 i c p -> Proof
mappendK1Assoc mappendC mappendCAssoc x@(K1 c1) y@(K1 c2) z@(K1 c3)
  =   mappendK1 mappendC x (mappendK1 mappendC y z)
  ==. mappendK1 mappendC x (K1 (mappendC c2 c3))
  ==. K1 (mappendC c1 (mappendC c2 c3))
  ==. K1 (mappendC (mappendC c1 c2) c3) ? mappendCAssoc c1 c2 c3
  ==. mappendK1 mappendC (K1 (mappendC c1 c2)) z
  ==. mappendK1 mappendC (mappendK1 mappendC x y) z
  *** QED

{-@ lMemptyK1 :: memptyC:c
              -> mappendC:(c -> c -> c)
              -> lMemptyC:(x:c -> { mappendC memptyC x == x })
              -> x:K1 i c p
              -> { mappendK1 mappendC (memptyK1 memptyC) x == x }
@-}
lMemptyK1 :: c
          -> (c -> c -> c)
          -> (c -> Proof)
          -> K1 i c p
          -> Proof
lMemptyK1 memptyC mappendC lMemptyC x@(K1 c)
  =   mappendK1 mappendC (memptyK1 memptyC) x
  ==. mappendK1 mappendC (K1 memptyC) x
  ==. K1 (mappendC memptyC c)
  ==. K1 c ? lMemptyC c
  ==. x
  *** QED

{-@ rMemptyK1 :: memptyC:c
              -> mappendC:(c -> c -> c)
              -> rMemptyC:(x:c -> { mappendC x memptyC == x })
              -> x:K1 i c p
              -> { mappendK1 mappendC x (memptyK1 memptyC) == x }
@-}
rMemptyK1 :: c
          -> (c -> c -> c)
          -> (c -> Proof)
          -> K1 i c p
          -> Proof
rMemptyK1 memptyC mappendC rMemptyC x@(K1 c)
  =   mappendK1 mappendC x (memptyK1 memptyC)
  ==. mappendK1 mappendC x (K1 memptyC)
  ==. K1 (mappendC c memptyC)
  ==. K1 c ? rMemptyC c
  ==. x
  *** QED

vmonoidK1 :: VerifiedMonoid c -> VerifiedMonoid (K1 i c p)
vmonoidK1 (VerifiedMonoid mappendC mappendCAssoc memptyC lMemptyC rMemptyC)
  = VerifiedMonoid (mappendK1      mappendC)
                   (mappendK1Assoc mappendC mappendCAssoc)
                   (memptyK1       memptyC)
                   (lMemptyK1      memptyC mappendC lMemptyC)
                   (rMemptyK1      memptyC mappendC rMemptyC)

{-@ axiomatize memptyM1 @-}
memptyM1 :: f p -> M1 i c f p
memptyM1 memptyFP = M1 memptyFP

{-@ axiomatize mappendM1 @-}
mappendM1 :: (f p -> f p -> f p) -> M1 i c f p -> M1 i c f p -> M1 i c f p
mappendM1 mappendFP (M1 fp1) (M1 fp2) = M1 (mappendFP fp1 fp2)

{-@ mappendM1Assoc :: mappendFP:(f p -> f p -> f p)
                   -> mappendFPAssoc:(i:(f p) -> j:(f p) -> k:(f p) -> { mappendFP i (mappendFP j k) == mappendFP (mappendFP i j) k })
                   -> x:M1 i c f p
                   -> y:M1 i c f p
                   -> z:M1 i c f p
                   -> { mappendM1 mappendFP x (mappendM1 mappendFP y z) == mappendM1 mappendFP (mappendM1 mappendFP x y) z }
@-}
mappendM1Assoc :: (f p -> f p -> f p) -> (f p -> f p -> f p -> Proof)
               -> M1 i c f p -> M1 i c f p -> M1 i c f p -> Proof
mappendM1Assoc mappendFP mappendFPAssoc x@(M1 fp1) y@(M1 fp2) z@(M1 fp3)
  =   mappendM1 mappendFP x (mappendM1 mappendFP y z)
  ==. mappendM1 mappendFP x (M1 (mappendFP fp2 fp3))
  ==. M1 (mappendFP fp1 (mappendFP fp2 fp3))
  ==. M1 (mappendFP (mappendFP fp1 fp2) fp3) ? mappendFPAssoc fp1 fp2 fp3
  ==. mappendM1 mappendFP (M1 (mappendFP fp1 fp2)) z
  ==. mappendM1 mappendFP (mappendM1 mappendFP x y) z
  *** QED

{-@ lMemptyM1 :: memptyFP:f p
              -> mappendFP:(f p -> f p -> f p)
              -> lMemptyFP:(x:(f p) -> { mappendFP memptyFP x == x })
              -> x:M1 i c f p
              -> { mappendM1 mappendFP (memptyM1 memptyFP) x == x }
@-}
lMemptyM1 :: f p
          -> (f p -> f p -> f p)
          -> (f p -> Proof)
          -> M1 i c f p
          -> Proof
lMemptyM1 memptyFP mappendFP lMemptyFP x@(M1 fp)
  =   mappendM1 mappendFP (memptyM1 memptyFP) x
  ==. mappendM1 mappendFP (M1 memptyFP) x
  ==. M1 (mappendFP memptyFP fp)
  ==. M1 fp ? lMemptyFP fp
  ==. x
  *** QED

{-@ rMemptyM1 :: memptyFP:f p
              -> mappendFP:(f p -> f p -> f p)
              -> rMemptyFP:(x:(f p) -> { mappendFP x memptyFP == x })
              -> x:M1 i c f p
              -> { mappendM1 mappendFP x (memptyM1 memptyFP) == x }
@-}
rMemptyM1 :: f p
          -> (f p -> f p -> f p)
          -> (f p -> Proof)
          -> M1 i c f p
          -> Proof
rMemptyM1 memptyFP mappendFP rMemptyFP x@(M1 fp)
  =   mappendM1 mappendFP x (memptyM1 memptyFP)
  ==. mappendM1 mappendFP x (M1 memptyFP)
  ==. M1 (mappendFP fp memptyFP)
  ==. M1 fp ? rMemptyFP fp
  ==. x
  *** QED

vmonoidM1 :: VerifiedMonoid (f p) -> VerifiedMonoid (M1 i c f p)
vmonoidM1 (VerifiedMonoid mappendFP mappendFPAssoc memptyFP lMemptyFP rMemptyFP)
  = VerifiedMonoid (mappendM1      mappendFP)
                   (mappendM1Assoc mappendFP mappendFPAssoc)
                   (memptyM1       memptyFP)
                   (lMemptyM1      memptyFP mappendFP lMemptyFP)
                   (rMemptyM1      memptyFP mappendFP rMemptyFP)

{-@ axiomatize mappendProd @-}
mappendProd :: (f p -> f p -> f p) -> (g p -> g p -> g p)
            -> Product f g p -> Product f g p -> Product f g p
mappendProd mappendFP mappendGP (Product fp1 gp1) (Product fp2 gp2)
  = Product (mappendFP fp1 fp2) (mappendGP gp1 gp2)

{-@ axiomatize memptyProd @-}
memptyProd :: f p -> g p -> Product f g p
memptyProd memptyFP memptyGP = Product memptyFP memptyGP

{-@ mappendProdAssoc :: mappendFP:(f p -> f p -> f p)
                     -> mappendFPAssoc:(a:(f p) -> b:(f p) -> c:(f p) -> { mappendFP a (mappendFP b c) == mappendFP (mappendFP a b) c })
                     -> mappendGP:(g p -> g p -> g p)
                     -> mappendGPAssoc:(a:(g p) -> b:(g p) -> c:(g p) -> { mappendGP a (mappendGP b c) == mappendGP (mappendGP a b) c })
                     -> x:Product f g p
                     -> y:Product f g p
                     -> z:Product f g p
                     -> { mappendProd mappendFP mappendGP x (mappendProd mappendFP mappendGP y z) == mappendProd mappendFP mappendGP (mappendProd mappendFP mappendGP x y) z }
@-}
mappendProdAssoc :: (f p -> f p -> f p)
                 -> (f p -> f p -> f p -> Proof)
                 -> (g p -> g p -> g p)
                 -> (g p -> g p -> g p -> Proof)
                 -> Product f g p
                 -> Product f g p
                 -> Product f g p
                 -> Proof
mappendProdAssoc mappendFP mappendFPAssoc mappendGP mappendGPAssoc
                 x@(Product fp1 gp1) y@(Product fp2 gp2) z@(Product fp3 gp3)
  =   mappendProd mappendFP mappendGP x (mappendProd mappendFP mappendGP y z)
  ==. mappendProd mappendFP mappendGP x (Product (mappendFP fp2 fp3) (mappendGP gp2 gp3))
  ==. Product (mappendFP fp1 (mappendFP fp2 fp3)) (mappendGP gp1 (mappendGP gp2 gp3))
  ==. Product (mappendFP (mappendFP fp1 fp2) fp3) (mappendGP gp1 (mappendGP gp2 gp3)) ? mappendFPAssoc fp1 fp2 fp3
  ==. Product (mappendFP (mappendFP fp1 fp2) fp3) (mappendGP (mappendGP gp1 gp2) gp3) ? mappendGPAssoc gp1 gp2 gp3
  ==. mappendProd mappendFP mappendGP (Product (mappendFP fp1 fp2) (mappendGP gp1 gp2)) z
  ==. mappendProd mappendFP mappendGP (mappendProd mappendFP mappendGP x y) z
  *** QED

{-@ lMemptyProd :: mappendFP:(f p -> f p -> f p)
                -> mappendGP:(g p -> g p -> g p)
                -> memptyFP:(f p)
                -> memptyGP:(g p)
                -> lMemptyFP:(x:(f p) -> { mappendFP memptyFP x == x })
                -> lMemptyGP:(x:(g p) -> { mappendGP memptyGP x == x })
                -> x:Product f g p
                -> { mappendProd mappendFP mappendGP (memptyProd memptyFP memptyGP) x == x }
@-}
lMemptyProd :: (f p -> f p -> f p)
            -> (g p -> g p -> g p)
            -> f p
            -> g p
            -> (f p -> Proof)
            -> (g p -> Proof)
            -> Product f g p
            -> Proof
lMemptyProd mappendFP mappendGP memptyFP memptyGP lMemptyFP lMemptyGP x@(Product fp gp)
  =   mappendProd mappendFP mappendGP (memptyProd memptyFP memptyGP) x
  ==. mappendProd mappendFP mappendGP (Product memptyFP memptyGP) x
  ==. Product (mappendFP memptyFP fp) (mappendGP memptyGP gp)
  ==. Product fp (mappendGP memptyGP gp) ? lMemptyFP fp
  ==. Product fp gp ? lMemptyGP gp
  ==. x
  *** QED

{-@ rMemptyProd :: mappendFP:(f p -> f p -> f p)
                -> mappendGP:(g p -> g p -> g p)
                -> memptyFP:(f p)
                -> memptyGP:(g p)
                -> rMemptyFP:(x:(f p) -> { mappendFP x memptyFP == x })
                -> rMemptyGP:(x:(g p) -> { mappendGP x memptyGP == x })
                -> x:Product f g p
                -> { mappendProd mappendFP mappendGP x (memptyProd memptyFP memptyGP) == x }
@-}
rMemptyProd :: (f p -> f p -> f p)
            -> (g p -> g p -> g p)
            -> f p
            -> g p
            -> (f p -> Proof)
            -> (g p -> Proof)
            -> Product f g p
            -> Proof
rMemptyProd mappendFP mappendGP memptyFP memptyGP rMemptyFP rMemptyGP x@(Product fp gp)
  =   mappendProd mappendFP mappendGP x (memptyProd memptyFP memptyGP)
  ==. mappendProd mappendFP mappendGP x (Product memptyFP memptyGP)
  ==. Product (mappendFP fp memptyFP) (mappendGP gp memptyGP)
  ==. Product fp (mappendGP gp memptyGP) ? rMemptyFP fp
  ==. Product fp gp ? rMemptyGP gp
  ==. x
  *** QED

vmonoidProd :: VerifiedMonoid (f p) -> VerifiedMonoid (g p)
            -> VerifiedMonoid (Product f g p)
vmonoidProd (VerifiedMonoid mappendFP mappendFPAssoc memptyFP lMemptyFP rMemptyFP)
            (VerifiedMonoid mappendGP mappendGPAssoc memptyGP lMemptyGP rMemptyGP)
  = VerifiedMonoid (mappendProd mappendFP mappendGP)
                   (mappendProdAssoc mappendFP mappendFPAssoc mappendGP mappendGPAssoc)
                   (memptyProd memptyFP memptyGP)
                   (lMemptyProd mappendFP mappendGP memptyFP memptyGP lMemptyFP lMemptyGP)
                   (rMemptyProd mappendFP mappendGP memptyFP memptyGP rMemptyFP rMemptyGP)
