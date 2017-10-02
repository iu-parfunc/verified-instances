{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--prune-unsorted"  @-}

module List where

-- import GHC.Classes.VerifiedEq
import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ data List [llen] = Nil | Cons { x :: a , xs :: List a } @-}
data List a = Nil | Cons a (List a)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil = 0
llen (Cons _ xs) = 1 + llen xs

{-@ axiomatize eqList @-}
eqList :: Eq a => List a -> List a -> Bool
eqList Nil Nil = True
eqList (Cons x xs) (Cons y ys) = if x == y then eqList xs ys else False
eqList _ _ = False

{-@ eqListRefl :: xs:List a -> {eqList xs xs} @-}
eqListRefl :: Eq a => List a -> Proof
eqListRefl xs@Nil =   eqList xs xs
                  ==. True
                  *** QED
eqListRefl (Cons x xs) =   eqList (Cons x xs) (Cons x xs)
                       ==. (if x == x then eqList xs xs else False)
                       ==. eqList xs xs
                       ==. True ? eqListRefl xs
                       *** QED

{-@ eqListSym :: xs:List a -> ys: List a -> {eqList xs ys ==> eqList ys xs} @-}
eqListSym :: Eq a => List a -> List a -> Proof
eqListSym Nil Nil = simpleProof
eqListSym Nil (Cons y ys) =   eqList Nil (Cons y ys)
                          ==. False
                          *** QED
eqListSym (Cons x xs) Nil =   eqList (Cons x xs) Nil
                          ==. False
                          *** QED
eqListSym (Cons x xs) (Cons y ys) =   eqList (Cons x xs) (Cons y ys)
                                  ==. (if x == y then eqList xs ys else False)
                                  ==. (if y == x then eqList xs ys else False)
                                  ==. (if y == x then eqList ys xs else False) ? eqListSym xs ys
                                  ==. eqList (Cons y ys) (Cons x xs)
                                  ==. eqList ys xs
                                  *** QED

{-@ eqListTrans :: xs:List a -> ys:List a -> zs:List a -> {eqList xs ys && eqList ys zs ==> eqList xs zs} @-}
eqListTrans :: Eq a => List a -> List a -> List a -> Proof
eqListTrans Nil Nil Nil = simpleProof
eqListTrans Nil Nil (Cons z zs) = eqList Nil (Cons z zs)
                                ==. True
                                *** QED
eqListTrans Nil (Cons y ys) _zs =   eqList Nil (Cons y ys)
                                ==. False
                                *** QED
eqListTrans (Cons x xs) Nil _zs =   eqList (Cons x xs) Nil
                                ==. False
                                *** QED
eqListTrans (Cons _ _) (Cons y ys) Nil =   eqList (Cons y ys) Nil
                                       ==. False
                                       *** QED
eqListTrans (Cons x xs) (Cons y ys) (Cons z zs) =   (eqList (Cons x xs) (Cons y ys) && eqList (Cons y ys) (Cons z zs))
                                                ==. ((if x == y then eqList xs ys else False) && (if y == z then eqList ys zs else False))
                                                ==. (if (x == y && y == z) then (eqList xs ys && eqList ys zs) else False)
                                                ==. (if x == z then eqList xs zs else False) ? eqListTrans xs ys zs
                                                ==. eqList (Cons x xs) (Cons z zs)
                                                *** QED

instance Eq a => Eq (List a) where
  (==) = eqList

-- instance VerifiedEq a => VerifiedEq (List a) where
--   refl = eqListRefl
--   sym = eqListSym
--   trans = eqListTrans

veqList :: Eq a => VerifiedEq (List a)
veqList = VerifiedEq eqList eqListRefl eqListSym eqListTrans

{-@ axiomatize appendList @-}
appendList :: List a -> List a -> List a
appendList Nil ys = ys
appendList (Cons x xs) ys = Cons x (appendList xs ys)

{-@ appendListAssoc :: xs:List a -> ys:List a -> zs:List a
  -> { appendList (appendList xs ys) zs == appendList xs (appendList ys zs) }
@-}
appendListAssoc :: List a -> List a -> List a -> Proof
appendListAssoc Nil ys zs =   appendList (appendList Nil ys) zs
                          ==. appendList ys zs
                          ==. appendList Nil (appendList ys zs)
                          *** QED
appendListAssoc (Cons x xs) ys zs =   appendList (appendList (Cons x xs) ys) zs
                                  ==. appendList (Cons x (appendList xs ys)) zs
                                  ==. Cons x (appendList (appendList xs ys) zs)
                                  ==. Cons x (appendList xs (appendList ys zs)) ? appendListAssoc xs ys zs
                                  ==. appendList (Cons x xs) (appendList ys zs)
                                  *** QED
