{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}

module Data.VerifiedMonad.Instances.List where

import Data.VerifiedMonad
import Language.Haskell.Liquid.ProofCombinators

{-@ data List [lengthList] = Nil | Cons { x :: a, xs :: List a } @-}
data List a = Nil | Cons a (List a)

{-@ measure lengthList @-}
{-@ lengthList :: List a -> Nat @-}
lengthList :: List a -> Int
lengthList Nil         = 0
lengthList (Cons x xs) = 1 + lengthList xs

{-@ axiomatize returnList @-}
returnList :: a -> List a
returnList x = Cons x Nil

{-@ axiomatize appendList @-}
appendList :: List a -> List a -> List a
appendList Nil ys         = ys
appendList ys Nil         = ys
appendList (Cons x xs) ys = Cons x (appendList xs ys)

{-@ appendListNil :: xs:List a -> { appendList xs Nil == xs } @-}
appendListNil :: List a -> Proof
appendListNil Nil = appendList Nil Nil ==. Nil *** QED
appendListNil (Cons x xs) = appendList (Cons x xs) Nil
                        ==. Cons x (appendList xs Nil)
                        ==. Cons x xs ? appendListNil xs
                        *** QED

{-@ axiomatize bindList @-}
bindList :: List a -> (a -> List b) -> List b
bindList Nil f         = Nil
bindList (Cons x xs) f = appendList (f x) (bindList xs f)

{-@ returnListLIdent :: x:a -> f:(a -> List b) -> { bindList (returnList x) f == f x } @-}
returnListLIdent :: a -> (a -> List b) -> Proof
returnListLIdent x f = bindList (returnList x) f
                   ==. bindList (Cons x Nil) f
                   ==. appendList (f x) (bindList Nil f)
                   ==. appendList (f x) Nil
                   ==. f x ? appendListNil (f x)
                   *** QED

{-@ returnListRIdent :: f:List a -> { bindList f returnList == f } @-}
returnListRIdent :: List a -> Proof
returnListRIdent Nil = bindList Nil returnList ==. Nil *** QED
returnListRIdent (Cons x xs) = bindList (Cons x xs) returnList
                           ==. appendList (returnList x) (bindList xs returnList)
                           ==. appendList (Cons x Nil) (bindList xs returnList)
                           ==. appendList (Cons x Nil) xs ? returnListRIdent xs
                           ==. Cons x (appendList Nil xs)
                           ==. Cons x xs
                           *** QED

{-@ bindListAssoc :: f:List a -> g:(a -> List b) -> h:(b -> List c)
                  -> { bindList f (\x:a -> bindList (g x) h) == bindList (bindList f g) h }
@-}
bindListAssoc :: List a -> (a -> List b) -> (b -> List c) -> Proof
bindListAssoc Nil g h =
      bindList Nil (\x -> bindList (g x) h)
  ==. Nil
  ==. bindList (bindList Nil g) h
  *** QED
bindListAssoc (Cons x xs) g h =
      bindList (Cons x xs) (\x -> bindList (g x) h)
  ==. appendList ((\x -> bindList (g x) h) x) (bindList xs (\x -> bindList (g x) h))
  ==. appendList (bindList (g x) h) (bindList xs (\x -> bindList (g x) h))
  ==. appendList (bindList (g x) h) (bindList (bindList xs g) h) ? bindListAssoc xs g h
  ==. bindList (appendList (g x) (bindList xs g)) h ? appendBindComm (g x) (bindList xs g) h
  ==. bindList (bindList (Cons x xs) g) h
  *** QED

{-@
appendAssoc :: xs:List a -> ys:List a -> zs:List a
            -> { appendList xs (appendList ys zs) == appendList (appendList xs ys) zs }
@-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc Nil ys zs =
      appendList Nil (appendList ys zs)
  ==. appendList ys zs
  ==. appendList (appendList Nil ys) zs
  *** QED
appendAssoc (Cons x xs) ys zs =
      appendList (Cons x xs) (appendList ys zs)
  ==. Cons x (appendList xs (appendList ys zs))
  ==. Cons x (appendList (appendList xs ys) zs) ? appendAssoc xs ys zs
  ==. appendList (Cons x (appendList xs ys)) zs
  ==. appendList (appendList (Cons x xs) ys) zs
  *** QED

{-@
appendBindComm :: xs:List a -> ys:List a -> f:(a -> List b)
               -> { appendList (bindList xs f) (bindList ys f) == bindList (appendList xs ys) f }
@-}
appendBindComm :: List a -> List a -> (a -> List b) -> Proof
appendBindComm Nil ys f =
      appendList (bindList Nil f) (bindList ys f)
  ==. appendList Nil (bindList ys f)
  ==. bindList ys f
  ==. bindList (appendList Nil ys) f
  *** QED
appendBindComm (Cons x xs) ys f =
      appendList (bindList (Cons x xs) f) (bindList ys f)
  ==. appendList (appendList (f x) (bindList xs f)) (bindList ys f)
  ==. appendList (f x) (appendList (bindList xs f) (bindList ys f))
      ? appendAssoc (f x) (bindList xs f) (bindList ys f)
  ==. appendList (f x) (bindList (appendList xs ys) f)
      ? appendBindComm xs ys f
  ==. bindList (Cons x (appendList xs ys)) f
  ==. bindList (appendList (Cons x xs) ys) f
  *** QED
