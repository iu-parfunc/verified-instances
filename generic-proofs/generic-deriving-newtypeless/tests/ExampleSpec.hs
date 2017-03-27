{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ >= 705
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans #-}

module ExampleSpec (main, spec) where

import           Control.Monad (liftM, liftM2)

import           Generics.Deriving.Newtypeless
import           Generics.Deriving.Newtypeless.TH

import           Prelude hiding (Either(..))

import           Test.Hspec (Spec, describe, hspec, it, parallel, shouldBe)

import qualified Text.Read.Lex (Lexeme)

main :: IO ()
main = hspec spec

spec :: Spec
spec = parallel $ do
    describe "[] and Maybe tests" $ do
        it "gshow hList" $
            gshow hList `shouldBe`
                "[1,2,3,4,5,6,7,8,9,10]"

        it "gshow (children maybe2)" $
            gshow (children maybe2) `shouldBe`
                "[]"

        it "gshow (transform (const \"abc\") [])" $
            gshow (transform (const "abc") []) `shouldBe`
                "\"abc\""

        it "gshow (transform double hList)" $
            gshow (transform double hList) `shouldBe`
                "[1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10]"

        it "gshow (geq hList hList)" $
            gshow (geq hList hList) `shouldBe`
                "True"

        it "gshow (geq maybe1 maybe2)" $
            gshow (geq maybe1 maybe2) `shouldBe`
                "False"

        it "gshow (take 5 genum)" $
            gshow (take 5 (genum :: [Maybe Int])) `shouldBe`
                "[Nothing,Just 0,Just -1,Just 1,Just -2]"

        it "gshow (take 15 genum)" $
            gshow (take 15 (genum :: [[Int]])) `shouldBe`
                "[[],[0],[0,0],[-1],[0,0,0],[-1,0],[1],[0,-1],[-1,0,0],[1,0],[-2],[0,0,0,0],[-1,-1],[1,0,0],[-2,0]]"

        it "gshow (range ([0], [1]))" $
            gshow (range ([0], [1::Int])) `shouldBe`
                "[[0],[0,0],[-1],[0,0,0],[-1,0]]"

        it "gshow (inRange ([0], [3,5]) hList)" $
            gshow (inRange ([0], [3,5::Int]) hList) `shouldBe`
                "False"

    describe "Tests for Tree" $ do
        it "gshow tree" $
            gshow tree `shouldBe`
                "Branch 2 Empty (Branch 1 Empty Empty)"

        it "gshow (children tree)" $
            gshow (children tree) `shouldBe`
                "[Empty,Branch 1 Empty Empty]"

        it "gshow (descend (descend (\\_ -> Branch 0 Empty Empty)) tree)" $
            gshow (descend (descend (\_ -> Branch 0 Empty Empty)) tree) `shouldBe`
                "Branch 2 Empty (Branch 1 (Branch 0 Empty Empty) (Branch 0 Empty Empty))"

        it "gshow (context tree [Branch 1 Empty Empty,Empty])" $
            gshow (context tree [Branch 1 Empty Empty,Empty]) `shouldBe`
                "Branch 2 (Branch 1 Empty Empty) Empty"

        it "gshow (transform upgradeTree tree)" $
            gshow (transform upgradeTree tree) `shouldBe`
                "Branch 3 (Branch 0 Empty Empty) (Branch 2 (Branch 0 Empty Empty) (Branch 0 Empty Empty))"

        it "gshow (take 10 genum)" $ do
            gshow (take 10 (genum :: [Tree])) `shouldBe`
                "[Empty,Branch 0 Empty Empty,Branch 0 Empty (Branch 0 Empty Empty),Branch -1 Empty Empty,Branch 0 (Branch 0 Empty Empty) Empty,Branch -1 Empty (Branch 0 Empty Empty),Branch 1 Empty Empty,Branch 0 Empty (Branch 0 Empty (Branch 0 Empty Empty)),Branch -1 (Branch 0 Empty Empty) Empty,Branch 1 Empty (Branch 0 Empty Empty)]"

    describe "Tests for List" $ do
        it "gshow (gmap fromEnum list)" $
            gshow (gmap fromEnum list) `shouldBe`
                "Cons 112 (Cons 113 Nil)"

        it "gshow (gmap gshow listlist)" $
            gshow (gmap gshow listlist) `shouldBe`
                "Cons \"Cons 'p' (Cons 'q' Nil)\" (Cons \"Nil\" Nil)"

        it "gshow list" $
            gshow list `shouldBe`
                "Cons 'p' (Cons 'q' Nil)"

        it "gshow listlist" $
            gshow listlist `shouldBe`
                "Cons (Cons 'p' (Cons 'q' Nil)) (Cons Nil Nil)"

        it "gshow (children list)" $
            gshow (children list) `shouldBe`
                "[Cons 'q' Nil]"

        it "gshow (children listlist)" $
            gshow (children listlist) `shouldBe`
                "[Cons Nil Nil]"

    describe "Tests for Rose" $ do
        it "gshow rose1" $
            gshow rose1 `shouldBe`
                "Rose [1,2] [Rose [3,4] [],Rose [5] []]"

        it "gshow (gmap gshow rose1)" $
            gshow (gmap gshow rose1) `shouldBe`
                "Rose [\"1\",\"2\"] [Rose [\"3\",\"4\"] [],Rose [\"5\"] []]"

    describe "Tests for GRose" $ do
        it "gshow grose1" $
            gshow grose1 `shouldBe`
                "GRose [1,2] [GRose [3] [],GRose [] []]"

        it "gshow (gmap gshow grose1)" $
            gshow (gmap gshow grose1) `shouldBe`
                "GRose [\"1\",\"2\"] [GRose [\"3\"] [],GRose [] []]"

    describe "Tests for Either" $ do
        it "gshow either1" $
            gshow either1 `shouldBe`
                "Left Right 'p'"

        it "gshow (gmap gshow either1)" $
            gshow (gmap gshow either1) `shouldBe`
                "Left Right \"'p'\""

    describe "Tests for Nested" $ do
        it "gshow nested" $
            gshow nested `shouldBe`
                "Nested {value = 1, rec = Nested {value = [2], rec = Nested {value = [[3],[4,5],[]], rec = Leaf}}}"

        it "gshow (gmap gshow nested)" $
            gshow (gmap gshow nested) `shouldBe`
                "Nested {value = \"1\", rec = Nested {value = [\"2\"], rec = Nested {value = [[\"3\"],[\"4\",\"5\"],[]], rec = Leaf}}}"

    describe "Tests for Bush" $ do
        it "gshow bush1" $
            gshow bush1 `shouldBe`
                "BushCons 0 (BushCons (BushCons 1 BushNil) BushNil)"

        it "gshow (gmap gshow bush1)" $
            gshow (gmap gshow bush1) `shouldBe`
                "BushCons \"0\" (BushCons (BushCons \"1\" BushNil) BushNil)"

-------------------------------------------------------------------------------
-- Example: Haskell's lists and Maybe
-------------------------------------------------------------------------------

hList:: [Int]
hList = [1..10]

maybe1, maybe2 :: Maybe (Maybe Char)
maybe1 = Nothing
maybe2 = Just (Just 'p')

double :: [Int] -> [Int]
double []     = []
double (x:xs) = x:x:xs

-------------------------------------------------------------------------------
-- Example: trees of integers (kind *)
-------------------------------------------------------------------------------

data Tree = Empty | Branch Int Tree Tree

instance GShow Tree where
    gshowsPrec = gshowsPrecdefault

instance Uniplate Tree where
  children   = childrendefault
  context    = contextdefault
  descend    = descenddefault
  descendM   = descendMdefault
  transform  = transformdefault
  transformM = transformMdefault

instance GEnum Tree where
    genum = genumDefault

upgradeTree :: Tree -> Tree
upgradeTree Empty          = Branch 0 Empty Empty
upgradeTree (Branch n l r) = Branch (succ n) l r

tree :: Tree
tree = Branch 2 Empty (Branch 1 Empty Empty)

-------------------------------------------------------------------------------
-- Example: lists (kind * -> *)
-------------------------------------------------------------------------------

data List a = Nil | Cons a (List a)

instance GFunctor List where
  gmap = gmapdefault

instance (GShow a) => GShow (List a) where
  gshowsPrec = gshowsPrecdefault

instance (Uniplate a) => Uniplate (List a) where
  children   = childrendefault
  context    = contextdefault
  descend    = descenddefault
  descendM   = descendMdefault
  transform  = transformdefault
  transformM = transformMdefault

list :: List Char
list = Cons 'p' (Cons 'q' Nil)

listlist :: List (List Char)
listlist = Cons list (Cons Nil Nil) -- ["pq",""]

-------------------------------------------------------------------------------
-- Example: Type composition
-------------------------------------------------------------------------------

data Rose a = Rose [a] [Rose a]

instance (GShow a) => GShow (Rose a) where
  gshowsPrec = gshowsPrecdefault

instance GFunctor Rose where
  gmap = gmapdefault

-- Example usage
rose1 :: Rose Int
rose1 = Rose [1,2] [Rose [3,4] [], Rose [5] []]

-------------------------------------------------------------------------------
-- Example: Higher-order kinded datatype, type composition
-------------------------------------------------------------------------------

data GRose f a = GRose (f a) (f (GRose f a))
deriving instance Functor f => Functor (GRose f)

instance (GShow (f a), GShow (f (GRose f a))) => GShow (GRose f a) where
  gshowsPrec = gshowsPrecdefault

instance (Functor f, GFunctor f) => GFunctor (GRose f) where
  gmap = gmapdefault

grose1 :: GRose [] Int
grose1 = GRose [1,2] [GRose [3] [], GRose [] []]

-------------------------------------------------------------------------------
-- Example: Two parameters, nested on other parameter
-------------------------------------------------------------------------------

data Either a b = Left (Either [a] b) | Right b

instance (GShow a, GShow b) => GShow (Either a b) where
  gshowsPrec = gshowsPrecdefault

instance GFunctor (Either a) where
  gmap = gmapdefault

either1 :: Either Int Char
either1 = Left either2

either2 :: Either [Int] Char
either2 = Right 'p'

-------------------------------------------------------------------------------
-- Example: Nested datatype, record selectors
-------------------------------------------------------------------------------

data Nested a = Leaf | Nested { value :: a, rec :: Nested [a] }
  deriving Functor

instance (GShow a) => GShow (Nested a) where
  gshowsPrec = gshowsPrecdefault

instance GFunctor Nested where
  gmap = gmapdefault

nested :: Nested Int
nested = Nested { value = 1, rec = Nested [2] (Nested [[3],[4,5],[]] Leaf) }

-------------------------------------------------------------------------------
-- Example: Nested datatype Bush (minimal)
-------------------------------------------------------------------------------

data Bush a = BushNil | BushCons a (Bush (Bush a)) deriving Functor

instance GFunctor Bush where
  gmap = gmapdefault

instance (GShow a) => GShow (Bush a) where
  gshowsPrec = gshowsPrecdefault

bush1 :: Bush Int
bush1 = BushCons 0 (BushCons (BushCons 1 BushNil) BushNil)

-------------------------------------------------------------------------------
-- Example: Double type composition (minimal)
-------------------------------------------------------------------------------

data Weird a = Weird [[[a]]] deriving Show

instance GFunctor Weird where
  gmap = gmapdefault

--------------------------------------------------------------------------------
-- Temporary tests for TH generation
--------------------------------------------------------------------------------

data Empty a

data (:/:) f a = MyType1Nil
               | MyType1Cons { _myType1Rec :: (f :/: a), _myType2Rec :: MyType2 }
               | MyType1Cons2 (f :/: a) Int a (f a)
               | (f :/: a) :/: MyType2

infixr 5 :!@!:
data GADTSyntax a b where
  GADTPrefix :: d -> c -> GADTSyntax c d
  (:!@!:)    :: e -> f -> GADTSyntax e f

data MyType2 = MyType2 Float ([] :/: Int)

-- Test to see if generated names are unique
data Lexeme = Lexeme

#if MIN_VERSION_template_haskell(2,7,0)
data family MyType3
# if __GLASGOW_HASKELL__ >= 705
  (a :: v) (b :: w) (c :: x)      (d :: y) (e :: z)
# else
  (a :: *) (b :: *) (c :: * -> *) (d :: *) (e :: *)
# endif
newtype instance MyType3 (f p) (f p) f p q = MyType3Newtype q
data    instance MyType3 Bool  ()    f p q = MyType3True | MyType3False
#endif

class GEq a where
  geq :: a -> a -> Bool


class GEq' f where
  geq' :: f a -> f a -> Bool

instance GEq' U1 where
  geq' _ _ = True

instance (GEq c) => GEq' (K1 i c) where
  geq' (K1 a) (K1 b) = geq a b

-- No instances for P or Rec because geq is only applicable to types of kind *

instance (GEq' a) => GEq' (M1 i c a) where
  geq' (M1 a) (M1 b) = geq' a b

instance (GEq' a, GEq' b) => GEq' (a :+: b) where
  geq' (L1 a) (L1 b) = geq' a b
  geq' (R1 a) (R1 b) = geq' a b
  geq' _      _      = False

instance (GEq' a, GEq' b) => GEq' (a :*: b) where
  geq' (a1 :*: b1) (a2 :*: b2) = geq' a1 a2 && geq' b1 b2

geqdefault :: (Generic a, GEq' (Rep a)) => a -> a -> Bool
geqdefault x y = geq' (from x) (from y)

instance GEq a => GEq (Maybe a) where
  geq = geqdefault

instance GEq a => GEq [a] where
  geq = geqdefault

instance GEq Char where
  geq = (==)

instance GEq Int where
  geq = (==)

class GShow a where
  gshowsPrec :: Int -> a -> ShowS
  gshows :: a -> ShowS
  gshows = gshowsPrec 0
  gshow :: a -> String
  gshow x = gshows x ""

instance GShow Int where
  gshowsPrec = showsPrec

instance GShow Bool where
  gshowsPrec = gshowsPrecdefault

instance GShow Char where
  gshowsPrec = showsPrec

instance GShow a => GShow (Maybe a) where
  gshowsPrec = gshowsPrecdefault

intersperse :: a -> [a] -> [a]
intersperse _ []    = []
intersperse _ [h]   = [h]
intersperse x (h:t) = h : x : (intersperse x t)

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPABLE #-}
#endif
    (GShow a) => GShow [a] where
  gshowsPrec _ l =   showChar '['
                   . foldr (.) id
                      (intersperse (showChar ',') (map (gshowsPrec 0) l))
                   . showChar ']'

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPING #-}
#endif
    GShow String where
  gshowsPrec = showsPrec

gshowsPrecdefault :: (Generic a, GShow' (Rep a))
                  => Int -> a -> ShowS
gshowsPrecdefault n = gshowsPrec' Pref n . from

appPrec :: Int
appPrec = 2

data Type = Rec | Tup | Pref | Inf String

class GShow' f where
  gshowsPrec' :: Type -> Int -> f a -> ShowS
  isNullary   :: f a -> Bool
  isNullary = error "generic show (isNullary): unnecessary case"

instance GShow' U1 where
  gshowsPrec' _ _ U1 = id
  isNullary _ = True

instance (GShow c) => GShow' (K1 i c) where
  gshowsPrec' _ n (K1 a) = gshowsPrec n a
  isNullary _ = False

-- No instances for P or Rec because gshow is only applicable to types of kind *

instance (GShow' a, Constructor c) => GShow' (M1 C c a) where
  gshowsPrec' _ n c@(M1 x) =
    case fixity of
      Prefix    -> showParen (n > appPrec && not (isNullary x))
                    ( showString (conName c)
                    . if (isNullary x) then id else showChar ' '
                    . showBraces t (gshowsPrec' t appPrec x))
      Infix _ m -> showParen (n > m) (showBraces t (gshowsPrec' t m x))
      where fixity = conFixity c
            t = if (conIsRecord c) then Rec else
                  case (conIsTuple c) of
                    True -> Tup
                    False -> case fixity of
                                Prefix    -> Pref
                                Infix _ _ -> Inf (show (conName c))
            showBraces :: Type -> ShowS -> ShowS
            showBraces Rec     p = showChar '{' . p . showChar '}'
            showBraces Tup     p = showChar '(' . p . showChar ')'
            showBraces Pref    p = p
            showBraces (Inf _) p = p

            conIsTuple :: C1 c f p -> Bool
            conIsTuple y = tupleName (conName y) where
              tupleName ('(':',':_) = True
              tupleName _           = False

instance (Selector s, GShow' a) => GShow' (M1 S s a) where
  gshowsPrec' t n s@(M1 x) | selName s == "" = --showParen (n > appPrec)
                                                 (gshowsPrec' t n x)
                           | otherwise       =   showString (selName s)
                                               . showString " = "
                                               . gshowsPrec' t 0 x
  isNullary (M1 x) = isNullary x

instance (GShow' a) => GShow' (M1 D d a) where
  gshowsPrec' t n (M1 x) = gshowsPrec' t n x

instance (GShow' a, GShow' b) => GShow' (a :+: b) where
  gshowsPrec' t n (L1 x) = gshowsPrec' t n x
  gshowsPrec' t n (R1 x) = gshowsPrec' t n x

instance (GShow' a, GShow' b) => GShow' (a :*: b) where
  gshowsPrec' t@Rec     n (a :*: b) =
    gshowsPrec' t n     a . showString ", " . gshowsPrec' t n     b
  gshowsPrec' t@(Inf s) n (a :*: b) =
    gshowsPrec' t n     a . showString s    . gshowsPrec' t n     b
  gshowsPrec' t@Tup     n (a :*: b) =
    gshowsPrec' t n     a . showChar ','    . gshowsPrec' t n     b
  gshowsPrec' t@Pref    n (a :*: b) =
    gshowsPrec' t (n+1) a . showChar ' '    . gshowsPrec' t (n+1) b

  -- If we have a product then it is not a nullary constructor
  isNullary _ = False

class (Ord a) => GIx a where
    -- | The list of values in the subrange defined by a bounding pair.
    range               :: (a,a) -> [a]
    -- | The position of a subscript in the subrange.
    index               :: (a,a) -> a -> Int
    -- | Returns 'True' the given subscript lies in the range defined
    -- the bounding pair.
    inRange             :: (a,a) -> a -> Bool

rangeDefault :: (GEq a, Generic a, Enum' (Rep a))
             => (a,a) -> [a]
rangeDefault = t (map to enum') where
  t l (x,y) =
    case (findIndex (geq x) l, findIndex (geq y) l) of
      (Nothing, _)     -> error "rangeDefault: no corresponding index"
      (_, Nothing)     -> error "rangeDefault: no corresponding index"
      (Just i, Just j) -> take (j-i) (drop i l)

indexDefault :: (GEq a, Generic a, Enum' (Rep a))
             => (a,a) -> a -> Int
indexDefault = t (map to enum') where
  t l (x,y) z =
    case (findIndex (geq x) l, findIndex (geq y) l) of
      (Nothing, _)     -> error "indexDefault: no corresponding index"
      (_, Nothing)     -> error "indexDefault: no corresponding index"
      (Just i, Just j) -> case findIndex (geq z) (take (j-i) (drop i l)) of
                            Nothing -> error "indexDefault: index out of range"
                            Just k  -> k

inRangeDefault :: (GEq a, Generic a, Enum' (Rep a))
               => (a,a) -> a -> Bool
inRangeDefault = t (map to enum') where
  t l (x,y) z =
    case (findIndex (geq x) l, findIndex (geq y) l) of
      (Nothing, _)     -> error "indexDefault: no corresponding index"
      (_, Nothing)     -> error "indexDefault: no corresponding index"
      (Just i, Just j) -> maybe False (const True)
                            (findIndex (geq z) (take (j-i) (drop i l)))

instance (GEq a, GEnum a, GIx a) => GIx [a] where
  range   = rangeDefault
  index   = indexDefault
  inRange = inRangeDefault

instance GIx Int where
  range   = rangeEnum
  index   = indexIntegral
  inRange = inRangeOrd

class GEnum a where
  genum :: [a]

instance GEnum Int where
  genum = genumNumSigned

instance GEnum a => GEnum (Maybe a) where
  genum = genumDefault

instance GEnum a => GEnum [a] where
  genum = genumDefault

genumNumSigned :: (Bounded a, Enum a, Num a) => [a]
genumNumSigned = [0 .. maxBound] ||| [-1, -2 .. minBound]

infixr 5 |||

(|||) :: [a] -> [a] -> [a]
[]     ||| ys = ys
(x:xs) ||| ys = x : ys ||| xs

diag :: [[a]] -> [a]
diag = concat . foldr skew [] . map (map (\x -> [x]))

skew :: [[a]] -> [[a]] -> [[a]]
skew []     ys = ys
skew (x:xs) ys = x : combine (++) xs ys

combine :: (a -> a -> a) -> [a] -> [a] -> [a]
combine _ xs     []     = xs
combine _ []     ys     = ys
combine f (x:xs) (y:ys) = f x y : combine f xs ys


findIndex :: (a -> Bool) -> [a] -> Maybe Int
findIndex p xs = let l = [ i | (y,i) <- zip xs [(0::Int)..], p y]
                 in if (null l)
                    then Nothing
                    else Just (head l)

rangeEnum :: Enum a => (a, a) -> [a]
rangeEnum (m,n) = [m..n]

indexIntegral :: Integral a => (a, a) -> a -> Int
indexIntegral (m,_n) i = fromIntegral (i - m)

inRangeOrd :: Ord a => (a, a) -> a -> Bool
inRangeOrd (m,n) i =  m <= i && i <= n

class Enum' f where
  enum' :: [f a]

instance Enum' U1 where
  enum' = [U1]

instance (GEnum c) => Enum' (K1 i c) where
  enum' = map K1 genum

instance (Enum' f) => Enum' (M1 i c f) where
  enum' = map M1 enum'

instance (Enum' f, Enum' g) => Enum' (f :+: g) where
  enum' = map L1 enum' ||| map R1 enum'

instance (Enum' f, Enum' g) => Enum' (f :*: g) where
  enum' = diag [ [ x :*: y | y <- enum' ] | x <- enum' ]

genumDefault :: (Generic a, Enum' (Rep a)) => [a]
genumDefault = map to enum'

class GFunctor f where
  gmap :: (a -> b) -> f a -> f b

class GFunctor' f where
  gmap' :: (a -> b) -> f a -> f b

instance GFunctor' U1 where
  gmap' _ U1 = U1

instance GFunctor' Par1 where
  gmap' f (Par1 a) = Par1 (f a)

instance GFunctor' (K1 i c) where
  gmap' _ (K1 a) = K1 a

instance (GFunctor f) => GFunctor' (Rec1 f) where
  gmap' f (Rec1 a) = Rec1 (gmap f a)

instance (GFunctor' f) => GFunctor' (M1 i c f) where
  gmap' f (M1 a) = M1 (gmap' f a)

instance (GFunctor' f, GFunctor' g) => GFunctor' (f :+: g) where
  gmap' f (L1 a) = L1 (gmap' f a)
  gmap' f (R1 a) = R1 (gmap' f a)

instance (GFunctor' f, GFunctor' g) => GFunctor' (f :*: g) where
  gmap' f (a :*: b) = gmap' f a :*: gmap' f b

instance (GFunctor f, GFunctor' g) => GFunctor' (f :.: g) where
  gmap' f (Comp1 x) = Comp1 (gmap (gmap' f) x)

gmapdefault :: (Generic1 f, GFunctor' (Rep1 f))
            => (a -> b) -> f a -> f b
gmapdefault f = to1 . gmap' f . from1

instance GFunctor [] where
  gmap = gmapdefault

class Uniplate a where
  children :: a -> [a]
  context :: a -> [a] -> a
  descend :: (a -> a) -> a -> a
  descendM :: Monad m => (a -> m a) -> a -> m a
  transform :: (a -> a) -> a -> a
  transformM :: Monad m => (a -> m a) -> a -> m a

class Uniplate' f b where
  children'  :: f a -> [b]
  descend'   :: (b -> b) -> f a -> f a
  descendM'  :: Monad m => (b -> m b) -> f a -> m (f a)
  transform' :: (b -> b) -> f a -> f a
  transformM'  :: Monad m => (b -> m b) -> f a -> m (f a)

instance Uniplate' U1 a where
  children' U1 = []
  descend' _ U1 = U1
  descendM' _ U1 = return U1
  transform' _ U1 = U1
  transformM' _ U1 = return U1

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPING #-}
#endif
    (Uniplate a) => Uniplate' (K1 i a) a where
  children' (K1 a) = [a]
  descend' f (K1 a) = K1 (f a)
  descendM' f (K1 a) = liftM K1 (f a)
  transform' f (K1 a) = K1 (transform f a)
  transformM' f (K1 a) = liftM K1 (transformM f a)

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPABLE #-}
#endif
    Uniplate' (K1 i a) b where
  children' (K1 _) = []
  descend' _ (K1 a) = K1 a
  descendM' _ (K1 a) = return (K1 a)
  transform' _ (K1 a) = K1 a
  transformM' _ (K1 a) = return (K1 a)

instance (Uniplate' f b) => Uniplate' (M1 i c f) b where
  children' (M1 a) = children' a
  descend' f (M1 a) = M1 (descend' f a)
  descendM' f (M1 a) = liftM M1 (descendM' f a)
  transform' f (M1 a) = M1 (transform' f a)
  transformM' f (M1 a) = liftM M1 (transformM' f a)

instance (Uniplate' f b, Uniplate' g b) => Uniplate' (f :+: g) b where
  children' (L1 a) = children' a
  children' (R1 a) = children' a
  descend' f (L1 a) = L1 (descend' f a)
  descend' f (R1 a) = R1 (descend' f a)
  descendM' f (L1 a) = liftM L1 (descendM' f a)
  descendM' f (R1 a) = liftM R1 (descendM' f a)
  transform' f (L1 a) = L1 (transform' f a)
  transform' f (R1 a) = R1 (transform' f a)
  transformM' f (L1 a) = liftM L1 (transformM' f a)
  transformM' f (R1 a) = liftM R1 (transformM' f a)

instance (Uniplate' f b, Uniplate' g b) => Uniplate' (f :*: g) b where
  children' (a :*: b) = children' a ++ children' b
  descend' f (a :*: b) = descend' f a :*: descend' f b
  descendM' f (a :*: b) = liftM2 (:*:) (descendM' f a) (descendM' f b)
  transform' f (a :*: b) = transform' f a :*: transform' f b
  transformM' f (a :*: b) = liftM2 (:*:) (transformM' f a) (transformM' f b)

childrendefault :: (Generic a, Uniplate' (Rep a) a) => a -> [a]
childrendefault = children' . from

contextdefault :: (Generic a, Context' (Rep a) a) => a -> [a] -> a
contextdefault x cs = to (context' (from x) cs)

descenddefault :: (Generic a, Uniplate' (Rep a) a) => (a -> a) -> a -> a
descenddefault f = to . descend' f . from

descendMdefault :: (Generic a, Uniplate' (Rep a) a, Monad m) => (a -> m a) -> a -> m a
descendMdefault f = liftM to . descendM' f . from

transformdefault :: (Generic a, Uniplate' (Rep a) a) => (a -> a) -> a -> a
transformdefault f = f . to . transform' f . from

transformMdefault :: (Generic a, Uniplate' (Rep a) a, Monad m) => (a -> m a) -> a -> m a
transformMdefault f = liftM to . transformM' f . from

instance Uniplate Char where
  children _ = []
  context x _ = x
  descend _ = id
  descendM _ = return
  transform = id
  transformM _ = return

instance Uniplate (Maybe a) where
  children _ = []
  context x _ = x
  descend _ = id
  descendM _ = return
  transform = id
  transformM _ = return

instance Uniplate [a] where
  children []    = []
  children (_:t) = [t]
  context _     []    = error "Generics.Deriving.Uniplate.context: empty list"
  context []    _     = []
  context (h:_) (t:_) = h:t
  descend _ []    = []
  descend f (h:t) = h:f t
  descendM _ []    = return []
  descendM f (h:t) = f t >>= \t' -> return (h:t')
  transform f []    = f []
  transform f (h:t) = f (h:transform f t)
  transformM f []    = f []
  transformM f (h:t) = transformM f t >>= \t' -> f (h:t')


class Context' f b where
  context' :: f a -> [b] -> f a

instance Context' U1 b where
  context' U1 _ = U1

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPING #-}
#endif
    Context' (K1 i a) a where
  context' _      []    = error "Generics.Deriving.Uniplate.context: empty list"
  context' (K1 _) (c:_) = K1 c

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPABLE #-}
#endif
    Context' (K1 i a) b where
  context' (K1 a) _ = K1 a

instance (Context' f b) => Context' (M1 i c f) b where
  context' (M1 a) cs = M1 (context' a cs)

instance (Context' f b, Context' g b) => Context' (f :+: g) b where
  context' (L1 a) cs = L1 (context' a cs)
  context' (R1 a) cs = R1 (context' a cs)

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPING #-}
#endif
    (Context' g a) => Context' (M1 i c (K1 j a) :*: g) a where
  context' _                 []     = error "Generics.Deriving.Uniplate.context: empty list"
  context' (M1 (K1 _) :*: b) (c:cs) = M1 (K1 c) :*: context' b cs

instance
#if __GLASGOW_HASKELL__ >= 709
    {-# OVERLAPPABLE #-}
#endif
    (Context' g b) => Context' (f :*: g) b where
  context' (a :*: b) cs = a :*: context' b cs

-------------------------------------------------------------------------------
-- Template Haskell bits
-------------------------------------------------------------------------------

$(deriveAll0     ''Tree)

$(deriveAll0And1 ''List)

$(deriveAll0And1 ''Rose)

$(deriveMeta           ''GRose)
$(deriveRepresentable0 ''GRose)
$(deriveRep1           ''GRose)
instance Functor f => Generic1 (GRose f) where
  type Rep1 (GRose f) = $(makeRep1 ''GRose) f
  from1 = $(makeFrom1 ''GRose)
  to1   = $(makeTo1 ''GRose)

$(deriveAll0And1 ''Either)

$(deriveAll0And1 ''Nested)

$(deriveAll0And1 ''Bush)

$(deriveAll0And1 ''Weird)

$(deriveAll0And1 ''Empty)
$(deriveAll0And1 ''(:/:))
$(deriveAll0And1 ''GADTSyntax)
$(deriveAll0     ''MyType2)
$(deriveAll0     ''ExampleSpec.Lexeme)
$(deriveAll0     ''Text.Read.Lex.Lexeme)

#if MIN_VERSION_template_haskell(2,7,0)
# if __GLASGOW_HASKELL__ < 705
-- We can't use deriveAll0And1 on GHC 7.4 due to an old bug :(
$(deriveMeta 'MyType3Newtype)
$(deriveRep0 'MyType3Newtype)
$(deriveRep1 'MyType3Newtype)
instance Generic (MyType3 (f p) (f p) f p q) where
    type Rep (MyType3 (f p) (f p) f p q) = $(makeRep0 'MyType3Newtype) f p q
    from = $(makeFrom0 'MyType3Newtype)
    to   = $(makeTo0 'MyType3Newtype)
instance Generic1 (MyType3 (f p) (f p) f p) where
    type Rep1 (MyType3 (f p) (f p) f p) = $(makeRep1 'MyType3Newtype) f p
    from1 = $(makeFrom1 'MyType3Newtype)
    to1   = $(makeTo1 'MyType3Newtype)
# else
$(deriveAll0And1 'MyType3Newtype)
# endif
$(deriveAll0And1 'MyType3False)
#endif
