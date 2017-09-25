{-@ LIQUID "--higherorder"        @-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
#!/usr/bin/env stack
-- stack --resolver lts-6.20 --install-ghc runghc --package containers

-- |

module Main
    (
    -- * Programmer API
    new,put,get, IVar, Par

    -- * Example programs
    , err, deadlock, loop, dag1
      
    -- * Run tests
    , main
    )
    where

import GHC.Generics
import Control.Monad
import Control.Monad.Except
import Data.IntMap as M hiding (fromList)
import Data.List as L
import Test.QuickCheck
-- import Test.QuickCheck.Modifiers
import Test.Tasty
import Test.Tasty.QuickCheck as QC

--------------------------------------------------------------------------------

-- Full version:
-- data Trace = forall a . Get (IVar a) (a -> Trace)
--            | forall a . Put (IVar a) a Trace
--            | forall a . New (IVarContents a) (IVar a -> Trace)
--            | Fork Trace Trace
--            | Done
--            | Yield Trace
--            | forall a . LiftIO (IO a) (a -> Trace)


-- | Restricted version:
data Trace = Get (IVar Val) (Val -> Trace)
           | Put (IVar Val) Val Trace
           | New (IVar Val -> Trace)
           | Fork Trace Trace
           | Done
  deriving (Generic, CoArbitrary)

instance Arbitrary Trace where
  arbitrary =
    oneof
      [ return Done
      , liftM2 Fork arbitrary arbitrary
      , liftM New arbitrary
      , liftM3 Put arbitrary arbitrary arbitrary -- (arbitrary `suchThat` (>= 0))
      , liftM2 Get arbitrary arbitrary
      ]

-- | Hack: hardcode all IVar values to Double:
type Val = Double

-- newtype IVar a = IVar (IORef (IVarContents a))

-- | An IVar is an index into an IntMap
data IVar a = IVar Int

instance Arbitrary (IVar a) where
  arbitrary = liftM IVar arbitrary -- (arbitrary `suchThat` (>= 0))

instance CoArbitrary (IVar a) where
  coarbitrary (IVar v) = coarbitrary v

type Heap = M.IntMap (Maybe Val)

-- User-facing API:
--------------------------------------------------------------------------------

new :: Par (IVar Val)
new  = Par New

get :: IVar Val -> Par Val
get v = Par $ \c -> Get v c

put :: IVar Val -> Val -> Par ()
put v a = Par $ \c -> Put v a (c ())

fork :: Par () -> Par ()
-- Child thread executes with no continuation:
fork (Par k1) = Par (\k2 -> Fork (k1 (\() -> Done)) (k2 ()))

--------------------------------------------------------------------------------

newtype Par a = Par {
    -- A par computation takes a continuation and generates a trace
    -- incorporating it.
    runCont :: (a -> Trace) -> Trace
}

instance Show (Par a) where
  show _ = "Par"

instance Arbitrary (Par Val) where
  arbitrary = liftM Par arbitrary

instance Functor Par where
    fmap f m = Par $ \c -> runCont m (c . f)

instance Applicative Par where
   (<*>) = ap
   -- Par ff <*> Par fa = Par (\bcont -> fa (\ a -> ff (\ ab -> bcont (ab a))))
   pure a = Par ($ a)

instance Monad Par where
    return = pure
    m >>= k  = Par $ \c -> runCont m $ \a -> runCont (k a) c


data InfList a = Cons a (InfList a)

instance Show a => Show (InfList a) where
  show xs = show (take 10 (toList' xs)) ++ "..."

instance Functor InfList where
  fmap f (Cons a as) = Cons (f a) (fmap f as)

fromList :: [a] -> InfList a
fromList (a:b) = Cons a (fromList b)
fromList [] = error "fromList: cannot convert finite list to infinite list!"

toList' :: InfList a -> [a]
toList' (Cons a as) = a : toList' as

instance Arbitrary a => Arbitrary (InfList a) where
  arbitrary = liftM fromList infiniteList

--------------------------------------------------------------------------------
-- The scheduler itself
--------------------------------------------------------------------------------

-- Goal: Prove that every schedule is equivalent to a canonical schedule:
-- Theorem: forall p l1 . runPar l1 p == runPar (repeat 0) p

-- | Exception thrown by runPar
data Exn = MultiplePut Val Int Val
         | Deadlock (M.IntMap [Val -> Trace])
         | HeapExn

instance Eq Exn where
  MultiplePut _ _ _ == MultiplePut _ _ _ = True
  Deadlock _ == Deadlock _ = True
  HeapExn == HeapExn = True
  _ == _ = False

instance Show Exn where
  show (MultiplePut v ix v0) =
    "multiple put, attempt to put " ++ show v ++ " to IVar " ++
    show ix ++ " already containing " ++ show v0
  show (Deadlock blkd) =
    "no runnable threads, but " ++ show (sum (L.map length (M.elems blkd))) ++
    " thread(s) blocked on these IVars: " ++ show (M.keys blkd)
  show HeapExn =
    "heap location 0 was empty"

-- we can syntactically describe parallel evaluation contexts if we like:
--   fork (a1 >>= k1) (a2 >>= k2)

-- lemma: the heap is used linearly and grows monotonically towards deterministic final state

-- noninteference lemma:  i /= j  =>  get (IVar i) # put (IVar j) v


-- | Run a Par computation.  Take a stream of random numbers for scheduling decisions.
runPar :: InfList Word -> Par Val -> Except Exn Val
runPar randoms p0 = do
  let initHeap = M.singleton 0 Nothing
      initThreads :: [Trace]
      initThreads = [runCont p0 (\v -> Put (IVar 0) v Done)]

  finalHeap <- sched randoms initThreads M.empty 1 initHeap
  let maybeFinalVal = finalHeap M.! 0
  case maybeFinalVal of
    Nothing       -> throwError HeapExn
    Just finalVal -> return finalVal

  where
    sched :: InfList Word -> [Trace] -> M.IntMap [Val -> Trace] -> Int -> Heap -> Except Exn Heap
    sched _ [] blkd _ heap = do
      if M.null blkd
        then return heap
        else throwError $ Deadlock blkd

    sched (Cons rnd rs) threads blkd cntr heap = do
      (thrds', blkd', cntr', heap') <- step (yank rnd threads) blkd cntr heap
      sched rs thrds' blkd' cntr' heap'
            
    -- Potential Step lemmas:
    -- (1) Monotonicity lemma:
    --     step a b c heap = (_,_,_,heap2)  =>  (heap <= heap2)

    -- (2) Independence: other stuff in the heap doesn't change our outcome.
    --     If    step p b c h = (p2,b2,c2,h2)
    --     then  ...

    -- (3) Local confluence
    --   If   step (a1,[a2..ai..an]) b c h => sigma1
    --   and  step (ai,[a2..a1..an]) b c h => sigma2
    --   then there exists sigma3, such that ...
    -- 
    step :: (Trace, [Trace]) -> IntMap [Val -> Trace] -> Int -> IntMap (Maybe Val)
         -> Except Exn ([Trace], IntMap [Val -> Trace], Int, IntMap (Maybe Val))
    step (trc, others) blkd cntr heap =
      case trc of
        Done -> return (others, blkd, cntr, heap)
        Fork t1 t2 -> return (t1 : t2 : others, blkd, cntr, heap)
        New k -> return (k (IVar cntr) : others, blkd, cntr + 1, M.insert cntr Nothing heap)
        Get (IVar ix) k ->
          case join (M.lookup ix heap) of
            Nothing -> return (others, M.insertWith (++) ix [k] blkd, cntr, heap)
            Just v  -> return (k v : others, blkd, cntr, heap)
        Put (IVar ix) v t2 ->
          let heap' = M.insert ix (Just v) heap
          in case join (M.lookup ix heap) of
            Nothing ->
              case M.lookup ix blkd of
                Nothing -> return (t2 : others, blkd, cntr, heap')
                Just ls -> return (t2 : [ k v | k <- ls ] ++ others
                                 , M.delete ix blkd, cntr, heap')
            Just v0 -> throwError $ MultiplePut v ix v0

    yank n ls =
      let (hd, x:tl) = splitAt (fromIntegral n `mod` length ls) ls
      in (x, hd ++ tl)

runPar' :: InfList Word -> Par Val -> Either Exn Val
runPar' randoms p = runExcept (runPar randoms p)

--------------------------------------------------------------------------------
-- [2017.01.23] Some meeting notes.

-- Ranjit's suggestion of a simpler starting point a la http://www.cs.nott.ac.uk/~pszgmh/ccc.pdf
--  Can we start with programs but no scheduler?
                    
-- Ranjit suggests a baby version:
----------------------------------
{- One global Ivar, multiple threads.

 What's an example of something very simple we can prove with *no schedule*?
 Consider, for all programs p:

    do put 12; p
 
 The final state will satisfy either:
 
  (1) final heap state is (Just 12)
  (2) multiple Put exception.


-}

--------------------------------------------------------------------------------

roundRobin :: InfList Word
roundRobin = fromList [0..]

canonical :: InfList Word
canonical = fromList (repeat 0)

main :: IO ()
main = defaultMain tests
  -- print $ runPar' roundRobin (return 3.99)
  -- print $ runPar' roundRobin (do v <- new; put v 3.12; get v)


tests :: TestTree
tests = testGroup "Tests"
          [
-- TODO: need to fix Arbitrary instance for Par for this to work:
           -- QC.testProperty "forall p l1 . runPar l1 p == runPar (repeat 0) p" $
           --  \p (l1 :: InfList (NonNegative Word)) ->
           --    runPar' (getNonNegative <$> l1) p == runPar' canonical p

           QC.testProperty "determinism of dag1" $
            \(l1 :: InfList (NonNegative Word)) ->
              runPar' (getNonNegative <$> l1) dag1 == runPar' canonical dag1

          ]


-- Example invalid programs:
--------------------------------------------------------------------------------
          
-- | Example error
err :: IO ()
err = print $ runPar roundRobin (do v <- new; put v 3.12; put v 4.5; get v)

-- | Example deadlock
deadlock :: IO ()
deadlock = print $ runPar roundRobin (do v <- new; get v)

-- | runPar can be nonterminating of course.
loop :: IO ()
loop = print $ runPar roundRobin (do v <- new; put v 4.1; loopit 0.0 v)

loopit :: Val -> IVar Val -> Par b
loopit !acc vr = do n <- get vr; loopit (acc+n) vr


-- A test suite of valid programs:
--------------------------------------------------------------------------------

-- | A program that cannot execute sequentially.
dag1 :: Par Val
dag1 = do a <- new
          b <- new
          fork $ do x <- get a
 --                 put b 3 -- Control dependence without information flow.
                    put b x -- Control dependence PLUS information flow.
          put a 100
          get b

-- [2016.12.15] Notes from call:
-- Possibly related:
-- "Core calculus of dependency": https://people.mpi-sws.org/~dg/teaching/lis2014/modules/ifc-3-abadi99.pdf
-- Also check out "Partial order reduction" in model checking.
