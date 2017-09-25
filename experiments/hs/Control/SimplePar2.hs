{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE Rank2Types          #-}

-- | This alternate version.............

module Control.SimplePar2 where

import Control.Monad.Except

import GHC.Generics
-- import Data.Word
import Data.List as L
-- import Data.IntMap as M hiding (fromList)
import Data.Map as M hiding (fromList)
-- import Data.Set as S
import Data.Dynamic
import Test.QuickCheck

-- Preliminaries:

-- Ivars, Values, and Heaps
------------------------------------------------------------    

-- | Only use a simple notion of values for now.
type Val = Double

-- | An IVar is an index into an Map
data IVar a = IVar IVarID
type IVarID = Pedigree
    -- ^ Using Pedigree to identify IVars gives an
    -- schedule-independent identifier for the IVar.

instance Arbitrary (IVar a) where
  arbitrary = liftM IVar arbitrary -- (arbitrary `suchThat` (>= 0))

instance CoArbitrary (IVar a) where
  coarbitrary (IVar v) = coarbitrary v

type ThreadID = () -- Could use pedigree here...

dummyTID :: ThreadID
dummyTID = ()

type Heap = M.Map IVarID (Maybe Val)

-- Exceptions
------------------------------------------------------------           

-- | Exception thrown by runPar
data Exn = MultiplePut Val Int Val
         | Deadlock (M.Map IVarID [Val -> Trace Dynamic])
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

-- Pedigrees:
------------------------------------------------------------

-- TODO: replace with efficient encoding.. bitlist or Integer:
data PedStep = Parent | Child
  deriving (Eq, Ord, Show, Read, Generic, CoArbitrary)

instance Arbitrary PedStep where
  arbitrary = oneof [return Parent, return Child]

type PedPath = [PedStep] -- root is empty list.  Each forkIO
                         -- introduces an intermediate node in the
                         -- tree and makes paths deeper.

-- Counters reset when we go to a new segment (edge) in the tree:
consParent :: Pedigree -> Pedigree
consParent (Pedigree _c ls) = Pedigree 0 (Parent : ls)

consChild :: Pedigree -> Pedigree
consChild (Pedigree _c ls)  = Pedigree 0 (Child : ls)

rootPedigree :: Pedigree
rootPedigree = Pedigree 0 []

-- | Increment to count operations along ONE thread.
incr :: Pedigree -> Pedigree
incr (Pedigree n ti) = Pedigree (n+1) ti

-- | Location in the fork tree, IGNORING IVar synchronization
-- operations.
data Pedigree = Pedigree { cntr    :: Word -- ^ count events along one thread.
                         , treeInd :: PedPath
                         }
  deriving (Eq,Show, Generic, CoArbitrary)

-- | The order in the fork tree IF no IVar synchronizations existed.
--   LESS means "before" in this ordering.
--   This corresponds to the order in a hypothetical sequential
--   execution of the program should be used only for symmetry breaking.
instance Ord Pedigree where
  Pedigree c1 l1 <= Pedigree c2 l2 =
      if   l1 == l2
      then c1 <= c2
      else go (L.reverse l1) (L.reverse l2)
    where
     go [] [] = True
     go [] _  = True -- The computation BEFORE the fork happens before
                     -- either the left or right branch of the fork.
     go _  [] = False
     go (Child:_) (Parent:_) = True -- Child before parent in this ordering.
     go (Parent:_) (Child:_) = False
     go (_:a) (_:b)          = go a b -- Match, keep going.

instance Arbitrary Pedigree where
  arbitrary = liftM2 Pedigree arbitrary arbitrary 
  
-- User-facing API:
--------------------------------------------------------------------------------

new :: Par (IVar Val)
new  = Par New

get :: IVar Val -> Par Val
get v = Par $ \c -> Get v c

put :: IVar Val -> Val -> Par ()
put v a = Par $ \c -> Put v a (c ())

fork :: Par () -> Par ()
-- -- Child thread executes with no continuation:
fork (Par k1) = Par (\k2 -> Fork (k1 (\() -> ThreadDone ())) (k2 ()))

--------------------------------------------------------------------------------

newtype Par a = Par {
    -- A par computation takes a continuation and generates a trace
    -- incorporating it.
    runCont :: forall b . (a -> Trace b) -> Trace b
}

instance Show (Par a) where
  show _ = "Par"

instance Arbitrary (Par Val) where
--  arbitrary = liftM Par arbitrary

instance Functor Par where
    fmap f m = Par $ \c -> runCont m (c . f)

instance Applicative Par where
   (<*>) = ap
   -- Par ff <*> Par fa = Par (\bcont -> fa (\ a -> ff (\ ab -> bcont (ab a))))
   pure a = Par ($ a)

instance Monad Par where
    return = pure
    m >>= k  = Par $ \c -> runCont m $ \a -> runCont (k a) c

  

--------------------------------------------------------------------------------          
-- Problem (1): Returning a value from the main thread:
-------------------------------------------------------
data Trace fin = Get (IVar Val) (Val -> Trace fin)
               | Put (IVar Val) Val (Trace fin)
               | New (IVar Val -> Trace fin)
               | Fork (Trace ()) (Trace fin)
               | ThreadDone fin
  deriving (Generic, CoArbitrary)

instance Arbitrary a => Arbitrary (Trace a) where
  arbitrary =
    oneof
      [ liftM ThreadDone arbitrary
      , liftM2 Fork arbitrary arbitrary
      , liftM New arbitrary
      , liftM3 Put arbitrary arbitrary arbitrary -- (arbitrary `suchThat` (>= 0))
      , liftM2 Get arbitrary arbitrary
      ]


-- Problem (2): pattern matching on the schedule
-------------------------------------------------------         

-- How do we represent the choice of a random schedule from the space
-- of possible schedules?

-- Related question: How do we /enumerate/ the valid schedules?


-- First, a DAG captures the dataflow in a parallel computation.  A
--   Par computation creates a /unique/ DAG.

-- | A forward DAG.  This represents only synchronization structure
-- and not the flow of values.
data DAG = EndD 
         | GetD IVarID DAG
         | PutD IVarID DAG
         | ForkD  DAG  DAG


-- -- | This DAG is stored in reverse, starting from the final result,
-- --   using sharing in the data structure.
-- data DAGRev = Start
--          | EndDR { final :: Val,                prev :: DAGRev }
--          | GetDR { syncEdge :: (IVarID,DAGRev), prev :: DAGRev }
--                -- ^ A sync point that joins another thread into ours.
--                -- 'prev' represents the
--          | PutDR { input :: (IVarID, Val),      prev :: DAGRev }
           
-- | While a program induces a unique DAG, it can produce a set of
-- multiple logs (internal nondeterminism).
data LogAction = PutL ThreadID IVarID
               | GotL ThreadID IVarID

type Log = [LogAction]

emptyLog :: Log
emptyLog = []
           
-- | Enumerate all the schedules for a communication graph.
enumerate :: DAG -> [Log]
enumerate dag =
 case dag of
   EndD -> [emptyLog]
   ForkD d1 d2 -> concat
                  [ interleave x y
                  | x <- enumerate d1
                  , y <- enumerate d2 ]
   GetD iid d -> [ GotL dummyTID iid : l | l <- enumerate d ]
   PutD iid d -> [ PutL dummyTID iid : l | l <- enumerate d ]

-- | All interleavings
interleave :: [a] -> [a] -> [[a]]
interleave [] [] = [[]]
interleave xs@(_:_) [] = [xs]
interleave [] ys@(_:_) = [ys]
interleave (x:xs) (y:ys) = L.map (x:) (interleave xs (y:ys)) ++
                           L.map (y:) (interleave (x:xs) ys)
           

-- runPar1 :: Par a -> (DAG, Log -> Except Exn Val)

runPar2 :: forall a . Par a -> Log -> (DAG, Except Exn a)
runPar2 (Par runCont) log =
 
   undefined

 where
   trc0 :: Trace a
   trc0 = runCont ThreadDone
             

-- Chew off the matching part of the schedule, return the rest.

sched :: Pedigree -> Heap -> Trace a -> Log -> Except Exn a
sched ped hp t@(Get (IVar id1) k) (lh:lr) | headMatch t lh = 
  -- The schedule indicates that a get should occur, so the value
  -- should already be there.
  case hp M.! id1 of
    Nothing -> undefined  
    Just val -> sched ped hp (k val) lr

sched ped hp t@(Put (IVar id1) val trc) (lh:lr) | headMatch t lh =
  case M.lookup id1 hp of
    Nothing -> sched ped (M.insert id1 (Just val) hp) trc lr
    Just _val -> undefined

sched ped hp (Fork t1 t2) (lh:lr)
    | headMatch t1 lh = undefined -- do sched (consChild ped) t1 lr
    | headMatch t2 lh = undefined
    | otherwise = undefined

sched _ _ (New k) _ = undefined
sched _ _ (ThreadDone _) _ = undefined


headMatch :: Trace t -> LogAction -> Bool
headMatch (Get (IVar id1) _)   (GotL () id2) = id1 == id2
headMatch (Put (IVar id1) _ _) (PutL () id2) = id1 == id2
headMatch _ _                                = False
             
------------------------------------------------------------


-- Lemma: same IVarID is written the same value in every log.
-- 
