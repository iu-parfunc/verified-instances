#!/usr/bin/env stack
-- stack --resolver lts-6.20 --install-ghc runghc --package containers

-- | 

module Control.SimplePar
    ( new,put,get
    , IVar, Par
    , main, err, deadlock
    )
    where

import Control.Monad    
import Data.IntMap as M
import Data.List as L

    
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


-- | Hack: hardcode all IVar values to Double:
type Val = Double

-- newtype IVar a = IVar (IORef (IVarContents a))

-- | An IVar is an index into an IntMap
data IVar a = IVar Int

type Heap = M.IntMap (Maybe Val)

-- User-facing API:
--------------------------------------------------------------------------------          

new :: Par (IVar Val)
new  = Par New 

get :: IVar Val -> Par Val
get v = Par $ \c -> Get v c

put :: IVar Val -> Val -> Par ()
put v a = Par $ \c -> Put v a (c ())

--------------------------------------------------------------------------------          
             
newtype Par a = Par {
    -- A par computation takes a continuation and generates a trace
    -- incorporating it.
    runCont :: (a -> Trace) -> Trace
}

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

-- Take a stream of random numbers for scheduling decisions             
runPar :: [Word] -> Par Val -> Val
runPar randoms p = finalVal
 where
  Just finalVal = finalHeap M.! 0
  finalHeap = sched randoms initThreads M.empty 1 initHeap
  initThreads :: [Trace] 
  initThreads = [runCont p (\v -> Put (IVar 0) v Done)]
  initHeap = M.singleton 0 Nothing

  sched _ [] blkd _ heap =
    if M.null blkd
    then heap
    else error $ "no runnable threads, but "++show (sum (L.map length (M.elems blkd)))
               ++" thread(s) blocked on these IVars: "++ show (M.keys blkd)

  sched (rnd:rs) threads blkd cntr heap =
    let (thrds',blkd', cntr',heap') = step (yank rnd threads) blkd cntr heap
    in sched rs thrds' blkd' cntr' heap'

  sched [] _ _ _ _ = error "impossible: random supply cannot run out"

  step (trc,others) blkd cntr heap =
    case trc of
      Done       -> (      others, blkd,cntr,heap)
      Fork t1 t2 -> (t1:t2:others, blkd,cntr,heap)
      New  k     -> (k (IVar cntr) : others, blkd,
                     cntr+1, M.insert cntr Nothing heap)
      Get (IVar ix) k -> case heap M.! ix of
                           Nothing -> (others, M.insertWith (++) ix [k] blkd, cntr,heap)
                           Just v  -> (k v:others, blkd, cntr,heap)
      Put (IVar ix) v t2 ->
          let heap' = M.insert ix (Just v) heap in
          case heap M.! ix of
            Nothing ->
                case M.lookup ix blkd of
                  Nothing -> (t2:others, blkd, cntr, heap')
                  Just ls -> ( t2: [ k v | k <- ls] ++ others
                             , M.delete ix blkd, cntr, heap')
            Just v0 -> error $ "multiple put, attempt to put "++show v
                         ++" to IVar "++show ix++" already containing "++show v0

  yank n ls =
    let (hd,x:tl) = splitAt (fromIntegral n `mod` length ls) ls 
    in (x, hd++tl)
                            
main :: IO ()
main = do
  print $ runPar [0..] (return 3.99)

  print $ runPar [0..] (do v <- new; put v 3.12; get v)

-- | Example error
err :: IO ()
err = print $ runPar [0..] (do v <- new; put v 3.12; put v 4.5; get v)

-- | Example deadlock
deadlock :: IO ()
deadlock = print $ runPar [0..] (do v <- new; get v)
