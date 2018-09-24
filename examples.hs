{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Set
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Control.Monad.IO.Class
import Control.Concurrent.Async

{-@ type RegionT = {v:(Nat,Nat) | fst v <= snd v} @-}
type Region = (Int, Int)

{-@ type SubRegion P = {v:RegionT | snd v < plen P} @-}

{-@ measure interfere :: Region -> Region -> Bool @-}
interfere :: Region -> Region -> Bool
interfere (l, h) (l', h') = l >= l' && l <= h' || h >= l' && h <= h' || l <= l' && h >= h'

{-@ type OkPtr a = {v:Ptr a | 0 < plen v} @-}
{-@ type In r = {x:Nat | x >= fst r  && x <= snd r} @-}
{-@ measure ioRange :: IO a -> Ptr b -> Int -> Int -> Bool @-}
{-@ assume mallocArray :: Storable a => n:Nat -> IO (PtrN a n) @-}
{-@ assume withArray :: Storable a => x:[a] -> (PtrN a (len x) -> IO b) -> IO b @-}
{-@ assume newArray :: Storable a => x:[a] -> IO (PtrN a (len x)) @-}
{-@ assume peekElemOff :: Storable a => p:Ptr a -> x:{n:Nat | n < plen p} -> IO a @-}
{-@ assume pokeElemOff :: Storable a => p:Ptr a -> x:{n:Nat | n < plen p} -> a -> IO () @-}
{-@ assume advancePtr :: Storable a => o:Ptr a -> x:Nat -> {v : PtrN a m | plen v == plen o - x} @-}

{-@ measure safe :: Perm -> Perm -> Bool @-}
safe :: Perm -> Perm -> Bool
safe R R = True
safe _ _ = False

data Perm = R | W
newtype PIO p i a = MkPIO { getIO :: IO a } deriving Functor

instance Applicative PIO where
  MkPIO x <*> MkPIO y = MkPIO (x <*> y)
  pure = MkPIO . pure

instance Monad PIO where
  MkPIO x >>= y = MkPIO (x >>= getIO . y)
  return = MkPIO . return

instance MonadIO PIO where
   liftIO = MkPIO   

{-@ exampleNonInterfere :: {p : (RegionT, RegionT) | not (interfere (fst p) (snd p))} @-}
exampleNonInterfere :: (Region, Region)
exampleNonInterfere = ((3, 4), (5, 6))

{-@ withConstArray :: Storable a => a -> n:Nat -> (PtrN a n -> IO b) -> IO b @-}
withConstArray x n = withArray (replicate n x) 

{-@ regionPeekElemOff :: Storable a => p:Ptr a -> r:SubRegion p -> x:In r -> IO a @-}
regionPeekElemOff :: Storable a => Ptr a -> Region -> Int -> IO a
regionPeekElemOff p r x = peekElemOff p x

{-@ regionPokeElemOff :: Storable a => p:Ptr a -> r:SubRegion p -> x:In r -> a -> IO () @-}
regionPokeElemOff :: Storable a => Ptr a -> Region -> Int -> a -> IO ()
regionPokeElemOff p r x a = pokeElemOff p x a

{-@ safeConc :: p:Ptr a -> x:SubRegion p -> y:{y':SubRegion p | not (interfere x y')} ->
                   IO b -> IO c -> IO (b,c) @-}
safeConc :: Ptr a -> Region -> Region -> IO b -> IO c -> IO (b, c)
safeConc p r r' f g = concurrently f g

{-@ regionPeek :: Storable a => p:Ptr a -> r:SubRegion p -> IO [a] @-}
regionPeek :: Storable a => Ptr a -> Region -> IO [a]
regionPeek p (s,e) = if s < e then do
    v <- peekElemOff p s 
    vs <- regionPeek p (succ s, e) 
    return (v:vs)
  else if s == e then do
    v <- peekElemOff p s
    return [v]
  else 
    return []

main :: IO ()
main = do
  arr <- newArray "hello world" 
  c <- peekElemOff arr 3 
  let r1 = (0, 5)
  let r2 = (6, 10)  
  (one, two) <- safeConc arr r1 r2
                  (regionPeekElemOff arr r1 0) 
                  (regionPeekElemOff arr r2 7)
  print (one, two)

