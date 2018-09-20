{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

import Data.Set
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Control.Monad.IO.Class
import Control.Concurrent.Async

{-@ type Region = {v:(Nat,Nat) | fst v <= snd v} @-}
type Region = (Int, Int)

{-@ type SubRegion p = {v:Region | snd v < plen p} @-}
type SubRegion p = Region

{-@ measure interfere :: (Int,Int) -> (Int,Int) -> Bool @-}
interfere (l, h) (l', h') = l >= l' && l <= h' || h >= l' && h <= h'

{-@ type OkPtr a = {v:Ptr a | 0 < plen v} @-}
{-@ type In r = {x:Nat | x >= fst r  && x <= snd r} @-}
{-@ measure ioRange :: IO a -> Ptr b -> Int -> Int -> Bool @-}
{-@ assume mallocArray :: Storable a => n:Nat -> IO (PtrN a n) @-}
{-@ assume withArray :: Storable a => x:[a] -> (PtrN a (len x) -> IO b) -> IO b @-}
{-@ assume peekElemOff :: Storable a => p:Ptr a -> x:{n:Nat | n < plen p} -> IO a @-}
{-@ assume pokeElemOff :: Storable a => p:Ptr a -> x:{n:Nat | n < plen p} -> a -> IO () @-}
{-@ assume advancePtr :: Storable a => o:Ptr a -> x:Nat -> {v : PtrN a m | plen v == plen o - x} @-}

newtype PIO a = MkPIO { getIO :: IO a } deriving Functor

instance Applicative PIO where
  MkPIO x <*> MkPIO y = MkPIO (x <*> y)
  pure = MkPIO . pure

instance Monad PIO where
  MkPIO x >>= y = MkPIO (x >>= getIO . y)
  return = MkPIO . return

instance MonadIO PIO where
   liftIO = MkPIO   

{-@ withConstArray :: Storable a => a -> n:Nat -> (PtrN a n -> IO b) -> IO b @-}
withConstArray x n = withArray (replicate n x) 

{-@ regionPeekElemOff :: Storable a => p:Ptr a -> r:SubRegion p -> x:In r -> IO a @-}
regionPeekElemOff :: Storable a => Ptr a -> Region -> Int -> IO a
regionPeekElemOff p r x = peekElemOff p x

{-@ regionPokeElemOff :: Storable a => p:Ptr a -> r:SubRegion p -> x:In r -> a -> IO () @-}
regionPokeElemOff :: Storable a => Ptr a -> Region -> Int -> a -> IO ()
regionPokeElemOff p r x a = pokeElemOff p x a

{-@ safeConc :: p:Ptr a -> v:SubRegion p -> v':{v':SubRegion p | not (interfere v v')} ->
                   (Ptr a -> SubRegion p -> IO b) -> 
                   (Ptr a -> SubRegion p -> IO c) -> 
                   IO (b,c) @-}
safeConc :: Ptr a -> Region -> Region -> 
            (Ptr a -> Region -> IO b) ->
            (Ptr a -> Region -> IO c) -> 
            IO (b, c)
safeConc p r r' f g = concurrently (f p r) (g p r')

--{-@ regionMalloc :: Storable a => r:SubRegion p -> x:In r -> RegionIO p r a @-}
regionMalloc = undefined 

{-{-@ regionPeeks :: Storable a => p:Ptr a -> r:SubRegion p -> IO [a] @-}
regionPeeks :: Storable a => Ptr a -> Region -> IO [a]
regionPeeks p (s,e) = mapM (regionPeekElemOff p (s,e)) [s..e]
-}

{-@ regionPeekElemOff :: Storable a => p:Ptr a -> r:SubRegion p -> x:In r -> IO a @-}
f :: Ptr Char -> Region -> IO Char 
f p r = regionPeekElemOff p r 1

g :: Ptr Char -> Region -> IO Char
g p r = regionPeekElemOff p r 2

main :: IO ()
main = withArray "hello world" $ \arr -> do
  c <- peekElemOff arr 3 
  (one, two) <- safeConc arr (0, 1) (2, 3) f g
  print c
