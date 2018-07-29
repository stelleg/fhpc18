{-# LANGUAGE RankNTypes #-}
import Data.Set
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array

{-@ type Region = {v:(Nat,Nat) | fst v <= snd v} @-}
-- Subregion of ptr
{-@ type SubRegion p = {v:Region | snd v < plen p} @-}
{-@ measure interfere :: (Int, Int) -> (Int, Int) -> Bool @-}
interfere (l, h) (l', h') = l >= l' && l <= h' || h >= l' && h <= h'
{-@ type OkPtr a = {v:Ptr a | 0 < plen v} @-}
{-@ type In r = {x:Nat | x >= fst r  && x <= snd r} @-}
{-@ measure ioRange :: IO a -> Ptr b -> Int -> Int -> Bool @-}
{-@ assume mallocArray :: Storable a => n:Nat -> IO (PtrN a n) @-}
{-@ assume withArray :: Storable a => x:[a] -> (PtrN a (len x) -> IO b) -> IO b @-}
{-@ assume peekElemOff :: Storable a => p:Ptr a -> x:{n:Nat | n < plen p} -> {v:IO a | ioRange v p x x} @-}
{-@ assume pokeElemOff :: Storable a => p:Ptr a -> x:{n:Nat | n < plen p} -> a -> {v:IO () | ioRange v p x x} @-}
{-@ assume advancePtr :: Storable a => o:Ptr a -> x:Nat -> {v : PtrN a m | plen v == plen o - x} @-}

{-@ withConstArray :: Storable a => a -> n:Nat -> (PtrN a n -> IO b) -> IO b @-}
withConstArray x n = withArray (replicate n x) 

{-@ regionPeekElemOff :: Storable a => p:Ptr a -> r:SubRegion p -> x:In r -> {v:IO a | ioRange v p x x} @-}
regionPeekElemOff :: Storable a => Ptr a -> (Int, Int) -> Int -> IO a
regionPeekElemOff p r x = peekElemOff p x

{-@ forkRegions :: p:Ptr a -> v:SubRegion p -> v':{v:SubRegion p | not (interfere v v') @-} -> IO {
{-@ regionMalloc :: Storable a => r:SubRegion p -> x:In r -> RegionIO p r a @-}
regionMalloc = undefined 
